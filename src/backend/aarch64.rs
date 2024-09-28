use std::io::Write;
use std::rc::Rc;

use super::common::{self, Result, CodegenError};
use crate::analyzer::sst;

struct TempVar {
    typ: Rc<sst::Type>,
    stack_base: usize,
    frame_offset: usize,
}

struct Frame<W: Write> {
    w: W,
    retvar: Rc<sst::LocalVar>,
    stack_size: usize,
    temps: Vec<TempVar>,
}

impl<W: Write> Frame<W> {
    fn new(w: W, func: &sst::Function) -> Self {
        Self {
            w,
            retvar: func.retvar.clone(),
            stack_size: func.stack_size,
            temps: Vec::new(),
        }
    }

    fn push_temp(&mut self, typ: Rc<sst::Type>) -> sst::LocalVar {
        let stack_base = self.stack_size;
        while typ.align > 0 && self.stack_size % typ.align != 0 {
            self.stack_size += 1;
        }

        let frame_offset = self.stack_size;
        self.stack_size += typ.size;

        self.temps.push(TempVar{
            typ: typ.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar{
            typ,
            frame_offset: frame_offset as isize,
        }
    }

    fn pop_temp(&mut self, var: sst::LocalVar) {
        // We want to ensure that the passed-in variable is the most recent
        // variable returned from push_temp().
        // We don't keep around a reference to the actual LocalVar
        // that was returned by push_temp,
        // so we do a series of sanity checks instead.
        // If they are violated, that's a serious programming error,
        // so we just panic.

        let Some(last) = self.temps.pop() else {
            panic!("pop_temp called with an empty temporary stack!");
        };

        if !Rc::ptr_eq(&last.typ, &var.typ) {
            panic!(
                "pop_temp called with wrong type: expected {}, got {}",
                last.typ.name, var.typ.name);
        }

        if last.frame_offset as isize != var.frame_offset {
            panic!(
                "pop_temp called with wrong frame_offset: expected {}, got {}",
                last.frame_offset, var.frame_offset);
        }

        self.stack_size = last.stack_base;
    }

    fn done(self) -> W {
        self.w
    }
}

fn frame_pointer_offset(var: &sst::LocalVar) -> isize {
    -(var.frame_offset + var.typ.size as isize)
}

fn gen_copy<W: Write>(
    frame: &mut Frame<W>,
    dest: &sst::LocalVar,
    src: &sst::LocalVar,
) -> Result<()> {
    let size = dest.typ.size;
    if size != src.typ.size {
        return Err(CodegenError::SizeMismatch(dest.typ.size, src.typ.size));
    }

    let doffset = frame_pointer_offset(dest);
    let soffset = frame_pointer_offset(src);
    if doffset == soffset {
        return Ok(());
    }

    if size == 1 {
        write!(&mut frame.w, "\tldrb w1, [fp, {}]", soffset)?;
        write!(&mut frame.w, "\tstrb w1, [fp, {}]", doffset)?;
    } else if size == 2 {
        write!(&mut frame.w, "\tldrh w1, [fp, {}]", soffset)?;
        write!(&mut frame.w, "\tstrh w1, [fp, {}]", doffset)?;
    } else if size == 4 {
        write!(&mut frame.w, "\tldr w1, [fp, {}]", soffset)?;
        write!(&mut frame.w, "\tstr w1, [fp, {}]", doffset)?;
    } else if size == 8 {
        write!(&mut frame.w, "\tldr x1, [fp, {}]", soffset)?;
        write!(&mut frame.w, "\tstr x1, [fp, {}]", doffset)?;
    } else {
        panic!("Unsupported copy size: {}", size);
    }

    Ok(())
}

fn gen_expr_to<W: Write>(
    frame: &mut Frame<W>,
    expr: &sst::Expression,
    loc: &sst::LocalVar,
) -> Result<()> {
    write!(
        &mut frame.w, "\t// <Expression kind:{:?} size:{} to:{}>\n",
        expr.kind, expr.typ.size, loc.frame_offset)?;

    match &expr.kind {
        sst::ExprKind::FuncCall(_signature, _params) => {
            write!(&mut frame.w, "\t// TODO\n")?;
        }

        sst::ExprKind::Assignment(var, expr) => {
            gen_expr_to(frame, expr, var)?;
        }

        sst::ExprKind::Uninitialized => {
            // Nothing to do here
        }

        sst::ExprKind::Variable(var) => {
            gen_copy(frame, loc, var)?;
        }
    }

    write!(&mut frame.w, "\t// </Expression>\n")?;

    Ok(())
}

fn gen_extern_func<W: Write>(
    w: &mut W,
    func: &sst::FuncSignature,
) -> Result<()> {
    common::gen_signature_comment(w, func)?;
    write!(w, ".extern {}\n\n", func.name)?;
    Ok(())
}

fn gen_return<W: Write>(frame: &mut Frame<W>) -> Result<()> {
    // To return, restore the stack pointer,
    // pop the return address into bl, and ret
    write!(frame.w, "\t// <Return>\n")?;
    write!(frame.w, "\tadd sp, fp, 16\n")?;
    write!(frame.w, "\tldr lr, [sp, -8]\n")?;
    write!(frame.w, "\tret\n")?;
    write!(frame.w, "\t// </Return>\n")?;
    Ok(())
}

fn gen_stmt<W: Write>(frame: &mut Frame<W>, stmt: &sst::Statement) -> Result<()> {
    match stmt {
        sst::Statement::Expression(expr) => {
            let local = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &local)?;
            frame.pop_temp(local);
        }

        sst::Statement::VarDecl(var, expr) => {
            gen_expr_to(frame, expr, &var)?;
        }

        sst::Statement::Return(expr) => {
            if let Some(expr) = expr {
                let retvar = frame.retvar.clone();
                gen_expr_to(frame, expr, &retvar)?;
            }
            gen_return(frame)?;
        }
    }

    Ok(())
}

fn gen_func<W: Write>(frame: &mut Frame<W>, func: &sst::Function) -> Result<()> {
    common::gen_signature_comment(&mut frame.w, &func.signature)?;
    write!(frame.w, ".global awe__{}\n", func.signature.name)?;
    write!(frame.w, "awe__{}:\n", func.signature.name)?;

    // We expect to have been called using the 'bl' instruction,
    // which puts the return pointer in the link register.
    // Therefore, we have to write the link register to the stack,
    // in order to conform to the expected stack layout.
    // We also need to put the stack pointer in the frame pointer.
    // Then, we allocate stack space for all the local variables.
    write!(frame.w, "\t// <Preamble>\n")?;
    write!(frame.w, "\tstr lr, [sp]\n")?;
    write!(frame.w, "\tsub sp, sp, 8\n")?;
    write!(frame.w, "\tmov fp, sp\n")?;
    write!(frame.w, "\t// </Preamble>\n")?;

    for stmt in &func.body {
        write!(frame.w, "\t// <Statement>\n")?;
        gen_stmt(frame, stmt)?;
        write!(frame.w, "\t// </Statement>\n")?;
    }

    // Always return at the end of a function,
    // unless the function always returns itself
    if !func.always_returns {
        gen_return(frame)?;
    }

    write!(frame.w, "\n")?;
    Ok(())
}

pub fn codegen<W: Write>(mut w: W, prog: &sst::Program) -> Result<()> {
    for func in &prog.extern_funcs {
        gen_extern_func(&mut w, func)?;
    }

    for func in &prog.functions {
        let mut frame = Frame::new(w, &func);
        gen_func(&mut frame, func)?;
        w = frame.done();
    }

    write!(w, ".global _main\n")?;
    write!(w, "_main:\n")?;
    write!(w, "\tbl awe__main\n")?;
    write!(w, "\tmov x0, 0\n")?; // Exit code
    write!(w, "\tmov x16, 1\n")?; // Terminate svc
    write!(w, "\tsvc 0\n")?;

    Ok(())
}
