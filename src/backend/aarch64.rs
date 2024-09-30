use std::io::Write;
use std::rc::Rc;

use super::common::{self, Result, CodegenError};
use crate::analyzer::sst;

/*
 * Registers:
 * lr (x30): Link register
 * sp: Stack pointer
 * x0-x3, w0-w3: Scratch register
 *
 * The stack pointer will always point to the byte before the return value.
 * On function call, the stack pointer should be decremented as necessary
 * right before the bl instruction,
 * then promptly incremented back to where it was after the call.
 */

struct TempVar {
    typ: Rc<sst::Type>,
    stack_base: usize,
    frame_offset: usize,
}

struct Frame<'a, W: Write> {
    w: W,
    func: &'a sst::Function,
    stack_size: usize,
    temps: Vec<TempVar>,
    sentinel: Rc<sst::Type>,
}

impl<'a, W: Write> Frame<'a, W> {
    fn new(w: W, func: &'a sst::Function, sentinel: Rc<sst::Type>) -> Self {
        let stack_size = func.stack_size;
        Self {
            w,
            func,
            stack_size,
            temps: Vec::new(),
            sentinel,
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

    fn push_align(&mut self, align: usize) -> sst::LocalVar {
        let stack_base = self.stack_size;
        while align > 0 && self.stack_size % align != 0 {
            self.stack_size += 1;
        }

        let frame_offset = self.stack_size;

        self.temps.push(TempVar{
            typ: self.sentinel.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar{
            typ: self.sentinel.clone(),
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

fn frame_offset(var: &sst::LocalVar) -> isize {
    -(var.frame_offset + var.typ.size as isize)
}

fn gen_integer<W: Write>(
    frame: &mut Frame<W>,
    dest: &sst::LocalVar,
    num: i128,
) -> Result<()> {
    let size = dest.typ.size;
    let doffset = frame_offset(dest);

    if size == 1 {
        write!(&mut frame.w, "\tmov w0, {}\n", num)?;
        write!(&mut frame.w, "\tstrb w0, [sp, {}]\n", doffset)?;
    } else if size == 2 {
        write!(&mut frame.w, "\tmov w0, {}\n", num)?;
        write!(&mut frame.w, "\tstrh w0, [sp, {}]\n", doffset)?;
    } else if size == 4 {
        write!(&mut frame.w, "\tmov w0, {}\n", num)?;
        write!(&mut frame.w, "\tstr w0, [sp, {}]\n", doffset)?;
    } else if size == 8 {
        write!(&mut frame.w, "\tmov x0, {}\n", num)?;
        write!(&mut frame.w, "\tstr x0, [sp, {}]\n", doffset)?;
    } else {
        panic!("Unsupported copy size: {}", size);
    }

    Ok(())
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

    let doffset = frame_offset(dest);
    let soffset = frame_offset(src);
    if doffset == soffset {
        return Ok(());
    }

    if size == 1 {
        write!(&mut frame.w, "\tldrb w0, [sp, {}]\n", soffset)?;
        write!(&mut frame.w, "\tstrb w0, [sp, {}]\n", doffset)?;
    } else if size == 2 {
        write!(&mut frame.w, "\tldrh w0, [sp, {}]\n", soffset)?;
        write!(&mut frame.w, "\tstrh w0, [sp, {}]\n", doffset)?;
    } else if size == 4 {
        write!(&mut frame.w, "\tldr w0, [sp, {}]\n", soffset)?;
        write!(&mut frame.w, "\tstr w0, [sp, {}]\n", doffset)?;
    } else if size == 8 {
        write!(&mut frame.w, "\tldr x0, [sp, {}]\n", soffset)?;
        write!(&mut frame.w, "\tstr x0, [sp, {}]\n", doffset)?;
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
    match &expr.kind {
        sst::ExprKind::Literal(literal) => {
            write!(&mut frame.w, "\t// <Expression::Literal {:?}>\n", literal)?;
            match literal {
                sst::Literal::Integer(num) => {
                    gen_integer(frame, loc, *num)?;
                }

                sst::Literal::String(sc) => {
                    write!(&mut frame.w, "\tadr x0, awestr__{}\n", sc.index)?;
                    write!(&mut frame.w, "\tstr x0, [sp, {}]\n", frame_offset(loc))?;
                }
            }
            write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
        }

        sst::ExprKind::FuncCall(signature, params) => {
            write!(&mut frame.w, "\t// <Expression::FuncCall {}>\n", signature.name)?;
            let aligned = frame.push_align(16);

            let return_var = frame.push_temp(signature.ret.clone());

            let mut param_vars = Vec::<sst::LocalVar>::new();
            param_vars.reserve(params.len());
            for param in params {
                let var = frame.push_temp(param.typ.clone());
                gen_expr_to(frame, param, &var)?;
                param_vars.push(var);
            }

            write!(&mut frame.w, "\tsub sp, sp, {}\n", aligned.frame_offset)?;
            write!(&mut frame.w, "\tbl awe__{}\n", signature.name)?;
            write!(&mut frame.w, "\tadd sp, sp, {}\n", aligned.frame_offset)?;

            while let Some(var) = param_vars.pop() {
                frame.pop_temp(var);
            }

            gen_copy(frame, loc, &return_var)?;

            frame.pop_temp(return_var);
            frame.pop_temp(aligned);
            write!(&mut frame.w, "\t// </Expression::FuncCall>\n")?;
        }

        sst::ExprKind::Assignment(var, expr) => {
            write!(&mut frame.w, "\t// <Expression::Assignment {:?}>\n", var)?;
            gen_expr_to(frame, expr, var)?;
            write!(&mut frame.w, "\t// </Expression::Assignment>\n")?;
        }

        sst::ExprKind::Uninitialized => {
            write!(&mut frame.w, "\t// <Expression::Uninitialized />\n")?;
        }

        sst::ExprKind::Variable(var) => {
            write!(&mut frame.w, "\t// <Expression::Variable loc:{}>\n", var.frame_offset)?;
            gen_copy(frame, loc, var)?;
            write!(&mut frame.w, "\t// </Expression::Variable>\n")?;
        }
    }

    Ok(())
}

fn gen_return<W: Write>(frame: &mut Frame<W>) -> Result<()> {
    // Read the return address into bl if necessary, and ret
    if !frame.func.is_leaf {
        write!(frame.w, "\tldr lr, [sp, {}]\n", frame_offset(&frame.func.return_addr))?;
    }
    write!(frame.w, "\tret\n")?;
    Ok(())
}

fn gen_stmt<W: Write>(frame: &mut Frame<W>, stmt: &sst::Statement) -> Result<()> {
    match stmt {
        sst::Statement::Return(expr) => {
            write!(&mut frame.w, "\t// <Statement::Return>\n")?;
            if let Some(expr) = expr {
                let retvar = frame.func.return_var.clone();
                gen_expr_to(frame, expr, &retvar)?;
            }
            gen_return(frame)?;
            write!(&mut frame.w, "\t// </Statement::Return>\n")?;
        }

        sst::Statement::VarDecl(var, expr) => {
            write!(&mut frame.w, "\t// <Statement::VarDecl>\n")?;
            gen_expr_to(frame, expr, &var)?;
            write!(&mut frame.w, "\t// </Statement::VarDecl>\n")?;
        }

        sst::Statement::Expression(expr) => {
            write!(&mut frame.w, "\t// <Statement::Expression>\n")?;
            let local = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &local)?;
            frame.pop_temp(local);
            write!(&mut frame.w, "\t// </Statement::Expression>\n")?;
        }
    }

    Ok(())
}

fn gen_func<W: Write>(frame: &mut Frame<W>) -> Result<()> {
    common::gen_signature_comment(&mut frame.w, &frame.func.signature)?;
    write!(frame.w, ".global awe__{}\n", frame.func.signature.name)?;
    write!(frame.w, ".balign 4\n")?;
    write!(frame.w, "awe__{}:\n", frame.func.signature.name)?;

    // We expect to have been called using the 'bl' instruction,
    // which puts the return pointer in the link register.
    // Therefore, we have to write the link register to the stack,
    // in order to conform to the expected stack layout.
    // We also need to put the stack pointer in the frame pointer.
    // Then, we allocate stack space for all the local variables.
    if !frame.func.is_leaf {
        write!(frame.w, "\tstr lr, [sp, {}]\n", frame_offset(&frame.func.return_addr))?;
    }

    for stmt in &frame.func.body {
        gen_stmt(frame, stmt)?;
    }

    // Always return at the end of a function,
    // unless the function always returns itself
    if !frame.func.always_returns {
        gen_return(frame)?;
    }

    write!(frame.w, "\n")?;
    Ok(())
}

pub fn codegen<W: Write>(mut w: W, prog: &sst::Program) -> Result<()> {
    let sentinel = Rc::new(sst::Type{
        name: Rc::new("<sentinel>".to_owned()),
        size: 0,
        align: 0,
        kind: sst::TypeKind::Primitive(sst::Primitive::Void),
    });

    for func in &prog.functions {
        let mut frame = Frame::new(w, &func, sentinel.clone());
        gen_func(&mut frame)?;
        w = frame.done();
    }

    write!(w, ".global _main\n")?;
    write!(w, ".balign 4\n")?;
    write!(w, "_main:\n")?;
    write!(w, "\tbl awe__main\n")?;
    write!(w, "\tmov x0, 0\n")?; // Exit code
    write!(w, "\tldr w0, [sp, -4]\n")?; // Exit code
    write!(w, "\tmov x16, 1\n")?; // Terminate svc
    write!(w, "\tsvc 0\n")?;
    write!(w, "\n")?;

    write!(w, "// Strings\n")?;
    for (s, sc) in &prog.strings {
        write!(w, "awestr__{}:\n", sc.index)?;
        write!(w, "\t.ascii \"")?;
        for ch in s.bytes() {
            if ch == b'"' {
                write!(w, "\\\"")?;
            } else if ch == b'\\' {
                write!(w, "\\\\")?;
            } else if ch == b'\r' {
                write!(w, "\\r")?;
            } else if ch == b'\n' {
                write!(w, "\\n")?;
            } else {
                w.write(&[ch])?;
            }
        }
        write!(w, "\\0\"\n")?;
    }

    Ok(())
}
