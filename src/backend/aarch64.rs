use std::io::Write;
use std::rc::Rc;

use super::common::{self, CodegenError, Result};
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

enum MaybeTemp {
    Temp(sst::LocalVar),
    NonTemp(Rc<sst::LocalVar>),
}

impl MaybeTemp {
    fn var(&self) -> &sst::LocalVar {
        match self {
            Self::Temp(var) => var,
            Self::NonTemp(var) => var,
        }
    }
}

#[derive(Clone)]
struct Loop {
    break_label: usize,
    continue_label: usize
}

struct Frame<'a, W: Write> {
    w: W,
    func: &'a sst::Function,
    stack_size: usize,
    temps: Vec<TempVar>,
    sentinel: Rc<sst::Type>,
    next_label: usize,
    loops: Vec<Loop>,
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
            next_label: 0,
            loops: Vec::new(),
        }
    }

    fn push_temp(&mut self, typ: Rc<sst::Type>) -> sst::LocalVar {
        let stack_base = self.stack_size;
        while typ.align > 0 && self.stack_size % typ.align != 0 {
            self.stack_size += 1;
        }

        let frame_offset = self.stack_size;
        self.stack_size += typ.size;

        self.temps.push(TempVar {
            typ: typ.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar {
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

        self.temps.push(TempVar {
            typ: self.sentinel.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar {
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
                last.typ.name, var.typ.name
            );
        }

        if last.frame_offset as isize != var.frame_offset {
            panic!(
                "pop_temp called with wrong frame_offset: expected {}, got {}",
                last.frame_offset, var.frame_offset
            );
        }

        self.stack_size = last.stack_base;
    }

    fn maybe_pop_temp(&mut self, var: MaybeTemp) {
        if let MaybeTemp::Temp(temp) = var {
            self.pop_temp(temp);
        }
    }

    fn label(&mut self) -> usize {
        let label = self.next_label;
        self.next_label += 1;
        label
    }

    fn push_loop(&mut self) -> Loop {
        let labels = Loop {
            break_label: self.label(),
            continue_label: self.label(),
        };
        self.loops.push(labels.clone());
        labels
    }

    fn top_loop(&self) -> Option<Loop> {
        if let Some(labels) = self.loops.first() {
            return Some(labels.clone())
        }

        None
    }

    fn pop_loop(&mut self) {
        self.loops.pop();
    }

    fn done(self) -> W {
        self.w
    }
}

fn frame_offset(var: &sst::LocalVar) -> isize {
    -(var.frame_offset + var.typ.size as isize)
}

fn gen_load<W: Write>(frame: &mut Frame<W>, reg: u8, src: &sst::LocalVar) -> Result<()> {
    let soffset = frame_offset(src);
    let size = src.typ.size;
    let s = match src.typ.kind {
        sst::TypeKind::Primitive(sst::Primitive::Int) => "s",
        _ => "",
    };

    let w = &mut frame.w;
    match size {
        1 => write!(w, "\tldr{}b w{}, [sp, {}]\n", s, reg, soffset),
        2 => write!(w, "\tldr{}h w{}, [sp, {}]\n", s, reg, soffset),
        4 => write!(w, "\tldr w{}, [sp, {}]\n", reg, soffset),
        8 => write!(w, "\tldr x{}, [sp, {}]\n", reg, soffset),
        _ => panic!("Unsupported load size: {}", size),
    }?;

    Ok(())
}

fn gen_store<W: Write>(frame: &mut Frame<W>, dest: &sst::LocalVar, reg: u8) -> Result<()> {
    let doffset = frame_offset(dest);
    let size = dest.typ.size;

    let w = &mut frame.w;
    match size {
        1 => write!(w, "\tstrb w{}, [sp, {}]\n", reg, doffset),
        2 => write!(w, "\tstrh w{}, [sp, {}]\n", reg, doffset),
        4 => write!(w, "\tstr w{}, [sp, {}]\n", reg, doffset),
        8 => write!(w, "\tstr x{}, [sp, {}]\n", reg, doffset),
        _ => panic!("Unsupported store size: {}", size),
    }?;

    Ok(())
}

fn gen_integer<W: Write>(frame: &mut Frame<W>, dest: &sst::LocalVar, num: i128) -> Result<()> {
    let size = dest.typ.size;

    let w = &mut frame.w;
    match size {
        1 => write!(w, "\tmov w0, {}\n", num),
        2 => write!(w, "\tmov w0, {}\n", num),
        4 => write!(w, "\tmov w0, {}\n", num),
        8 => write!(w, "\tmov x0, {}\n", num),
        _ => panic!("Unsupported integer size: {}", size),
    }?;

    gen_store(frame, dest, 0)
}

fn gen_binop<W: Write>(
    frame: &mut Frame<W>,
    dest: &sst::LocalVar,
    lhs: &sst::LocalVar,
    op: sst::BinOp,
    rhs: &sst::LocalVar,
) -> Result<()> {
    let size = lhs.typ.size;
    gen_load(frame, 0, lhs)?;
    gen_load(frame, 1, rhs)?;

    // Register prefix
    let r = match size {
        0..=4 => "w",
        _ => "x",
    };

    // Signedness
    let signed = match lhs.typ.kind {
        sst::TypeKind::Primitive(sst::Primitive::Int) => true,
        _ => false,
    };

    let w = &mut frame.w;
    match op {
        sst::BinOp::Add => write!(w, "\tadd {r}0, {r}0, {r}1\n"),
        sst::BinOp::Sub => write!(w, "\tsub {r}0, {r}0, {r}1\n"),
        sst::BinOp::Mul => write!(w, "\tmul {r}0, {r}0, {r}1\n"),
        sst::BinOp::Div => match signed {
            true => write!(w, "\tsdiv {r}0, {r}0, {r}1\n"),
            false => write!(w, "\tudiv {r}0, {r}0, {r}1\n"),
        }

        sst::BinOp::Eq => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            write!(w, "\tcset {r}0, EQ\n")
        }

        sst::BinOp::Neq => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            write!(w, "\tcset {r}0, zr, zr, NE\n")
        }

        sst::BinOp::Lt => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            match signed {
                true => write!(w, "\tcset {r}0, LT\n"),
                false => write!(w, "\tcset {r}0, LO\n"),
            }
        }

        sst::BinOp::Leq => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            match signed {
                true => write!(w, "\tcset {r}0, LE\n"),
                false => write!(w, "\tcset {r}0, LS\n"),
            }
        }
    }?;

    gen_store(frame, dest, 0)
}

fn gen_copy<W: Write>(
    frame: &mut Frame<W>,
    dest: &sst::LocalVar,
    src: &sst::LocalVar,
) -> Result<()> {
    if dest.typ.size != src.typ.size {
        return Err(CodegenError::SizeMismatch(dest.typ.size, src.typ.size));
    }

    if dest.frame_offset == src.frame_offset {
        return Ok(());
    }

    gen_load(frame, 0, src)?;
    gen_store(frame, dest, 0)
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
                    write!(&mut frame.w, "\tadr x0, awestr${}\n", sc.index)?;
                    write!(&mut frame.w, "\tstr x0, [sp, {}]\n", frame_offset(loc))?;
                }

                sst::Literal::Bool(b) => {
                    if *b {
                        gen_integer(frame, loc, 1)?;
                    } else {
                        gen_integer(frame, loc, 0)?;
                    }
                }
            }
            write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
        }

        sst::ExprKind::FuncCall(signature, params) => {
            write!(
                &mut frame.w,
                "\t// <Expression::FuncCall {}>\n",
                signature.name
            )?;
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
            write!(&mut frame.w, "\tbl awe${}\n", signature.name)?;
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
            write!(
                &mut frame.w,
                "\t// <Expression::Variable loc:{}>\n",
                var.frame_offset
            )?;
            gen_copy(frame, loc, var)?;
            write!(&mut frame.w, "\t// </Expression::Variable>\n")?;
        }

        sst::ExprKind::BinOp(lhs, op, rhs) => {
            write!(&mut frame.w, "\t// <Expression::BinOp {:?}>\n", op)?;
            let lhs_var = gen_expr(frame, lhs)?;
            let rhs_var = gen_expr(frame, rhs)?;
            gen_binop(frame, loc, lhs_var.var(), *op, rhs_var.var())?;
            frame.maybe_pop_temp(rhs_var);
            frame.maybe_pop_temp(lhs_var);
            write!(&mut frame.w, "\t// </Expression::BinOp>\n")?;
        }
    }

    Ok(())
}

fn gen_expr<W: Write>(frame: &mut Frame<W>, expr: &sst::Expression) -> Result<MaybeTemp> {
    match &expr.kind {
        sst::ExprKind::Variable(var) => Ok(MaybeTemp::NonTemp(var.clone())),

        _ => {
            let temp = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &temp)?;
            Ok(MaybeTemp::Temp(temp))
        }
    }
}

fn gen_return<W: Write>(frame: &mut Frame<W>) -> Result<()> {
    // Read the return address into bl if necessary, and ret
    if !frame.func.is_leaf {
        write!(
            frame.w,
            "\tldr lr, [sp, {}]\n",
            frame_offset(&frame.func.return_addr)
        )?;
    }
    write!(frame.w, "\tret\n")?;
    Ok(())
}

fn gen_stmt<W: Write>(frame: &mut Frame<W>, stmt: &sst::Statement) -> Result<()> {
    match stmt {
        sst::Statement::If(cond, body, else_body) => {
            write!(&mut frame.w, "\t// <Statement::If>\n")?;
            let fname = frame.func.signature.name.as_str();
            let else_label = frame.label();
            let end_label = frame.label();
            let condvar = gen_expr(frame, cond)?;

            write!(
                &mut frame.w,
                "\tldrb w0, [sp, {}]\n",
                frame_offset(condvar.var())
            )?;
            frame.maybe_pop_temp(condvar);

            write!(&mut frame.w, "\tcbz w0, awe${}$L{}\n", fname, else_label)?;
            gen_stmt(frame, body)?;
            write!(&mut frame.w, "\tb awe${}$L{}\n", fname, end_label)?;

            write!(&mut frame.w, "awe${}$L{}:\n", fname, else_label)?;
            gen_stmt(frame, else_body)?;

            write!(&mut frame.w, "awe${}$L{}:\n", fname, end_label)?;
            write!(&mut frame.w, "\t// </Statement::If>\n")?;
        }

        sst::Statement::Loop(body) => {
            write!(&mut frame.w, "\t// <Statement::Loop>\n")?;
            let fname = frame.func.signature.name.as_str();
            let labels = frame.push_loop();
            write!(&mut frame.w, "awe${}$L{}:\n", fname, labels.continue_label)?;
            gen_stmt(frame, body)?;
            write!(&mut frame.w, "\tb awe${}$L{}\n", fname, labels.continue_label)?;
            write!(&mut frame.w, "awe${}$L{}:\n", fname, labels.break_label)?;
            frame.pop_loop();
            write!(&mut frame.w, "\t// </Statement::Loop>\n")?;
        }

        sst::Statement::Return(expr) => {
            write!(&mut frame.w, "\t// <Statement::Return>\n")?;
            if let Some(expr) = expr {
                let retvar = frame.func.return_var.clone();
                gen_expr_to(frame, expr, &retvar)?;
            }
            gen_return(frame)?;
            write!(&mut frame.w, "\t// </Statement::Return>\n")?;
        }

        sst::Statement::Break => {
            write!(&mut frame.w, "\t// <Statement::Break>\n")?;
            let Some(labels) = frame.top_loop() else {
                return Err(CodegenError::InvalidBreak);
            };

            let fname = frame.func.signature.name.as_str();
            write!(&mut frame.w, "\tb awe${}$L{}\n", fname, labels.break_label)?;
            write!(&mut frame.w, "\t// </Statement::Break>\n")?;
        }

        sst::Statement::VarDecl(var, expr) => {
            write!(&mut frame.w, "\t// <Statement::VarDecl>\n")?;
            gen_expr_to(frame, expr, &var)?;
            write!(&mut frame.w, "\t// </Statement::VarDecl>\n")?;
        }

        sst::Statement::Block(stmts) => {
            write!(&mut frame.w, "\t// <Statement::Block>\n")?;
            for stmt in stmts {
                gen_stmt(frame, stmt)?;
            }
            write!(&mut frame.w, "\t// </Statement::Block>\n")?;
        }

        sst::Statement::Expression(expr) => {
            write!(&mut frame.w, "\t// <Statement::Expression>\n")?;
            let local = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &local)?;
            frame.pop_temp(local);
            write!(&mut frame.w, "\t// </Statement::Expression>\n")?;
        }

        sst::Statement::Empty => {
            write!(&mut frame.w, "\t// </Statement::Empty />\n")?;
        }
    }

    Ok(())
}

fn gen_func<W: Write>(frame: &mut Frame<W>) -> Result<()> {
    common::gen_signature_comment(&mut frame.w, &frame.func.signature)?;
    write!(frame.w, ".global awe${}\n", frame.func.signature.name)?;
    write!(frame.w, ".balign 4\n")?;
    write!(frame.w, "awe${}:\n", frame.func.signature.name)?;

    // We expect to have been called using the 'bl' instruction,
    // which puts the return pointer in the link register.
    // Therefore, we have to write the link register to the stack,
    // in order to conform to the expected stack layout.
    // We also need to put the stack pointer in the frame pointer.
    // Then, we allocate stack space for all the local variables.
    if !frame.func.is_leaf {
        write!(
            frame.w,
            "\tstr lr, [sp, {}]\n",
            frame_offset(&frame.func.return_addr)
        )?;
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
    let sentinel = Rc::new(sst::Type {
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

    write!(w, "// Strings\n")?;
    for (sc, s) in &prog.strings {
        write!(w, "awestr${}:\n", sc.index)?;
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
