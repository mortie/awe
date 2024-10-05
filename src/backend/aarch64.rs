use std::io::Write;
use std::rc::Rc;

use super::common::{self, CodegenError, Result, Frame, MaybeTemp, MaybeTempKind};
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
        0 => return Ok(()),
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
        0 => return Ok(()),
        1 => write!(w, "\tstrb w{}, [sp, {}]\n", reg, doffset),
        2 => write!(w, "\tstrh w{}, [sp, {}]\n", reg, doffset),
        4 => write!(w, "\tstr w{}, [sp, {}]\n", reg, doffset),
        8 => write!(w, "\tstr x{}, [sp, {}]\n", reg, doffset),
        _ => panic!("Unsupported store size: {}", size),
    }?;

    Ok(())
}

fn gen_struct<W: Write>(
    frame: &mut Frame<W>,
    dest: &sst::LocalVar,
    s: &sst::Struct,
    exprs: &Vec<sst::Expression>,
) -> Result<()> {
    let count = s.fields.len();
    for i in 0..count {
        let field = &s.fields[i];
        let expr = &exprs[i];

        let var = sst::LocalVar {
            typ: field.typ.clone(),
            frame_offset: dest.frame_offset + field.offset as isize,
        };

        gen_expr_to(frame, expr, &var)?;
    }

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
        sst::BinOp::Mul => write!(w, "\tmul {r}0, {r}0, {r}1\n"),
        sst::BinOp::Div => match signed {
            true => write!(w, "\tsdiv {r}0, {r}0, {r}1\n"),
            false => write!(w, "\tudiv {r}0, {r}0, {r}1\n"),
        },
        sst::BinOp::Mod => {
            match signed {
                true => write!(w, "\tsdiv {r}2, {r}0, {r}1\n"),
                false => write!(w, "\tudiv {r}2, {r}0, {r}1\n"),
            }?;
            write!(w, "\tmsub {r}0, {r}2, {r}1, {r}0\n")
        }
        sst::BinOp::Add => write!(w, "\tadd {r}0, {r}0, {r}1\n"),
        sst::BinOp::Sub => write!(w, "\tsub {r}0, {r}0, {r}1\n"),

        sst::BinOp::Eq => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            write!(w, "\tcset {r}0, EQ\n")
        }

        sst::BinOp::Neq => {
            write!(w, "\tcmp {r}0, {r}1\n")?;
            write!(w, "\tcset {r}0, NE\n")
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
        sst::ExprKind::Literal(literal) => match literal {
            sst::Literal::Struct(s, exprs) => {
                write!(
                    &mut frame.w,
                    "\t// <Expression::Literal struct {}>\n",
                    s.name
                )?;
                gen_struct(frame, loc, s, exprs)?;
                write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
            }

            sst::Literal::Integer(num) => {
                write!(&mut frame.w, "\t// <Expression::Literal integer {}>\n", num)?;
                gen_integer(frame, loc, *num)?;
                write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
            }

            sst::Literal::String(sc) => {
                write!(
                    &mut frame.w,
                    "\t// <Expression::Literal string {}>\n",
                    sc.index
                )?;
                write!(&mut frame.w, "\tadr x0, awestr${}\n", sc.index)?;
                write!(&mut frame.w, "\tstr x0, [sp, {}]\n", frame_offset(loc))?;
                write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
            }

            sst::Literal::Bool(b) => {
                write!(&mut frame.w, "\t// <Expression::Literal bool {}>\n", b)?;
                if *b {
                    gen_integer(frame, loc, 1)?;
                } else {
                    gen_integer(frame, loc, 0)?;
                }
                write!(&mut frame.w, "\t// </Expression::Literal>\n")?;
            }
        },

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

        sst::ExprKind::Cast(sub) => {
            write!(
                &mut frame.w,
                "\t// <Expression::Cast {} -> {}>\n",
                sub.typ.name, loc.typ.name
            )?;
            let subloc = gen_expr(frame, sub)?;
            if subloc.var().typ.size < loc.typ.size {
                write!(&mut frame.w, "\tmov x0, 0\n")?;
            }
            gen_load(frame, 0, subloc.var())?;
            gen_store(frame, loc, 0)?;
            frame.maybe_pop_temp(subloc);
            write!(&mut frame.w, "\t// </Expression::Cast>\n")?;
        }

        sst::ExprKind::Assignment(..) => {
            write!(&mut frame.w, "\t// </Expression::Assignment::to>\n")?;
            let var = gen_expr(frame, expr)?;
            gen_copy(frame, loc, var.var())?;
            frame.maybe_pop_temp(var);
            write!(&mut frame.w, "\t// </Expression::Assignment::to>\n")?;
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

        sst::ExprKind::Reference(expr) => {
            write!(&mut frame.w, "\t// <Expression::Reference>\n")?;
            let var = gen_expr(frame, expr)?;
            let MaybeTempKind::NonTemp(var) = var.kind else {
                return Err(CodegenError::ReferenceToTemporary);
            };

            let o = frame_offset(&var);
            if o < 0 {
                write!(&mut frame.w, "\tsub x0, sp, {}\n", -o)?;
            } else {
                write!(&mut frame.w, "\tadd x0, sp, {}\n", o)?;
            }
            gen_store(frame, loc, 0)?;
            write!(&mut frame.w, "\t// </Expression::Reference>\n")?;
        }

        sst::ExprKind::MemberAccess(..) => {
            write!(&mut frame.w, "\t// <Expression::MemberAccess::to>\n")?;
            let var = gen_expr(frame, expr)?;
            gen_copy(frame, loc, var.var())?;
            frame.maybe_pop_temp(var);
            write!(&mut frame.w, "\t// </Expression::MemberAccess::to>\n")?;
        }
    }

    Ok(())
}

fn gen_expr<W: Write>(frame: &mut Frame<W>, expr: &sst::Expression) -> Result<MaybeTemp> {
    match &expr.kind {
        sst::ExprKind::Variable(var) => {
            write!(&mut frame.w, "\t// <Expression::Variable />\n")?;
            Ok(MaybeTemp::non_temp(var.as_ref().clone()))
        }

        sst::ExprKind::MemberAccess(expr, field) => {
            write!(&mut frame.w, "\t// <Expression::MemberAccess {}>\n", field.offset)?;
            let container = gen_expr(frame, expr)?;
            let var = sst::LocalVar {
                typ: field.typ.clone(),
                frame_offset: container.var().frame_offset + field.offset as isize,
            };
            let var = MaybeTemp::non_temp(var).with_container(container);
            write!(&mut frame.w, "\t// </Expression::MemberAccess>\n")?;
            Ok(var)
        }

        sst::ExprKind::Assignment(var, locators, expr) => {
            write!(&mut frame.w, "\t// <Expression::Assignment>\n")?;

            let mut mvar = MaybeTemp::non_temp(var.as_ref().clone());
            for locator in locators {
                match locator {
                    sst::Locator::MemberAccess(field) => {
                        let var = sst::LocalVar {
                            typ: field.typ.clone(),
                            frame_offset: mvar.var().frame_offset + field.offset as isize,
                        };
                        mvar = MaybeTemp::non_temp(var).with_container(mvar);
                    }
                }
            }

            gen_expr_to(frame, expr, mvar.var())?;
            write!(&mut frame.w, "\t// </Expression::Assignment>\n")?;
            Ok(mvar)
        }

        _ => {
            let temp = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &temp)?;
            Ok(MaybeTemp::temp(temp))
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
            write!(
                &mut frame.w,
                "\tb awe${}$L{}\n",
                fname, labels.continue_label
            )?;
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

        sst::Statement::Debugger => {
            write!(&mut frame.w, "\t// <Statement::Debugger>\n")?;
            write!(&mut frame.w, "\tbrk 0\n")?;
            write!(&mut frame.w, "\t// </Statement::Debugger>\n")?;
        }

        sst::Statement::Expression(expr) => {
            write!(&mut frame.w, "\t// <Statement::Expression>\n")?;
            let temp = gen_expr(frame, expr)?;
            frame.maybe_pop_temp(temp);
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
