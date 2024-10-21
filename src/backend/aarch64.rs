use std::io::Write;
use std::rc::Rc;

use super::common::{self, CodegenError, Frame, MaybeTemp, Result};
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

fn struct_field_offset(var: &sst::LocalVar, field: &sst::FieldDecl) -> sst::LocalVar {
    let base = var.frame_offset + var.typ.size as isize;
    sst::LocalVar {
        typ: field.typ.clone(),
        frame_offset: base - field.offset as isize - field.typ.size as isize,
    }

}

fn gen_load_from_reg(
    frame: &mut Frame,
    dest: u8,
    src: u8,
    offset: usize,
    size: usize,
) -> Result<()> {
    let w = &mut frame.w;
    match size {
        0 => return Ok(()),
        1 => writeln!(w, "\tldrb w{dest}, [x{src}, {offset}]"),
        2 => writeln!(w, "\tldrh w{dest}, [x{src}, {offset}]"),
        4 => writeln!(w, "\tldr w{dest}, [x{src}, {offset}]"),
        8 => writeln!(w, "\tldr x{dest}, [x{src}, {offset}]"),
        _ => panic!("Unsupported load size: {}", size),
    }?;

    Ok(())
}

fn gen_load(frame: &mut Frame, reg: u8, src: &sst::LocalVar) -> Result<()> {
    let soffset = frame_offset(src);
    let size = src.typ.size;
    let s = match src.typ.kind {
        sst::TypeKind::Primitive(sst::Primitive::Int) => "s",
        _ => "",
    };

    let w = &mut frame.w;
    match size {
        0 => return Ok(()),
        1 => writeln!(w, "\tldr{}b w{}, [sp, {}]", s, reg, soffset),
        2 => writeln!(w, "\tldr{}h w{}, [sp, {}]", s, reg, soffset),
        4 => writeln!(w, "\tldr w{}, [sp, {}]", reg, soffset),
        8 => writeln!(w, "\tldr x{}, [sp, {}]", reg, soffset),
        _ => panic!("Unsupported load size: {}", size),
    }?;

    Ok(())
}

fn gen_store(frame: &mut Frame, dest: &sst::LocalVar, reg: u8) -> Result<()> {
    let doffset = frame_offset(dest);
    let size = dest.typ.size;

    let w = &mut frame.w;
    match size {
        0 => return Ok(()),
        1 => writeln!(w, "\tstrb w{}, [sp, {}]", reg, doffset),
        2 => writeln!(w, "\tstrh w{}, [sp, {}]", reg, doffset),
        4 => writeln!(w, "\tstr w{}, [sp, {}]", reg, doffset),
        8 => writeln!(w, "\tstr x{}, [sp, {}]", reg, doffset),
        _ => panic!("Unsupported store size: {}", size),
    }?;

    Ok(())
}

fn gen_struct(
    frame: &mut Frame,
    dest: &sst::LocalVar,
    s: &sst::Struct,
    exprs: &[sst::Expression],
) -> Result<()> {
    for (i, field) in s.fields.iter().enumerate() {
        gen_expr_to(frame, &exprs[i], &struct_field_offset(dest, field))?;
    }

    Ok(())
}

fn gen_integer(frame: &mut Frame, dest: &sst::LocalVar, num: i128) -> Result<()> {
    let size = dest.typ.size;

    let w = &mut frame.w;
    match size {
        1 => writeln!(w, "\tmov w0, {}", num),
        2 => writeln!(w, "\tmov w0, {}", num),
        4 => writeln!(w, "\tmov w0, {}", num),
        8 => writeln!(w, "\tmov x0, {}", num),
        _ => panic!("Unsupported integer size: {}", size),
    }?;

    gen_store(frame, dest, 0)
}

fn gen_binop(
    frame: &mut Frame,
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
    let signed = matches!(lhs.typ.kind, sst::TypeKind::Primitive(sst::Primitive::Int));

    let w = &mut frame.w;
    match op {
        sst::BinOp::Mul => writeln!(w, "\tmul {r}0, {r}0, {r}1"),
        sst::BinOp::Div => match signed {
            true => writeln!(w, "\tsdiv {r}0, {r}0, {r}1"),
            false => writeln!(w, "\tudiv {r}0, {r}0, {r}1"),
        },
        sst::BinOp::Mod => {
            match signed {
                true => writeln!(w, "\tsdiv {r}2, {r}0, {r}1"),
                false => writeln!(w, "\tudiv {r}2, {r}0, {r}1"),
            }?;
            writeln!(w, "\tmsub {r}0, {r}2, {r}1, {r}0")
        }
        sst::BinOp::Add => writeln!(w, "\tadd {r}0, {r}0, {r}1"),
        sst::BinOp::Sub => writeln!(w, "\tsub {r}0, {r}0, {r}1"),

        sst::BinOp::Eq => {
            writeln!(w, "\tcmp {r}0, {r}1")?;
            writeln!(w, "\tcset {r}0, EQ")
        }

        sst::BinOp::Neq => {
            writeln!(w, "\tcmp {r}0, {r}1")?;
            writeln!(w, "\tcset {r}0, NE")
        }

        sst::BinOp::Lt => {
            writeln!(w, "\tcmp {r}0, {r}1")?;
            match signed {
                true => writeln!(w, "\tcset {r}0, LT"),
                false => writeln!(w, "\tcset {r}0, LO"),
            }
        }

        sst::BinOp::Leq => {
            writeln!(w, "\tcmp {r}0, {r}1")?;
            match signed {
                true => writeln!(w, "\tcset {r}0, LE"),
                false => writeln!(w, "\tcset {r}0, LS"),
            }
        }
    }?;

    gen_store(frame, dest, 0)
}

fn gen_copy(frame: &mut Frame, dest: &sst::LocalVar, src: &sst::LocalVar) -> Result<()> {
    if dest.typ.size != src.typ.size {
        return Err(CodegenError::SizeMismatch(dest.typ.size, src.typ.size));
    }

    if dest.frame_offset == src.frame_offset {
        return Ok(());
    }

    let mut soffset = frame_offset(src);
    let mut doffset = frame_offset(dest);
    let mut size = dest.typ.size;
    let w = &mut frame.w;

    while size >= 8 {
        writeln!(w, "\tldr x0, [sp, {soffset}]")?;
        writeln!(w, "\tstr x0, [sp, {doffset}]")?;
        soffset += 8;
        doffset += 8;
        size -= 8;
    }

    while size >= 4 {
        writeln!(w, "\tldr w0, [sp, {soffset}]")?;
        writeln!(w, "\tstr w0, [sp, {doffset}]")?;
        soffset += 4;
        doffset += 4;
        size -= 4;
    }

    while size >= 2 {
        writeln!(w, "\tldrh w0, [sp, {soffset}]")?;
        writeln!(w, "\tstrh w0, [sp, {doffset}]")?;
        soffset += 2;
        doffset += 2;
        size -= 2;
    }

    while size >= 1 {
        writeln!(w, "\tldrb w0, [sp, {soffset}]")?;
        writeln!(w, "\tstrb w0, [sp, {doffset}]")?;
        soffset += 1;
        doffset += 1;
        size -= 1;
    }

    Ok(())
}

fn gen_expr_to(frame: &mut Frame, expr: &sst::Expression, loc: &sst::LocalVar) -> Result<()> {
    match &expr.kind {
        sst::ExprKind::Literal(literal) => match literal {
            sst::Literal::Struct(s, exprs) => {
                writeln!(&mut frame.w, "\t// <Expression::Literal struct {}>", s.name)?;
                gen_struct(frame, loc, s, exprs)?;
                writeln!(&mut frame.w, "\t// </Expression::Literal>")?;
            }

            sst::Literal::Integer(num) => {
                writeln!(&mut frame.w, "\t// <Expression::Literal integer {}>", num)?;
                gen_integer(frame, loc, *num)?;
                writeln!(&mut frame.w, "\t// </Expression::Literal>")?;
            }

            sst::Literal::String(sc) => {
                writeln!(
                    &mut frame.w,
                    "\t// <Expression::Literal string {}>",
                    sc.index
                )?;
                let offset = frame_offset(loc);
                writeln!(&mut frame.w, "\tadr x0, awestr${}", sc.index)?;
                writeln!(&mut frame.w, "\tstr x0, [sp, {}]", offset)?;
                writeln!(&mut frame.w, "\tmov x0, {}", sc.length)?;
                writeln!(&mut frame.w, "\tstr x0, [sp, {}]", offset + 8)?;
                writeln!(&mut frame.w, "\t// </Expression::Literal>")?;
            }

            sst::Literal::Bool(b) => {
                writeln!(&mut frame.w, "\t// <Expression::Literal bool {}>", b)?;
                if *b {
                    gen_integer(frame, loc, 1)?;
                } else {
                    gen_integer(frame, loc, 0)?;
                }
                writeln!(&mut frame.w, "\t// </Expression::Literal>")?;
            }
        },

        sst::ExprKind::FuncCall(signature, params) => {
            writeln!(
                &mut frame.w,
                "\t// <Expression::FuncCall {}>",
                signature.name
            )?;
            let aligned = frame.push_align(16);

            let return_var = frame.push_temp(signature.ret.clone());

            let mut param_vars = Vec::<sst::LocalVar>::with_capacity(params.len());
            for param in params {
                let var = frame.push_temp(param.typ.clone());
                gen_expr_to(frame, param, &var)?;
                param_vars.push(var);
            }

            let symbol_name = common::mangle_name(&signature.name);
            writeln!(&mut frame.w, "\tsub sp, sp, {}", aligned.frame_offset)?;
            writeln!(&mut frame.w, "\tbl awe${}", symbol_name)?;
            writeln!(&mut frame.w, "\tadd sp, sp, {}", aligned.frame_offset)?;

            while let Some(var) = param_vars.pop() {
                frame.pop_temp(var);
            }

            gen_copy(frame, loc, &return_var)?;

            frame.pop_temp(return_var);
            frame.pop_temp(aligned);
            writeln!(&mut frame.w, "\t// </Expression::FuncCall>")?;
        }

        sst::ExprKind::Cast(sub) => {
            writeln!(
                &mut frame.w,
                "\t// <Expression::Cast {} -> {}>",
                sub.typ.name, loc.typ.name
            )?;
            let subloc = gen_expr(frame, sub)?;
            if subloc.var().typ.size < loc.typ.size {
                writeln!(&mut frame.w, "\tmov x0, 0")?;
            }
            gen_load(frame, 0, subloc.var())?;
            gen_store(frame, loc, 0)?;
            frame.maybe_pop_temp(subloc);
            writeln!(&mut frame.w, "\t// </Expression::Cast>")?;
        }

        sst::ExprKind::Assignment(..) => {
            writeln!(&mut frame.w, "\t// </Expression::Assignment::to>")?;
            let var = gen_expr(frame, expr)?;
            gen_copy(frame, loc, var.var())?;
            frame.maybe_pop_temp(var);
            writeln!(&mut frame.w, "\t// </Expression::Assignment::to>")?;
        }

        sst::ExprKind::Uninitialized => {
            writeln!(&mut frame.w, "\t// <Expression::Uninitialized />")?;
        }

        sst::ExprKind::Variable(var) => {
            writeln!(
                &mut frame.w,
                "\t// <Expression::Variable loc:{}>",
                var.frame_offset
            )?;
            gen_copy(frame, loc, var)?;
            writeln!(&mut frame.w, "\t// </Expression::Variable>")?;
        }

        sst::ExprKind::BinOp(lhs, op, rhs) => {
            writeln!(&mut frame.w, "\t// <Expression::BinOp {:?}>", op)?;
            let lhs_var = gen_expr(frame, lhs)?;
            let rhs_var = gen_expr(frame, rhs)?;
            gen_binop(frame, loc, lhs_var.var(), *op, rhs_var.var())?;
            frame.maybe_pop_temp(rhs_var);
            frame.maybe_pop_temp(lhs_var);
            writeln!(&mut frame.w, "\t// </Expression::BinOp>")?;
        }

        sst::ExprKind::Reference(expr) => {
            writeln!(&mut frame.w, "\t// <Expression::Reference>")?;
            let var = gen_expr(frame, expr)?;
            if var.is_temp() {
                return Err(CodegenError::ReferenceToTemporary);
            }

            let o = frame_offset(var.var());
            if o < 0 {
                writeln!(&mut frame.w, "\tsub x0, sp, {}", -o)?;
            } else {
                writeln!(&mut frame.w, "\tadd x0, sp, {}", o)?;
            }
            gen_store(frame, loc, 0)?;
            frame.maybe_pop_temp(var);
            writeln!(&mut frame.w, "\t// </Expression::Reference>")?;
        }

        sst::ExprKind::Dereference(expr) => {
            writeln!(&mut frame.w, "\t// <Expression::Dereference>")?;
            let ptr_var = gen_expr(frame, expr)?;
            gen_load(frame, 0, ptr_var.var())?;
            gen_load_from_reg(frame, 0, 0, 0, loc.typ.size)?;
            gen_store(frame, loc, 0)?;
            frame.maybe_pop_temp(ptr_var);
            writeln!(&mut frame.w, "\t// </Expression::Dereference>")?;
        }

        sst::ExprKind::DerefAccess(expr, field) => {
            writeln!(&mut frame.w, "\t// <Expression::Dereference>")?;
            let ptr_var = gen_expr(frame, expr)?;
            gen_load(frame, 0, ptr_var.var())?;
            gen_load_from_reg(frame, 0, 0, field.offset, loc.typ.size)?;
            gen_store(frame, loc, 0)?;
            frame.maybe_pop_temp(ptr_var);
            writeln!(&mut frame.w, "\t// </Expression::Dereference>")?;
        }

        sst::ExprKind::MemberAccess(..) => {
            writeln!(&mut frame.w, "\t// <Expression::MemberAccess::to>")?;
            let var = gen_expr(frame, expr)?;
            gen_copy(frame, loc, var.var())?;
            frame.maybe_pop_temp(var);
            writeln!(&mut frame.w, "\t// </Expression::MemberAccess::to>")?;
        }
    }

    Ok(())
}

fn gen_expr(frame: &mut Frame, expr: &sst::Expression) -> Result<MaybeTemp> {
    match &expr.kind {
        sst::ExprKind::Variable(var) => {
            writeln!(&mut frame.w, "\t// <Expression::Variable />")?;
            Ok(MaybeTemp::non_temp(var.as_ref().clone()))
        }

        sst::ExprKind::MemberAccess(expr, field) => {
            writeln!(
                &mut frame.w,
                "\t// <Expression::MemberAccess {}>",
                field.offset
            )?;
            let container = gen_expr(frame, expr)?;
            let var = struct_field_offset(container.var(), field);
            let var = MaybeTemp::non_temp(var).with_container(container);
            writeln!(&mut frame.w, "\t// </Expression::MemberAccess>")?;
            Ok(var)
        }

        sst::ExprKind::Assignment(var, locators, expr) => {
            writeln!(&mut frame.w, "\t// <Expression::Assignment>")?;

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
            writeln!(&mut frame.w, "\t// </Expression::Assignment>")?;
            Ok(mvar)
        }

        _ => {
            let temp = frame.push_temp(expr.typ.clone());
            gen_expr_to(frame, expr, &temp)?;
            Ok(MaybeTemp::temp(temp))
        }
    }
}

fn gen_return(frame: &mut Frame) -> Result<()> {
    // Read the return address into bl if necessary, and ret
    if !frame.func.is_leaf {
        writeln!(
            frame.w,
            "\tldr lr, [sp, {}]",
            frame_offset(&frame.func.return_addr)
        )?;
    }
    writeln!(frame.w, "\tret")?;
    Ok(())
}

fn gen_stmt(frame: &mut Frame, stmt: &sst::Statement) -> Result<()> {
    match stmt {
        sst::Statement::If(cond, body, else_body) => {
            writeln!(&mut frame.w, "\t// <Statement::If>")?;
            let fname = frame.symbol_name.clone();
            let else_label = frame.label();
            let end_label = frame.label();
            let condvar = gen_expr(frame, cond)?;

            writeln!(
                &mut frame.w,
                "\tldrb w0, [sp, {}]",
                frame_offset(condvar.var())
            )?;
            frame.maybe_pop_temp(condvar);

            writeln!(&mut frame.w, "\tcbz w0, awe${}$L{}", fname, else_label)?;
            gen_stmt(frame, body)?;
            writeln!(&mut frame.w, "\tb awe${}$L{}", fname, end_label)?;

            writeln!(&mut frame.w, "awe${}$L{}:", fname, else_label)?;
            gen_stmt(frame, else_body)?;

            writeln!(&mut frame.w, "awe${}$L{}:", fname, end_label)?;
            writeln!(&mut frame.w, "\t// </Statement::If>")?;
        }

        sst::Statement::Loop(body) => {
            writeln!(&mut frame.w, "\t// <Statement::Loop>")?;
            let fname = frame.symbol_name.clone();
            let labels = frame.push_loop();
            writeln!(&mut frame.w, "awe${}$L{}:", fname, labels.continue_label)?;
            gen_stmt(frame, body)?;
            writeln!(&mut frame.w, "\tb awe${}$L{}", fname, labels.continue_label)?;
            writeln!(&mut frame.w, "awe${}$L{}:", fname, labels.break_label)?;
            frame.pop_loop();
            writeln!(&mut frame.w, "\t// </Statement::Loop>")?;
        }

        sst::Statement::Return(expr) => {
            writeln!(&mut frame.w, "\t// <Statement::Return>")?;
            if let Some(expr) = expr {
                let retvar = frame.func.return_var.clone();
                gen_expr_to(frame, expr, &retvar)?;
            }
            gen_return(frame)?;
            writeln!(&mut frame.w, "\t// </Statement::Return>")?;
        }

        sst::Statement::Break => {
            writeln!(&mut frame.w, "\t// <Statement::Break>")?;
            let Some(labels) = frame.top_loop() else {
                return Err(CodegenError::InvalidBreak);
            };

            let fname = frame.symbol_name.clone();
            writeln!(&mut frame.w, "\tb awe${}$L{}", fname, labels.break_label)?;
            writeln!(&mut frame.w, "\t// </Statement::Break>")?;
        }

        sst::Statement::VarDecl(var, expr) => {
            writeln!(&mut frame.w, "\t// <Statement::VarDecl>")?;
            gen_expr_to(frame, expr, var)?;
            writeln!(&mut frame.w, "\t// </Statement::VarDecl>")?;
        }

        sst::Statement::Block(stmts) => {
            writeln!(&mut frame.w, "\t// <Statement::Block>")?;
            for stmt in stmts {
                gen_stmt(frame, stmt)?;
            }
            writeln!(&mut frame.w, "\t// </Statement::Block>")?;
        }

        sst::Statement::Debugger => {
            writeln!(&mut frame.w, "\t// <Statement::Debugger>")?;
            writeln!(&mut frame.w, "\tbrk 0")?;
            writeln!(&mut frame.w, "\t// </Statement::Debugger>")?;
        }

        sst::Statement::Expression(expr) => {
            writeln!(&mut frame.w, "\t// <Statement::Expression>")?;
            let temp = gen_expr(frame, expr)?;
            frame.maybe_pop_temp(temp);
            writeln!(&mut frame.w, "\t// </Statement::Expression>")?;
        }

        sst::Statement::Empty => {
            writeln!(&mut frame.w, "\t// </Statement::Empty />")?;
        }
    }

    Ok(())
}

fn gen_func(frame: &mut Frame) -> Result<()> {
    common::gen_signature_comment(&mut frame.w, &frame.func.signature)?;
    writeln!(frame.w, ".global awe${}", frame.symbol_name)?;
    writeln!(frame.w, ".balign 4")?;
    writeln!(frame.w, "awe${}:", frame.symbol_name)?;

    // We expect to have been called using the 'bl' instruction,
    // which puts the return pointer in the link register.
    // Therefore, we have to write the link register to the stack,
    // in order to conform to the expected stack layout.
    // We also need to put the stack pointer in the frame pointer.
    // Then, we allocate stack space for all the local variables.
    if !frame.func.is_leaf {
        writeln!(
            frame.w,
            "\tstr lr, [sp, {}]",
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

    writeln!(frame.w)?;
    Ok(())
}

pub fn codegen(w: &mut dyn Write, prog: &sst::Program) -> Result<()> {
    let sentinel = Rc::new(sst::Type {
        name: Rc::new("<sentinel>".to_owned()),
        size: 0,
        align: 0,
        kind: sst::TypeKind::Primitive(sst::Primitive::Void),
    });

    for func in &prog.functions {
        let mut frame = Frame::new(w, func, sentinel.clone());
        gen_func(&mut frame)?;
    }

    writeln!(w, "// Strings")?;
    for (sc, s) in &prog.strings {
        writeln!(w, "awestr${}:", sc.index)?;
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
                w.write_all(&[ch])?;
            }
        }
        writeln!(w, "\\0\"")?;
    }

    Ok(())
}
