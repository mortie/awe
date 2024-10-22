use std::io::{self, Write};
use std::iter::zip;

use super::sst;

type Result = io::Result<()>;

fn indent(w: &mut dyn Write, mut depth: u32) -> Result {
    while depth > 0 {
        write!(w, "    ")?;
        depth -= 1;
    }
    Ok(())
}

fn write_literal(w: &mut dyn Write, lit: &sst::Literal, depth: u32) -> Result {
    match lit {
        sst::Literal::Struct(sd, exprs) => {
            writeln!(w, "struct {{")?;
            for (field, expr) in zip(sd.fields.iter(), exprs.iter()) {
                indent(w, depth + 1)?;
                write!(w, "{} @ {}: ", field.name, field.offset)?;
                write_expr(w, expr, depth + 1)?;
                writeln!(w)?;
            }
            indent(w, depth)?;
            write!(w, "}}")?;
        }
        sst::Literal::Integer(num) => {
            write!(w, "{num}")?;
        }
        sst::Literal::String(sc) => {
            write!(w, "string {}:{}", sc.index, sc.length)?;
        }
        sst::Literal::Bool(b) => {
            write!(w, "{b}")?;
        }
    }

    Ok(())
}

fn write_expr(w: &mut dyn Write, expr: &sst::Expression, depth: u32) -> Result {
    write!(w, "[{}] ", expr.typ.name)?;
    match &expr.kind {
        sst::ExprKind::Literal(lit) => {
            write_literal(w, lit, depth)?;
        }
        sst::ExprKind::FuncCall(sig, exprs) => {
            if exprs.is_empty() {
                write!(w, "call {}()", sig.name)?;
            } else {
                writeln!(w, "call {}(", sig.name)?;
                indent(w, depth + 1)?;
                let mut first = true;
                for expr in exprs {
                    if !first {
                        writeln!(w, ",")?;
                        indent(w, depth + 1)?;
                    }
                    first = false;

                    write_expr(w, expr, depth + 1)?;
                }
                write!(w, ")")?;
            }
        }
        sst::ExprKind::Cast(expr) => {
            write!(w, "cast(")?;
            write_expr(w, expr, depth)?;
            write!(w, ")")?;
        }
        sst::ExprKind::Assignment(var, loc, expr) => {
            write!(w, "assign var {} : {:?} = ", var.frame_offset, loc)?;
            write_expr(w, expr, depth)?;
        }
        sst::ExprKind::Uninitialized => {
            write!(w, "uninitialized")?;
        }
        sst::ExprKind::Variable(var) => {
            write!(w, "var @ {}", var.frame_offset)?;
        }
        sst::ExprKind::BinOp(a, op, b) => {
            write!(w, "(")?;
            write_expr(w, a, depth)?;
            write!(w, ") {:?} (", op)?;
            write_expr(w, b, depth)?;
            write!(w, ")")?;
        }
        sst::ExprKind::Reference(expr) => {
            write!(w, "ref(")?;
            write_expr(w, expr, depth)?;
            write!(w, ")")?;
        }
        sst::ExprKind::Dereference(expr) => {
            write!(w, "deref(")?;
            write_expr(w, expr, depth)?;
            write!(w, ")")?;
        }
        sst::ExprKind::DerefAccess(expr, field) => {
            write!(w, "deref_member({}, {} into ", field.name, field.offset)?;
            write_expr(w, expr, depth)?;
            write!(w, ")")?;
        }
        sst::ExprKind::MemberAccess(expr, field) => {
            write!(w, "member({}, {} into ", field.name, field.offset)?;
            write_expr(w, expr, depth)?;
            write!(w, ")")?;
        }
    }

    Ok(())
}

fn write_stmt(w: &mut dyn Write, stmt: &sst::Statement, depth: u32) -> Result {
    match stmt {
        sst::Statement::If(cond, if_body, else_body) => {
            write!(w, "if ")?;
            write_expr(w, cond, depth)?;
            write_stmt(w, if_body, depth)?;
            write!(w, " else ")?;
            write_stmt(w, else_body, depth)?;
        }
        sst::Statement::Loop(body) => {
            write!(w, "loop ")?;
            write_stmt(w, body, depth)?;
        }
        sst::Statement::Return(Some(expr)) => {
            write!(w, "return ")?;
            write_expr(w, expr, depth)?;
            write!(w, ";")?;
        }
        sst::Statement::Return(None) => {
            write!(w, "return;")?;
        }
        sst::Statement::Break => {
            write!(w, "break;")?;
        }
        sst::Statement::Block(block) => write_block(w, block, depth)?,
        sst::Statement::Debugger => {
            write!(w, "debugger;")?;
        }
        sst::Statement::Expression(expr) => {
            write_expr(w, expr, depth)?;
            write!(w, ";")?;
        }
        sst::Statement::Empty => {
            write!(w, "_;")?;
        }
        sst::Statement::VarDecl(var, expr) => {
            write!(
                w,
                "decl {} @ {}/{} = ",
                var.typ.name, var.frame_offset, var.typ.size
            )?;
            write_expr(w, expr, depth)?;
            write!(w, ";")?;
        }
    }

    Ok(())
}

fn write_block(w: &mut dyn Write, body: &[sst::Statement], depth: u32) -> Result {
    writeln!(w, "{{")?;

    for stmt in body {
        indent(w, depth + 1)?;
        write_stmt(w, stmt, depth + 1)?;
        writeln!(w)?;
    }

    indent(w, depth)?;
    write!(w, "}}")
}

pub fn program(w: &mut dyn Write, prog: &sst::Program) -> Result {
    let mut first = true;
    for func in &prog.functions {
        if !first {
            writeln!(w)?;
        }
        first = false;

        write!(w, "func {}(", func.signature.name)?;
        let mut first = true;
        for field in &func.signature.params.fields {
            if !first {
                write!(w, ", ")?;
            }
            first = false;
            write!(w, "{}: {} @ {}", field.name, field.typ.name, field.offset)?;
        }
        write!(w, ") {} ", func.signature.ret.name)?;

        write_block(w, &func.body, 0)?;
        writeln!(w)?;
    }

    Ok(())
}
