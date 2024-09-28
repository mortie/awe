use std::io::Result;
use std::io::Write;

use super::common;
use crate::analyzer::sst;

fn gen_extern_func<W: Write>(w: &mut W, func: &sst::FuncSignature) -> Result<()> {
    common::gen_signature_comment(w, func)?;
    write!(w, ".extern {}\n\n", func.name)?;
    Ok(())
}

fn gen_func<W: Write>(w: &mut W, func: &sst::Function) -> Result<()> {
    common::gen_signature_comment(w, &func.signature)?;
    write!(w, "awe__{}:\n", func.signature.name)?;

    write!(w, "\n")?;
    Ok(())
}

pub fn codegen<W: Write>(w: &mut W, prog: &sst::Program) -> Result<()> {
    for func in &prog.extern_funcs {
        gen_extern_func(w, func)?;
    }

    for func in &prog.functions {
        gen_func(w, func)?;
    }

    Ok(())
}
