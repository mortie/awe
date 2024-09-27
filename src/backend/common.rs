use std::io::Write;
use std::io::Result;

use crate::analyzer::sst;

pub fn gen_signature_comment<W: Write>(w: &mut W, sig: &sst::FuncSignature) -> Result<()> {
    write!(w, "// func {}(", sig.name)?;

    let mut first = true;
    for param in &sig.params.fields {
        if !first {
            write!(w, ", ")?;
        }
        first = false;

        write!(w, "{}: {}", param.name, param.typ.name)?;
    }

    write!(w, ") {}\n", sig.ret.name)?;
    Ok(())
}
