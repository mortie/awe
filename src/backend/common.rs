use std::error::Error;
use std::fmt::{self, Display};
use std::io::{self, Write};

use crate::analyzer::sst;

#[derive(Debug)]
pub enum CodegenError {
    IOError(io::Error),
    SizeMismatch(usize, usize),
    InvalidBreak,
    ReferenceToTemporary,

    // Unimplemented is for code that's a work in progress.
    // Most of the time, nothing which uses Unimplemented will be committed,
    // so it should always be allowed to be unused.
    #[allow(dead_code)]
    Unimplemented,
}

impl Error for CodegenError {}

impl From<io::Error> for CodegenError {
    fn from(err: io::Error) -> Self {
        Self::IOError(err)
    }
}

impl Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CodegenError::*;
        match self {
            IOError(err) => write!(f, "IO error: {err}"),
            SizeMismatch(expected, got) => {
                write!(f, "Size mismatch: Expected {expected}, got {got}")
            }
            InvalidBreak => write!(f, "Break outside of loop"),
            ReferenceToTemporary => write!(f, "Reference to temporary"),

            // Unimplemented is for code that's a work in progress.
            // Most of the time, nothing which uses Unimplemented will be committed,
            // so it should always be allowed to be unused.
            #[allow(dead_code)]
            Unimplemented => write!(f, "Unimplemented feature"),
        }
    }
}

pub type Result<T> = std::result::Result<T, CodegenError>;

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
