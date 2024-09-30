mod analyzer;
mod backend;
mod parser;

use std::env;
use std::error::Error;
use std::fs;
use std::io::{self, Write};
use std::process::exit;

fn codegen<W: Write>(w: &mut W, prog: &analyzer::sst::Program) -> Result<(), Box<dyn Error>> {
    write!(w, "// <PRELUDE>\n")?;
    write!(w, "{}", backend::preludes::AARCH64_DARWIN)?;
    write!(w, "// <PRELUDE>\n")?;
    write!(w, "\n")?;

    if let Err(err) = backend::aarch64::codegen(&mut io::stdout(), prog) {
        eprintln!("{:?}", err);
    }

    Ok(())
}

fn main() {
    let mut args = env::args();
    args.next(); // argv[0]

    let fname = args.next().unwrap();
    let str = fs::read_to_string(&fname).unwrap();
    let mut reader = parser::reader::Reader::new(str.as_bytes(), fname.clone());

    let prog = match parser::parse::program(&mut reader) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{}: {}", fname, err);
            exit(1);
        }
    };

    let prog = match analyzer::analyze::program(&prog) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{:?}", err);
            exit(1);
        }
    };

    match codegen(&mut io::stdout(), &prog) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("{}", err);
            exit(1);
        }
    }
}
