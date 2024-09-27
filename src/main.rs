mod parser;
mod analyzer;
mod backend;

use std::{env, fs, io};

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
            return;
        }
    };

    let prog = match analyzer::analyze::program(&prog) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{:?}", err);
            return;
        }
    };

    if let Err(err) = backend::aarch64::codegen(&mut io::stdout(), &prog) {
        eprintln!("{:?}", err);
    }
}
