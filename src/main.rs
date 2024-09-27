mod parser;
mod analyzer;

use std::{env, fs};

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
    println!("Program: {:?}", prog);

    println!();

    if let Err(err) = analyzer::analyze::program(&prog) {
        eprintln!("{:?}", err);
    };
}
