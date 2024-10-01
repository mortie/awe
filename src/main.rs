mod analyzer;
mod backend;
mod parser;

use std::env;
use std::error::Error;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{self, Command};

fn temp_file(suffix: &str) -> io::Result<(PathBuf, fs::File)> {
    let temp_dir = env::temp_dir();

    let mut num = 0;
    loop {
        let mut path = temp_dir.clone();
        path.push(format!("awe-output.{}.{}", num, suffix));

        let res = fs::OpenOptions::new()
            .read(false)
            .write(true)
            .create_new(true)
            .open(&path);
        match res {
            Ok(file) => {
                return Ok((path, file));
            }

            Err(err) => {
                if err.kind() != io::ErrorKind::AlreadyExists {
                    return Err(err);
                }

            }
        };

        num += 1;
    }
}

fn codegen<W: Write>(w: &mut W, prog: &analyzer::sst::Program) -> Result<(), Box<dyn Error>> {
    write!(w, "// <PRELUDE>\n")?;
    write!(w, "{}", backend::preludes::AARCH64_DARWIN)?;
    write!(w, "// <PRELUDE>\n")?;
    write!(w, "\n")?;

    if let Err(err) = backend::aarch64::codegen(w, prog) {
        eprintln!("{:?}", err);
    }

    Ok(())
}

fn compile(prog: &analyzer::sst::Program) -> io::Result<PathBuf> {
    let (path, mut f) = temp_file("s")?;
    eprintln!("Compiling...");

    if let Err(err) = codegen(&mut f, prog) {
        eprintln!("{}", err);
        let _ = fs::remove_file(path);
        process::exit(1);
    }

    if let Err(err) = f.sync_all() {
        let _ = fs::remove_file(path);
        return Err(err);
    }

    Ok(path)
}

fn assemble(asm_path: &Path) -> io::Result<PathBuf> {
    let (obj_path, _) = temp_file("o")?;
    eprintln!("Assembling...");

    let res = Command::new("as").arg("-o").arg(&obj_path).arg(asm_path).spawn();
    let mut child = match res {
        Ok(child) => child,

        Err(err) => {
            let _ = fs::remove_file(asm_path);
            let _ = fs::remove_file(obj_path);
            return Err(err);
        }
    };

    let status = match child.wait() {
        Ok(status) => status,
        Err(err) => {
            let _ = fs::remove_file(asm_path);
            let _ = fs::remove_file(obj_path);
            return Err(err);
        }
    };

    if !status.success() {
        let _ = fs::remove_file(asm_path);
        let _ = fs::remove_file(obj_path);
        eprintln!("Assembler exited with error status {}", status);
        process::exit(1);
    }

    let _ = fs::remove_file(asm_path);
    Ok(obj_path)
}

fn link(obj_path: &Path, out_path: &Path) -> io::Result<()> {
    eprintln!("Linking to '{}'...", out_path.to_string_lossy());

    let res = Command::new("ld").arg("-o").arg(&out_path).arg(obj_path).spawn();
    let mut child = match res {
        Ok(child) => child,

        Err(err) => {
            let _ = fs::remove_file(obj_path);
            let _ = fs::remove_file(out_path);
            return Err(err);
        }
    };

    let status = match child.wait() {
        Ok(status) => status,
        Err(err) => {
            let _ = fs::remove_file(obj_path);
            let _ = fs::remove_file(out_path);
            return Err(err);
        }
    };

    if !status.success() {
        let _ = fs::remove_file(obj_path);
        let _ = fs::remove_file(out_path);
        eprintln!("Linker exited with error status {}", status);
        process::exit(1);
    }

    let _ = fs::remove_file(obj_path);
    Ok(())
}

fn main() {
    let mut codegen_only = false;
    let mut in_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut args = env::args();
    args.next(); // argv[0]

    while let Some(arg) = args.next() {
        if arg == "-s" {
            codegen_only = true;
        } else if arg == "-o" {
            out_path = args.next();
            if out_path.is_none() {
                eprintln!("-o requires an argument");
                process::exit(1);
            }
        } else if arg.starts_with("-") {
            eprintln!("Unknown option: {}", arg);
            process::exit(1);
        } else if in_path.is_none() {
            in_path = Some(arg);
        } else {
            eprintln!("Unexpected argument: {}", arg);
            process::exit(1);
        }
    }

    let Some(in_path) = in_path else {
        eprintln!("Expected input path");
        process::exit(1);
    };

    // Automatically only generate assembly code if outputting to a .s
    if let Some(out_path) = &out_path {
        if out_path.ends_with(".s") {
            codegen_only = true;
        }
    }

    let str = fs::read_to_string(&in_path).unwrap();
    let mut reader = parser::reader::Reader::new(str.as_bytes(), in_path.clone());

    let prog = match parser::parse::program(&mut reader) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{}: {}", in_path, err);
            process::exit(1);
        }
    };

    let prog = match analyzer::analyze::program(&prog) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{:?}", err);
            process::exit(1);
        }
    };

    if codegen_only {
        let err = match out_path {
            Some(path) => {
                let mut opts = fs::OpenOptions::new();
                opts.write(true).truncate(true);
                let mut file = match opts.open(path) {
                    Ok(f) => f,
                    Err(err) => {
                        eprintln!("{}", err);
                        process::exit(1);
                    }
                };

                codegen(&mut file, &prog)
            }
            None => codegen(&mut io::stdout(), &prog),
        };

        if let Err(err) = err {
            eprintln!("{}", err);
            process::exit(1);
        }

        process::exit(0);
    }

    let out_path = out_path.unwrap_or_else(||
        in_path.strip_suffix(".awe").unwrap_or("a.out").to_owned());

    let res = (|| -> io::Result<()> {
        let asm_path = compile(&prog)?;
        let obj_path = assemble(&asm_path)?;
        link(&obj_path, &Path::new(&out_path))?;
        Ok(())
    })();

    if let Err(err) = res {
        eprintln!("{}", err);
        process::exit(1);
    }
}
