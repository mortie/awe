mod analyzer;
mod backend;
mod parser;

use std::env;
use std::error::Error;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{self, Command};

use backend::Backend;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

pub static STDLIB: &str = include_str!("stdlib.awe");

struct TempFile {
    pub path: PathBuf,
    pub file: Option<fs::File>,
}

impl Drop for TempFile {
    fn drop(&mut self) {
        self.close();
        let _ = fs::remove_file(&self.path);
    }
}

impl TempFile {
    fn new(suffix: &str) -> io::Result<Self> {
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
                    return Ok(Self {
                        path,
                        file: Some(file),
                    });
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

    fn close(&mut self) {
        self.file.take();
    }
}

fn codegen<W: Write>(mut w: W, prog: &analyzer::sst::Program, backend: &Backend) -> Result<()> {
    writeln!(w, "// <PRELUDE>")?;
    write!(w, "{}", backend.prelude)?;
    writeln!(w, "// </PRELUDE>")?;
    writeln!(w)?;

    (backend.codegen)(&mut w, prog)?;
    Ok(())
}

fn compile(prog: &analyzer::sst::Program, backend: &Backend) -> Result<TempFile> {
    let temp = TempFile::new("s")?;
    let f = &temp.file;

    codegen(&mut f.as_ref().unwrap(), prog, backend)?;
    temp.file.as_ref().unwrap().sync_all()?;
    Ok(temp)
}

fn assemble(asm: TempFile) -> Result<TempFile> {
    let temp = TempFile::new("o")?;

    let mut child = Command::new("as")
        .arg("-o")
        .arg(&temp.path)
        .arg(&asm.path)
        .spawn()?;
    let status = child.wait()?;
    if !status.success() {
        return Err(format!("Assembler exited with {}", status).into());
    }

    Ok(temp)
}

fn link(out_path: &Path, obj: TempFile, backend: &Backend) -> Result<()> {
    let mut child = (backend.ld_command)(out_path, &obj.path).spawn()?;
    let status = child.wait()?;
    if !status.success() {
        return Err(format!("Linker exited with {}", status).into());
    }

    Ok(())
}

fn run() -> Result<()> {
    let mut codegen_only = false;
    let mut parse_only = false;
    let mut analyze_only = false;
    let mut run_only = false;
    let mut target: Option<String> = None;
    let mut in_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut args = env::args();
    args.next(); // argv[0]

    while let Some(arg) = args.next() {
        if arg == "-s" {
            codegen_only = true;
        } else if arg == "--parse" {
            parse_only = true;
        } else if arg == "--analyze" {
            analyze_only = true;
        } else if arg == "-r" || arg == "--run" {
            run_only = true;
            if in_path.is_some() {
                break;
            }
        } else if arg == "-o" {
            out_path = args.next();
            if out_path.is_none() {
                return Err("-o requires an argument".into());
            }
        } else if arg == "-t" || arg == "--target" {
            target = args.next();
            if target.is_none() {
                return Err("--target requires an argument".into());
            }
        } else if arg.starts_with("-") {
            eprintln!("Unknown option: {}", arg);
            process::exit(1);
        } else if in_path.is_none() {
            in_path = Some(arg);
            if run_only {
                break;
            }
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

    let mut prog = parser::parse::program_str(STDLIB)?;
    prog.append(&mut parser::parse::program_str(&fs::read_to_string(&in_path)?)?);
    if parse_only {
        println!("AST: {:#?}", prog);
        process::exit(0);
    }

    let prog = analyzer::analyze::program(&prog)?;
    if analyze_only {
        analyzer::display::program(&mut io::stdout(), &prog)?;
        return Ok(());
    }

    let target = match target {
        Some(target) => target,
        None => format!("{}-{}", env::consts::OS, env::consts::ARCH),
    };

    let Some(backend) = backend::get_backend(&target) else {
        return Err(format!("No backend for target '{target}'").into());
    };

    if codegen_only {
        match out_path {
            Some(path) => {
                let mut opts = fs::OpenOptions::new();
                opts.write(true).truncate(true).create(true);
                let mut file = opts.open(path)?;

                codegen(&mut file, &prog, &backend)?;
            }
            None => codegen(&mut io::stdout(), &prog, &backend)?,
        };

        return Ok(());
    }

    let out_path =
        out_path.unwrap_or_else(|| in_path.strip_suffix(".awe").unwrap_or("a.out").to_owned());

    let asm_file = compile(&prog, &backend)?;
    let obj_file = assemble(asm_file)?;

    if run_only {
        let exe_file = TempFile::new("bin")?;
        link(&exe_file.path, obj_file, &backend)?;

        let mut cmd = Command::new(&exe_file.path);
        for arg in args {
            cmd.arg(arg);
        }

        let mut child = cmd.spawn()?;
        let status = child.wait()?;
        if !status.success() {
            return Err(format!("Program exited with {}", status).into());
        }

        return Ok(());
    }

    eprintln!("Linking '{}'...", out_path);
    link(Path::new(&out_path), obj_file, &backend)?;
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("{}", err);
        process::exit(1);
    }
}
