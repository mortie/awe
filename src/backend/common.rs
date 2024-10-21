use std::error::Error;
use std::fmt::{self, Display};
use std::io::{self, Write};
use std::rc::Rc;

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

    writeln!(w, ") {}", sig.ret.name)?;
    Ok(())
}

fn is_legal_name_char(ch: u8) -> bool {
    (ch >= b'a' && ch <= b'z') ||
        (ch >= b'A' && ch <= b'Z') ||
        (ch >= b'0' && ch <= b'9') ||
        ch == b'_'
}

fn name_is_legal(name: &str) -> bool {
    if name.starts_with("_") {
        return false;
    }

    for ch in name.bytes() {
        if !is_legal_name_char(ch) {
            return false;
        }
    }

    return true;
}

pub fn mangle_name(name: &Rc<String>) -> Rc<String> {
    if name_is_legal(&name) {
        return name.clone();
    }

    let mut mangled = String::with_capacity(name.len() + 16);
    mangled.push_str("_Z");
    for ch in name.bytes() {
        if ch == b'_' {
            mangled.push_str("_Z");
        } else if ch == b':' {
            mangled.push_str("_X");
        } else if ch == b',' {
            mangled.push_str("_C");
        } else if ch == b'[' {
            mangled.push_str("_A");
        } else if ch == b'[' {
            mangled.push_str("_B");
        } else if !is_legal_name_char(ch) {
            panic!("Unexpected character in identifier: '{}'", ch as char);
        } else {
            mangled.push(ch as char);
        }
    }

    Rc::new(mangled)
}

#[derive(Clone)]
pub struct Loop {
    pub break_label: usize,
    pub continue_label: usize,
}

pub struct TempVar {
    typ: Rc<sst::Type>,
    stack_base: usize,
    frame_offset: usize,
}

pub struct Frame<'a, 'b> {
    pub w: &'a mut dyn Write,
    pub func: &'b sst::Function,
    pub symbol_name: Rc<String>,
    stack_size: usize,
    temps: Vec<TempVar>,
    sentinel: Rc<sst::Type>,
    next_label: usize,
    loops: Vec<Loop>,
}

impl<'a, 'b> Frame<'a, 'b> {
    pub fn new(w: &'a mut dyn Write, func: &'b sst::Function, sentinel: Rc<sst::Type>) -> Self {
        let stack_size = func.stack_size;
        let symbol_name = mangle_name(&func.signature.name);
        Self {
            w,
            func,
            symbol_name,
            stack_size,
            temps: Vec::new(),
            sentinel,
            next_label: 0,
            loops: Vec::new(),
        }
    }

    pub fn push_temp(&mut self, typ: Rc<sst::Type>) -> sst::LocalVar {
        let stack_base = self.stack_size;
        while typ.align > 0 && self.stack_size % typ.align != 0 {
            self.stack_size += 1;
        }

        let frame_offset = self.stack_size;
        self.stack_size += typ.size;

        self.temps.push(TempVar {
            typ: typ.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar {
            typ,
            frame_offset: frame_offset as isize,
        }
    }

    pub fn push_align(&mut self, align: usize) -> sst::LocalVar {
        let stack_base = self.stack_size;
        while align > 0 && self.stack_size % align != 0 {
            self.stack_size += 1;
        }

        let frame_offset = self.stack_size;

        self.temps.push(TempVar {
            typ: self.sentinel.clone(),
            stack_base,
            frame_offset,
        });

        sst::LocalVar {
            typ: self.sentinel.clone(),
            frame_offset: frame_offset as isize,
        }
    }

    pub fn pop_temp(&mut self, var: sst::LocalVar) {
        // We want to ensure that the passed-in variable is the most recent
        // variable returned from push_temp().
        // We don't keep around a reference to the actual LocalVar
        // that was returned by push_temp,
        // so we do a series of sanity checks instead.
        // If they are violated, that's a serious programming error,
        // so we just panic.

        let Some(last) = self.temps.pop() else {
            panic!("pop_temp called with an empty temporary stack!");
        };

        if !Rc::ptr_eq(&last.typ, &var.typ) {
            panic!(
                "pop_temp called with wrong type: expected {}, got {}",
                last.typ.name, var.typ.name
            );
        }

        if last.frame_offset as isize != var.frame_offset {
            panic!(
                "pop_temp called with wrong frame_offset: expected {}, got {}",
                last.frame_offset, var.frame_offset
            );
        }

        self.stack_size = last.stack_base;
    }

    pub fn maybe_pop_temp(&mut self, mut var: MaybeTemp) {
        if let Some(container) = var.container.take() {
            self.maybe_pop_temp(*container);
        }

        if let MaybeTempKind::Temp(temp) = var.kind {
            self.pop_temp(temp);
        }
    }

    pub fn label(&mut self) -> usize {
        let label = self.next_label;
        self.next_label += 1;
        label
    }

    pub fn push_loop(&mut self) -> Loop {
        let labels = Loop {
            break_label: self.label(),
            continue_label: self.label(),
        };
        self.loops.push(labels.clone());
        labels
    }

    pub fn top_loop(&self) -> Option<Loop> {
        if let Some(labels) = self.loops.first() {
            return Some(labels.clone());
        }

        None
    }

    pub fn pop_loop(&mut self) {
        self.loops.pop();
    }
}

pub enum MaybeTempKind {
    Temp(sst::LocalVar),
    NonTemp(sst::LocalVar),
}

pub struct MaybeTemp {
    pub kind: MaybeTempKind,
    container: Option<Box<MaybeTemp>>,
}

impl MaybeTemp {
    pub fn temp(var: sst::LocalVar) -> Self {
        Self {
            kind: MaybeTempKind::Temp(var),
            container: None,
        }
    }

    pub fn non_temp(var: sst::LocalVar) -> Self {
        Self {
            kind: MaybeTempKind::NonTemp(var),
            container: None,
        }
    }

    pub fn with_container(self, container: MaybeTemp) -> Self {
        if self.container.is_some() {
            panic!("with_container can only be called on a MaybeTemp without a container");
        }

        Self {
            kind: self.kind,
            container: Some(Box::new(container)),
        }
    }

    pub fn var(&self) -> &sst::LocalVar {
        match &self.kind {
            MaybeTempKind::Temp(var) => var,
            MaybeTempKind::NonTemp(var) => var,
        }
    }

    pub fn is_temp(&self) -> bool {
        match self.kind {
            MaybeTempKind::Temp(..) => true,
            _ => false,
        }
    }
}
