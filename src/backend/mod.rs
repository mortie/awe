use crate::analyzer::sst;
use std::io::Write;

pub mod aarch64;
pub mod preludes;

mod common;

type CodegenFn<W> = dyn Fn(W, &sst::Program) -> common::Result<()>;

pub struct Backend<W: Write> {
    pub prelude: &'static str,
    pub codegen: Box<CodegenFn<W>>,
}

pub fn get_backend<W: Write>(target: &str) -> Option<Backend<W>> {
    match target {
        "macos-aarch64" => Some(Backend {
            prelude: preludes::DARWIN_AARCH64,
            codegen: Box::new(|w: W, p| aarch64::codegen(w, p)),
        }),

        "linux-aarch64" => Some(Backend {
            prelude: preludes::LINUX_AARCH64,
            codegen: Box::new(|w: W, p| aarch64::codegen(w, p)),
        }),

        _ => None,
    }
}
