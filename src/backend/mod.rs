use crate::analyzer::sst;
use std::io::Write;

pub mod aarch64;
pub mod preludes;

mod common;

pub struct Backend {
    pub prelude: &'static str,
    pub codegen: fn(&mut dyn Write, &sst::Program) -> common::Result<()>,
}

pub fn get_backend(target: &str) -> Option<Backend> {
    match target {
        "macos-aarch64" => Some(Backend {
            prelude: preludes::DARWIN_AARCH64,
            codegen: aarch64::codegen,
        }),

        "linux-aarch64" => Some(Backend {
            prelude: preludes::LINUX_AARCH64,
            codegen: aarch64::codegen,
        }),

        _ => None,
    }
}
