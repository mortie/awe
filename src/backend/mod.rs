use crate::analyzer::sst;
use std::{io::Write, path::Path, process::Command};

pub mod aarch64;
pub mod preludes;

mod common;

pub struct Backend {
    pub prelude: &'static str,
    pub codegen: fn(&mut dyn Write, &sst::Program) -> common::Result<()>,
    pub ld_command: fn(out_path: &Path, obj_path: &Path) -> Command,
}

pub fn get_backend(target: &str) -> Option<Backend> {
    match target {
        "macos-aarch64" => Some(Backend {
            prelude: preludes::DARWIN_AARCH64,
            codegen: aarch64::codegen,
            ld_command: |out_path, obj_path| {
                let mut cmd = Command::new("ld");
                cmd.arg("-L");
                cmd.arg("/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib");
                cmd.arg("-lSystem");
                cmd.arg("-o");
                cmd.arg(out_path);
                cmd.arg(obj_path);
                return cmd;
            },
        }),

        "linux-aarch64" => Some(Backend {
            prelude: preludes::LINUX_AARCH64,
            codegen: aarch64::codegen,
            ld_command: |out_path, obj_path| {
                let mut cmd = Command::new("ld");
                cmd.arg("-o");
                cmd.arg(out_path);
                cmd.arg(obj_path);
                return cmd;
            },
        }),

        _ => None,
    }
}
