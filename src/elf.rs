#![allow(non_snake_case)]

use std::io::Write;

use serde_derive::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct ElfFileHeader {
    pub Class: String,
    pub Data: String,
    pub Type: String,
    pub Machine: u32,
    pub Entry: usize,
}

#[derive(Serialize, Deserialize)]
pub struct ElfSection {
    pub Name: String,
    pub Type: String,
    pub Flags: Vec<String>,
    pub Address: usize,
    pub AddressAlign: usize,
    pub Content: String,
}

#[derive(Serialize, Deserialize)]
pub struct ElfSymbol {
    pub Name: String,
    pub Type: String,
    pub Section: String,
    pub Value: usize,
    pub Binding: Option<String>
}

#[derive(Serialize, Deserialize)]
pub struct ElfSectionRef {
    pub Section: String,
}

#[derive(Serialize, Deserialize)]
pub struct ElfProgramHeader {
    pub Type: String,
    pub Flags: Vec<String>,
    pub VAddr: usize,
    pub Align: usize,
    pub Sections: Vec<ElfSectionRef>,
}

#[derive(Serialize, Deserialize)]
pub struct ElfFile {
    pub FileHeader: ElfFileHeader,
    pub Symbols: Vec<ElfSymbol>,
    pub Sections: Vec<ElfSection>,
    pub ProgramHeaders: Vec<ElfProgramHeader>,
}

impl ElfFile {
    pub fn from_disk(file: &str) -> Self {
        let obj2yaml = if std::env::consts::OS == "macos" {
            // we are on an M1 mac, where homebrew lives in /opt/homebrew
            if std::env::consts::ARCH == "aarch64" {
                "/opt/homebrew/opt/llvm/bin/obj2yaml"
            } else {
                todo!("Mac OS on x86_64: homebrew path")
            }
        } else {
            // it's in PATH
            "obj2yaml"
        };
        let process = std::process::Command::new(obj2yaml)
            .args(vec![file])
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("obj2yaml failed");
        let mut rd = process.stdout.unwrap();
        serde_yaml::from_reader(&mut rd).unwrap()
    }
    pub fn to_disk(&self, file: &str) {
        let obj2yaml = if std::env::consts::OS == "macos" {
            // we are on an M1 mac, where homebrew lives in /opt/homebrew
            if std::env::consts::ARCH == "aarch64" {
                "/opt/homebrew/opt/llvm/bin/yaml2obj"
            } else {
                todo!("Mac OS on x86_64: homebrew path")
            }
        } else {
            // it's in PATH
            "obj2yaml"
        };
        let process = std::process::Command::new(obj2yaml)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("obj2yaml failed");
        let s = serde_yaml::to_string(self).unwrap().replacen("---", "--- !ELF", 1);
        write!(process.stdin.unwrap(), "{}", &s).unwrap();
        std::io::copy(
            &mut process.stdout.unwrap(),
            &mut std::fs::OpenOptions::new()
                .write(true)
                .create(true)
                .open(file)
                .unwrap(),
        )
        .unwrap();
    }
}
