// Copyright (C) 2024 Lior Stern.
//
// This file is part of liorforth.
// liorforth is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or any later version.
//
// liorforth is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// liorforth. If not, see <https://www.gnu.org/licenses/>.

fn project_root_directory() -> std::path::PathBuf {
    std::path::Path::new(&std::env::var_os("CARGO_MANIFEST_DIR").unwrap()).into()
}

fn forth_sources_directory() -> std::path::PathBuf {
    project_root_directory().join("fth")
}

fn forth_runtime_priority(path: &std::path::PathBuf) -> usize {
    path.file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .split('_')
        .next()
        .unwrap()
        .parse::<usize>()
        .unwrap()
}

fn concat_files(paths: &[std::path::PathBuf]) -> String {
    let mut result = String::new();

    for path in paths {
        let content = std::fs::read(path).unwrap();
        let content = String::from_utf8(content).unwrap();
        result.push_str(&content);
    }

    result
}

fn main() {
    println!(
        "cargo:rerun-if-changed={}",
        forth_sources_directory().to_str().unwrap()
    );

    let mut fth_files: Vec<std::path::PathBuf> = forth_sources_directory()
        .read_dir()
        .unwrap()
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.extension().unwrap() == "fth")
        .collect();
    fth_files.sort_by_key(forth_runtime_priority);
    let fth_files = fth_files;

    let forth_runtime = concat_files(&fth_files);

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let runtime_path = std::path::Path::new(&out_dir).join("runtime.fth");
    std::fs::write(&runtime_path, forth_runtime).unwrap();
    println!("cargo:rerun-if-changed={}", runtime_path.to_str().unwrap());

    println!("cargo:rerun-if-changed=build.rs");
}
