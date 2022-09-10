// Copyright (C) 2022 Lior Stern.
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

fn find_forth_runtime_sources() -> Vec<std::path::PathBuf> {
    let project_root_directory = std::env::var_os("CARGO_MANIFEST_DIR").unwrap();
    let project_root_directory = std::path::Path::new(&project_root_directory);

    let mut forth_runtime_paths = vec![];
    for entry in project_root_directory.join("src").read_dir().unwrap() {
        if let Ok(entry) = entry {
            let path = entry.path();
            if path.extension().unwrap() == "fth" {
                forth_runtime_paths.push(path);
            }
        }
    }

    return forth_runtime_paths;
}

fn forth_runtime_priority(path: &std::path::PathBuf) -> usize {
    let prefix = path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .split('_')
        .nth(0)
        .unwrap();
    return usize::from_str_radix(prefix, 10).unwrap();
}

fn concat_files(paths: &[std::path::PathBuf]) -> String {
    let mut result = String::new();

    for path in paths {
        let content = std::fs::read(path).unwrap();
        let content = String::from_utf8(content).unwrap();
        result.push_str(&content);
    }

    return result;
}

fn main() {
    let mut fth_files = find_forth_runtime_sources();
    fth_files.sort_by(|a, b| forth_runtime_priority(a).cmp(&forth_runtime_priority(b)));

    for path in &fth_files {
        println!("cargo:rerun-if-changed={}", path.to_str().unwrap());
    }

    let forth_runtime = concat_files(&fth_files);

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let runtime_path = std::path::Path::new(&out_dir).join("runtime.fth");
    std::fs::write(&runtime_path, forth_runtime).unwrap();
    println!("cargo:rerun-if-changed={}", runtime_path.to_str().unwrap());

    println!("cargo:rerun-if-changed=build.rs");
}
