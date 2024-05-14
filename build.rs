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

fn find_forth_runtime_sources() -> Vec<std::path::PathBuf> {
    let project_root_directory = std::env::var_os("CARGO_MANIFEST_DIR").unwrap();
    let project_root_directory = std::path::Path::new(&project_root_directory);

    let mut forth_runtime_paths = vec![];
    for entry in project_root_directory
        .join("src")
        .read_dir()
        .unwrap()
        .flatten()
    {
        let path = entry.path();
        if path.extension().unwrap() == "fth" {
            forth_runtime_paths.push(path);
        }
    }

    forth_runtime_paths
}

fn forth_runtime_priority(path: &std::path::Path) -> usize {
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

fn remove_empty_lines(forth_code: String) -> String {
    forth_code
        .lines()
        .filter(|line| !line.is_empty())
        .collect::<Vec<&str>>()
        .join("\n")
}

fn remove_backslash_comments(forth_code: String) -> String {
    forth_code
        .lines()
        .map(|line| line.split("\\ ").next().unwrap())
        .collect::<Vec<&str>>()
        .join("\n")
}

fn remove_leading_and_trailing_whitespace(forth_code: String) -> String {
    forth_code
        .lines()
        .map(|line| line.trim())
        .collect::<Vec<&str>>()
        .join("\n")
}

fn minimize_source(forth_code: String) -> String {
    const TRANSFORMERS: &[fn(String) -> String] = &[
        remove_backslash_comments,
        remove_leading_and_trailing_whitespace,
        remove_empty_lines,
    ];

    // TODO: Use fancy functional thing instead of a loop
    let mut minimized_code = forth_code;
    for transform in TRANSFORMERS {
        minimized_code = transform(minimized_code)
    }
    minimized_code
}

fn main() {
    // TODO: Re-run when new fth files are added to the project

    let mut fth_files = find_forth_runtime_sources();
    fth_files.sort_by_key(|a| forth_runtime_priority(a));

    for path in &fth_files {
        println!("cargo:rerun-if-changed={}", path.to_str().unwrap());
    }

    let mut forth_runtime = concat_files(&fth_files);

    // TODO: Only in non debug targets
    forth_runtime = minimize_source(forth_runtime);

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let runtime_path = std::path::Path::new(&out_dir).join("runtime.fth");
    std::fs::write(&runtime_path, forth_runtime).unwrap();
    println!("cargo:rerun-if-changed={}", runtime_path.to_str().unwrap());

    println!("cargo:rerun-if-changed=build.rs");
}
