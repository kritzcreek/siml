extern crate siml;
use siml::pipeline::{run_program, Backend};
use std::fs;
use std::path::PathBuf;

fn backend_from_path(path: &PathBuf) -> Backend {
    if path
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .ends_with("wasm")
    {
        Backend::Wasm
    } else {
        Backend::Term
    }
}

#[test]
fn test_passing() {
    for entry in fs::read_dir("tests/passing").expect("Failed to read passing dir") {
        let path = entry.unwrap().path();
        if path.is_file() {
            let backend = backend_from_path(&path);
            let res = run_program(&fs::read_to_string(path.clone()).unwrap(), backend).unwrap();
            println!("Running: {} => {}", path.display(), res);
        }
    }
}

#[test]
fn test_failing() {
    for entry in fs::read_dir("tests/failing").expect("Failed to read failing dir") {
        let path = entry.unwrap().path();
        if path.is_file() {
            let backend = backend_from_path(&path);
            if !run_program(&fs::read_to_string(path.clone()).unwrap(), backend).is_err() {
                println!("{} failed to fail", path.display());
                assert!(false)
            }
        }
    }
}
