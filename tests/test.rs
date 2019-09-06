extern crate siml;
use siml::{bi_types, codegen::Codegen, grammar, term::Term, token, wasm};
use std::fs;
use std::path::PathBuf;

enum Backend {
    Term,
    Wasm,
}

impl Backend {
    pub fn from_path(path: &PathBuf) -> Backend {
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
}

#[test]
fn test_passing() {
    for entry in fs::read_dir("tests/passing").expect("Failed to read passing dir") {
        let path = entry.unwrap().path();
        if path.is_file() {
            let backend = Backend::from_path(&path);
            test_program(fs::read_to_string(path).unwrap(), backend).unwrap()
        }
    }
}

#[test]
fn test_failing() {
    for entry in fs::read_dir("tests/failing").expect("Failed to read failing dir") {
        let path = entry.unwrap().path();
        if path.is_file() {
            let backend = Backend::from_path(&path);
            if !test_program(fs::read_to_string(path.clone()).unwrap(), backend).is_err() {
                println!("{} failed to fail", path.display());
                assert!(false)
            }
        }
    }
}

fn test_program(input: String, backend: Backend) -> Result<(), String> {
    let lexer = token::Lexer::new(&input);
    let res = grammar::ProgramParser::new().parse(lexer);
    match res {
        Err(err) => Err(format!("Parse failure: {:?}", err)),
        Ok(prog) => {
            let mut type_checker = bi_types::TypeChecker::new();
            match type_checker.synth_prog(prog.clone()) {
                Err(err) => Err(format!("Type error: {}", err.print())),
                Ok(tys) => match backend {
                    Backend::Term => {
                        match Term::eval_prog(tys.into_iter().map(|(e, _)| e).collect()) {
                            Ok(_) => Ok(()),
                            Err(err) => Err(format!("{}", err)),
                        }
                    }
                    Backend::Wasm => match Codegen::new().codegen(&tys) {
                        Err(err) => Err(format!("Codegen error: {}", err)),
                        Ok(prog) => match wasm::run_wasm(prog) {
                            Ok(_) => Ok(()),
                            Err(err) => Err(format!("{}", err)),
                        },
                    },
                },
            }
        }
    }
}
