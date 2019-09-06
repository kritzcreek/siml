extern crate siml;
use siml::{bi_types, codegen::Codegen, grammar, token, wasm};
use std::fs::{self, DirEntry};
use std::path::Path;

#[test]
fn test_passing() {
    for entry in fs::read_dir("tests/passing").expect("Failed to read passing dir") {
        let path = entry.unwrap().path();
        if path.is_file() {
            test_wasm_program(fs::read_to_string(path).unwrap())
        }
    }
}

fn test_wasm_program(input: String) {
    let lexer = token::Lexer::new(&input);
    let res = grammar::ProgramParser::new().parse(lexer);
    match res {
        Err(err) => panic!("Parse failure: {:?}", err),
        Ok(prog) => {
            let mut type_checker = bi_types::TypeChecker::new();
            match type_checker.synth_prog(prog.clone()) {
                Err(err) => {
                    panic!("{}", err.print());
                }
                Ok(tys) => {
                    let prog = Codegen::new().codegen(&tys);
                    match wasm::run_wasm(prog) {
                        Ok(res) => {}
                        Err(err) => panic!("{}", err),
                    }
                }
            };
        }
    }
}
