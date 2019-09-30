use crate::bi_types::{TypeChecker, TypeError};
use crate::codegen::{Codegen, CodegenError, Lowering};
use crate::expr::{Declaration, ValueDeclaration};
use crate::grammar;
use crate::term::{EvalError, Term};
use crate::token;
use crate::types;
use crate::wasm;

#[derive(Debug, PartialEq, Eq)]
pub enum Backend {
    Term,
    Wasm,
}

#[derive(Debug)]
pub enum PipelineError {
    ParseError(String),
    TypeError(TypeError),
    NewTypeError(types::TypeError),
    EvalError(EvalError),
    CodegenError(CodegenError),
    WasmError(String),
}

pub fn run_program(input: &str, backend: Backend) -> Result<String, PipelineError> {
    let lexer = token::Lexer::new(&input);
    let prog = grammar::ProgramParser::new()
        .parse(lexer)
        .map_err(|err| PipelineError::ParseError(format!("Parse failure: {:?}", err)))?;
    // For when running without a type checker
    let tys: Vec<(Declaration<String>, u32)> = prog.into_iter().map(|d| (d, 42)).collect();
    // For when running the bidirectional type checker
//     let mut type_checker = TypeChecker::new();
//     let tys = type_checker
//         .synth_prog(prog.clone())
//         .map_err(PipelineError::TypeError)?;

    // For when running the unification based type checker
//    let mut type_checker = types::TypeChecker::new();
//    let tys = type_checker
//        .infer_prog(prog)
//        .map_err(PipelineError::NewTypeError)?;


    for (decl, ty) in tys.iter() {
        if let Declaration::Value(vd) = decl {
            info!("{} : {}", vd.name, ty)
        }
    }
    match backend {
        Backend::Term => {
            let res = Term::eval_prog(tys.into_iter().map(|(e, _)| e).collect())
                .map_err(PipelineError::EvalError)?;
            Ok(format!("{}", res))
        }
        Backend::Wasm => {
            let lowered = Lowering::new()
                .lower(tys)
                .map_err(PipelineError::CodegenError)?;
            let prog = Codegen::new().codegen(lowered);
            println!("{}", wasm::pretty_wat(&prog));
            let res =
                wasm::run_wasm(prog).map_err(|err| PipelineError::WasmError(format!("{}", err)))?;
            Ok(format!("{:?}", res))
        }
    }
}
