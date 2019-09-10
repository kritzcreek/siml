use crate::bi_types::{TypeChecker, TypeError};
use crate::codegen::{Codegen, CodegenError, IRLowering};
use crate::grammar;
use crate::term::{EvalError, Term};
use crate::token;
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
    EvalError(EvalError),
    CodegenError(CodegenError),
    WasmError(String),
}

pub fn run_program(input: &str, backend: Backend) -> Result<String, PipelineError> {
    let lexer = token::Lexer::new(&input);
    let prog = grammar::ProgramParser::new()
        .parse(lexer)
        .map_err(|err| PipelineError::ParseError(format!("Parse failure: {:?}", err)))?;
    let mut type_checker = TypeChecker::new();
    let tys = type_checker
        .synth_prog(prog.clone())
        .map_err(PipelineError::TypeError)?;
    match backend {
        Backend::Term => {
            let res = Term::eval_prog(tys.into_iter().map(|(e, _)| e).collect())
                .map_err(PipelineError::EvalError)?;
            Ok(format!("{}", res))
        }
        Backend::Wasm => {
            let lowered = IRLowering::new()
                .lower(tys)
                .map_err(PipelineError::CodegenError)?;
            let prog = Codegen::new().codegen_ir(lowered);
            println!("{}", prog);
            let res =
                wasm::run_wasm(prog).map_err(|err| PipelineError::WasmError(format!("{}", err)))?;
            Ok(format!("{:?}", res))
        }
    }
}
