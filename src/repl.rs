use crate::bi_types;
use crate::expr::ParserExpr;
use crate::grammar;
use crate::term;
use crate::term::Term;
use crate::token;
use crate::wasm;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn print_bi_ty_res(ty_res: Result<bi_types::Type, bi_types::TypeError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => format!("{}", ty),
    }
}

fn print_eval_res(res: Result<term::Term, term::EvalError>) -> String {
    match res {
        Err(err) => err.print(),
        Ok(term) => term.print(),
    }
}

pub fn run_expr(expr: ParserExpr) {
    info!("Expr:\n{}", expr);
    let mut type_checker = bi_types::TypeChecker::new();
    let ty_res = type_checker.synth(&expr);
    info!("BiInferred: {}", print_bi_ty_res(ty_res));
    // TODO Either restore eval_expr, or make this into an eval_prog call
    // let eval_res = Term::eval_expr(&expr);
    // info!("Evaled: {}", print_eval_res(eval_res));
}

pub fn run_term(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(res) => run_expr(res),
    }
}

fn run_type(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::TypeParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(res) => {
            info!("{}", res);
            info!("Free vars: {:#?}", res.free_vars());
        }
    }
}

pub fn run_program(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ProgramParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(prog) => {
            let mut type_checker = bi_types::TypeChecker::new();
            match type_checker.synth_prog(prog.clone()) {
                Err(err) => {
                    error!("{}", err.print());
                    info!("Trying interpreter anyway:");
                    let eval_result = Term::eval_prog(prog);
                    info!("{}", print_eval_res(eval_result));
                }
                Ok(tys) => {
                    info!("Running interpreter:");
                    let eval_result = Term::eval_prog(tys.into_iter().map(|(e, _)| e).collect());
                    info!("{}", print_eval_res(eval_result));
                    // info!("Running WASM backend:");
                    // wasm::test_wasm(tys);
                }
            };
        }
    }
}
pub fn run_wasm_program(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ProgramParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(prog) => {
            let mut type_checker = bi_types::TypeChecker::new();
            match type_checker.synth_prog(prog.clone()) {
                Err(err) => {
                    error!("{}", err.print());
                }
                Ok(tys) => {
                    info!("Codegen:");
                    wasm::test_wasm(tys);
                }
            };
        }
    }
}

pub fn run() {
    // `()` can be used when no completer is required
    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }

    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(&line);
                if line.starts_with(":ty") {
                    run_type(line.trim_start_matches(":ty "));
                } else {
                    run_term(&line);
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}
