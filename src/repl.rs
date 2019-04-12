use crate::grammar;
use crate::term;
use crate::term::Term;
use crate::token;
use crate::types;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn print_ty_res(ty_res: Result<types::Type, types::TypeError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

fn print_eval_res(ty_res: Result<term::Term, term::EvalError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

fn run_term(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(res) => {
            let mut type_checker = types::TypeChecker::new();
            let ty_res = type_checker.infer_expr(&res);
            info!("TInferred: {}", print_ty_res(ty_res));
            let eval_res = Term::eval_expr(&res);
            info!("TFinished: {}", print_eval_res(eval_res));
        }
    }
}

pub fn repl() {
    // `()` can be used when no completer is required
    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }

    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_ref());
                run_term(&line);
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
