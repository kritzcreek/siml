#[macro_use]
extern crate log;
extern crate siml;
extern crate simplelog;

use siml::eval::Eval;
use siml::expr::Expr;
use siml::grammar;
use siml::term::Term;
use siml::token;
use simplelog::*;

fn parse_expr(input: &str) -> Expr {
    let new_input = input.clone();
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    info!("Parsed {} into {}", new_input, &res.print());
    res
}

fn run_expr(input: &str) -> Expr {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    let mut e = Eval::new();
    let eval_res = e.eval(res);
    info!("EFinished: {}", eval_res.print());
    eval_res
}

fn run_term(input: &str) -> Term {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    let eval_res = Term::eval_expr(&res);
    info!("TFinished: {}", eval_res.print());
    eval_res
}

fn main() {
    let logger_conf = Config {
        time: None,
        level: Some(Level::Error),
        target: None,
        location: None,
        time_format: None,
    };
    TermLogger::init(LevelFilter::Info, logger_conf).unwrap();
    parse_expr("x");
    parse_expr("\\y. x y z");
    parse_expr("\\y. x (\\z.z)");
    parse_expr("x (y z)");
    parse_expr("(x x) (y z)");
    run_expr("(\\x. x) y");
    run_expr("(\\y.(\\x. x y)) x");
    run_expr("(\\y.(\\x. x y)) ((\\l. l) x)");
    run_expr("(\\y.(\\x. x y) (\\x. x y)) x");
    run_expr("(\\x.(\\x. x y) x) k");
    println!();
    run_expr("(\\x. (\\y.(\\x. x y)) x)(\\l. l)");
    run_term("(\\x. (\\y.(\\x. x y)) x)(\\l. l)");
    println!();
    run_expr("(\\x. (\\y.(\\x. x y)) x)(\\l. l)(\\k. k)");
    run_term("(\\x. (\\y.(\\x. x y)) x)(\\l. l)(\\k. k)");
    println!();
    run_expr("(\\x. x) true");
    run_term("(\\x. x) true");
    println!();
    run_expr("(\\x. x) 100");
    run_term("(\\x. x) 100");
    println!();
    run_expr("(\\x. x) pi");
    run_term("(\\x. x) pi");
    println!();
    run_term("add ((\\x. x) 4) ((\\x. x) 4)");

    // run_expr("(\\x. x x) (\\x. x x)");
    // run_term("(\\x. x x) (\\x. x x)");
}
