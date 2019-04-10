extern crate siml;
use siml::token;
use siml::grammar;
use siml::ast::Expr;
use siml::eval::Eval;

fn parse_expr(input: &str) -> Expr {
    let new_input = input.clone();
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    println!("Parsed {} into {}", new_input, &res.print());
    res
}

fn run_expr(input: &str) -> Expr {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    println!("Evaling: {}", &res.print());
    let mut e = Eval::new();
    let eval_res = e.eval(&res);
    println!("Evaled: {}", eval_res.print());
    eval_res
}

fn main() {
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
}
