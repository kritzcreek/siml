extern crate siml;
use siml::token;
use siml::grammar;

fn main() {
    let input = "\\x. \\y. y x";
    let lexer = token::Lexer::new(&input);
    /*
    lexer.for_each(|t| {
        println!("{:?}", t)
    });
    */

    println!("{:?}", grammar::ExprParser::new().parse(lexer))
}
