extern crate siml;
use siml::token;

fn main() {
    let input = "well";
    let mut lexer = token::Lexer::new(&input);
    lexer.drain()
}
