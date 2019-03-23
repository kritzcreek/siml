use std::str::{Chars};

pub fn hello() -> String{
     "something".to_owned()
}


#[derive(Debug, PartialEq, Eq)]
pub enum Token<'input> {
    Ident(&'input str)
}

pub struct Lexer<'input> {
    input: Chars<'input>,
    pos: u32,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Lexer<'input>{
        Lexer { input: input.chars(), pos: 0 }
    }

    fn next_char(&mut self) -> Option<char> {
        self.pos += 1;
        self.input.next()
    }

    pub fn drain(&mut self) {
        while let Some(c) = self.next_char() {
            println!("{:?}", c);
        }
        println!("Done")
    }
}
