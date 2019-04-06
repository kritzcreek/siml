use std::str::{Chars};
use std::iter::Peekable;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Lambda,
    Dot,
    LParen,
    RParen,
    Ident(String),
}

pub struct Lexer<'input> {
    input: Peekable<Chars<'input>>,
    pos: u32,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Lexer<'input>{
        Lexer { input: input.chars().peekable(), pos: 0 }
    }

    fn next_char(&mut self) -> Option<char> {
        self.pos += 1;
        self.input.next()
    }

    fn peek(&mut self) -> Option<&char> {
        self.input.peek()
    }

    fn consume_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.next_char();
            } else {
                break;
            }
        }
    }
}

fn is_ident_start(c: &char) -> bool {
    match c {
        'a'...'z' => true,
        _ => false,
    }
}

fn is_ident_member(c: &char) -> bool {
    match c {
        'a'...'z' => true,
        _ => false,
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let token = match self.next_char() {
            Some('\\') => {
                Some(Token::Lambda)
            },
            Some('.') => {
                Some(Token::Dot)
            },
            Some('(') => {
                Some(Token::LParen)
            },
            Some(')') => {
                Some(Token::RParen)
            },
            Some(c) => {
                if is_ident_start(&c) {
                    let mut res = c.to_string();
                    while let Some(c) = self.peek() {
                        if is_ident_member(c) {
                            res.push(self.next_char().unwrap())
                        } else {
                            break;
                        }
                    }
                    Some(Token::Ident(res))
                } else {
                    None
                }
            }
            None => {
                None
            }
        };
        self.consume_whitespace();
        token
    }
}
