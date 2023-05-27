use std::io::{BufRead, Write};

use crate::{lexer::Lexer, token::Token};

pub fn run() {
    let mut stdin = std::io::stdin().lock();

    loop {
        print!(">> ");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        stdin.read_line(&mut line).unwrap();

        let mut lexer = Lexer::new(&line);
        while let t = lexer.next() && t != Token::Eof {
            println!("{:?}", t);
        }
    }
}
