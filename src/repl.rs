use std::io::{BufRead, Write};

use crate::{lexer::Lexer, parser::Parser, token::Token};

pub fn run() {
    let mut stdin = std::io::stdin().lock();

    loop {
        print!(">> ");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        stdin.read_line(&mut line).unwrap();

        let mut parser = Parser::new(Lexer::new(&line));
        let program = parser.parse();
        if !parser.errors().is_empty() {
            println!("Parser errors:");
            for err in parser.errors() {
                println!("\t{}", err);
            }
            continue;
        }
        println!("{}", program);
    }
}
