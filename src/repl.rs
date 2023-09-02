use crate::{evaluator::eval_program, lexer::Lexer, parser::Parser};
use std::io::Write;

pub fn run() {
    loop {
        let mut input = String::new();
        print!(">> ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_line(&mut input).unwrap();
        let mut parser = Parser::new(Lexer::new(&input));

        match parser.parse_program() {
            Ok(p) => {
                eval_program(&p);
            }
            Err(err) => {
                println!("Parser had {} errors", err.len());
                for e in err {
                    println!("{}", e);
                }
            }
        }
    }
}
