use crate::{evaluator::eval, lexer::Lexer, parser::Parser};
use std::io::{BufRead, Write};

pub fn run() {
    let mut stdin = std::io::stdin().lock();

    loop {
        print!(">> ");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        stdin.read_line(&mut line).unwrap();

        let mut parser = Parser::new(Lexer::new(&line));
        match parser.parse() {
            Ok(program) => {
                let evaluated = eval(program);
                if let Some(obj) = evaluated {
                    println!("{}", obj);
                }
            }
            Err(errors) => {
                println!("Parser errors:");
                for err in errors {
                    println!("\t{}", err);
                }
            }
        }
    }
}
