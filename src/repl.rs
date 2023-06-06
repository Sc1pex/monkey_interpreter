use crate::{evaluator::eval, lexer::Lexer, object::Environment, parser::Parser};
use std::{
    cell::RefCell,
    io::{BufRead, Write},
    rc::Rc,
};

pub fn run() {
    let mut stdin = std::io::stdin().lock();
    let mut env = Rc::new(RefCell::new(Environment::new()));

    loop {
        print!(">> ");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        stdin.read_line(&mut line).unwrap();

        let mut parser = Parser::new(Lexer::new(&line));
        match parser.parse() {
            Ok(program) => {
                let evaluated = eval(program, &mut env);
                if let Ok(obj) = evaluated {
                    println!("{}", obj);
                } else {
                    println!("Error: {}", evaluated.unwrap_err());
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
