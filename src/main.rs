#![feature(let_chains)]
#![allow(dead_code)]

use clap::Parser;
use interpreter::{environment::Environment, evaluator::eval, lexer::Lexer, parser, repl};
use std::{cell::RefCell, rc::Rc};

#[derive(Parser)]
struct Cli {
    file: Option<String>,
}

fn main() {
    let cli = Cli::parse();
    if let Some(file) = cli.file {
        run_file(&file);
    } else {
        println!("Monkeylang interpreter");
        repl::run();
    }
}

fn run_file(file: &str) {
    let program = std::fs::read_to_string(file).expect("Could not read file");
    let mut env = Rc::new(RefCell::new(Environment::default()));
    let mut parser = parser::Parser::new(Lexer::new(&program));
    match parser.parse() {
        Ok(program) => match eval(program, &mut env) {
            Ok(res) => println!("{}", res),
            Err(e) => println!("Evaluation error: {}", e),
        },
        Err(errors) => {
            println!("Parser errors:");
            for err in errors {
                println!("\t{}", err);
            }
        }
    }
}
