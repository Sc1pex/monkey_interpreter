#![feature(let_chains)]
#![allow(dead_code)]

mod ast;
mod evaluator;
mod lexer;
mod object;
mod parser;
mod repl;
mod token;

fn main() {
    println!("Monkeylang interpreter");
    repl::run();
}
