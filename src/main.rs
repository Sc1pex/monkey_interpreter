#![feature(let_chains)]
#![allow(dead_code)]

mod ast;
mod lexer;
mod parser;
mod repl;
mod token;

fn main() {
    println!("Monkeylang interpreter");
    repl::run();
}
