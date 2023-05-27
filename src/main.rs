#![feature(let_chains)]

mod lexer;
mod repl;
mod token;

fn main() {
    println!("Monkeylang interpreter");
    repl::run();
}
