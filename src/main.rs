#![feature(let_chains)]
#![allow(dead_code)]

use interpreter::repl;

fn main() {
    println!("Monkeylang interpreter");
    repl::run();
}
