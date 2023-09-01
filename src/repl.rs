use crate::lexer::Lexer;

pub fn run() {
    loop {
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
        let lexer = Lexer::new(&input);

        lexer.for_each(|token| println!("{:?}", token));
    }
}
