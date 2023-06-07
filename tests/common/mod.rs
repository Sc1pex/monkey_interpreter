use interpreter::{
    evaluator::{eval, EvalResult},
    lexer::Lexer,
    object::Environment,
    parser::Parser,
};
use std::{cell::RefCell, rc::Rc};

#[macro_export]
macro_rules! evaluator_test {
    ($test_name:ident, $(($input:expr, $output:expr)),+) => {
        #[test]
        fn $test_name() {
            $(test_input($input, $output);)*
        }
    };
}

pub fn test_input(input: &str, expected: EvalResult) {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse().unwrap();
    // println!("PARSED:\n{:#?}\n", program);
    let mut env = Rc::new(RefCell::new(Environment::new()));
    let evaluated = eval(program, &mut env);
    assert_eq!(evaluated, expected);
}
