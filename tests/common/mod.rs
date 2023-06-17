use interpreter::{
    ast::Block,
    environment::Environment,
    evaluator::{eval, EvalResult},
    lexer::Lexer,
    parser::Parser,
};
use std::{cell::RefCell, rc::Rc};

#[macro_export]
macro_rules! evaluator_test {
    ($test_name:ident, $(($input:expr, $output:expr)),+) => {
        #[test]
        fn $test_name() {
            $(crate::common::evaluator_test_input($input, $output);)*
        }
    };
}

pub fn evaluator_test_input(input: &str, expected: EvalResult) {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse().unwrap();
    let mut env = Rc::new(RefCell::new(Environment::default()));
    let evaluated = eval(program, &mut env);
    assert_eq!(evaluated, expected);
}

#[macro_export]
macro_rules! parser_test {
    ($test_name:ident, $(($input:expr, $output:expr)),+) => {
        #[test]
        fn $test_name() {
            $(crate::common::parser_test_input($input, $output);)*
        }
    };
}

pub fn parser_test_input(input: &str, expected: Block) {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse().unwrap();
    assert_eq!(expected.statements.len(), program.statements.len());
    for (e, s) in expected.statements.iter().zip(program.statements.iter()) {
        assert_eq!(e, s);
    }
}
