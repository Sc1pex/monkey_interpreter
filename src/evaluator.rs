use crate::{ast::*, object::Object};

pub fn eval(b: Block) -> Option<Object> {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s)?;
    }

    Some(res)
}

fn eval_statement(s: Statement) -> Option<Object> {
    match s {
        Statement::Expression { value: e } => eval_expression(e),
        _ => None,
    }
}

fn eval_expression(e: Expression) -> Option<Object> {
    match e {
        Expression::Integer(x) => Some(Object::Integer(x)),
        Expression::Boolean(b) => Some(Object::Boolean(b)),
        _ => None,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{lexer::Lexer, parser::Parser};

    #[test]
    fn eval_int() {
        let tests = [("5", Object::Integer(5)), ("10", Object::Integer(10))];
        for (input, expected) in tests.iter() {
            let mut parser = Parser::new(Lexer::new(input));
            let program = parser.parse().unwrap();
            let evaluated = eval(program).unwrap();
            assert_eq!(evaluated, *expected);
        }
    }

    #[test]
    fn eval_bool() {
        let tests = [
            ("true", Object::Boolean(true)),
            ("false", Object::Boolean(false)),
        ];
        for (input, expected) in tests.iter() {
            let mut parser = Parser::new(Lexer::new(input));
            let program = parser.parse().unwrap();
            let evaluated = eval(program).unwrap();
            assert_eq!(evaluated, *expected);
        }
    }
}
