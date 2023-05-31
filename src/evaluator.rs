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
        Expression::Prefix { operator, right } => {
            let right = eval_expression(*right)?;
            eval_prefix_expression(operator, right)
        }
        Expression::Infix {
            left,
            operator,
            right,
        } => {
            let left = eval_expression(*left)?;
            let right = eval_expression(*right)?;
            eval_infix_expression(operator, left, right)
        }
        _ => None,
    }
}

fn eval_infix_expression(operator: InfixOperator, left: Object, right: Object) -> Option<Object> {
    match operator {
        InfixOperator::Add => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Integer(x + y)),
            _ => None,
        },
        InfixOperator::Subtract => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Integer(x - y)),
            _ => None,
        },
        InfixOperator::Multiply => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Integer(x * y)),
            _ => None,
        },
        InfixOperator::Divide => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Integer(x / y)),
            _ => None,
        },
        InfixOperator::Equal => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Boolean(x == y)),
            (Object::Boolean(x), Object::Boolean(y)) => Some(Object::Boolean(x == y)),
            _ => None,
        },
        InfixOperator::NotEqual => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Boolean(x != y)),
            (Object::Boolean(x), Object::Boolean(y)) => Some(Object::Boolean(x != y)),
            _ => None,
        },
        InfixOperator::LessThan => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Boolean(x < y)),
            _ => None,
        },
        InfixOperator::GreaterThan => match (left, right) {
            (Object::Integer(x), Object::Integer(y)) => Some(Object::Boolean(x > y)),
            _ => None,
        },
    }
}

fn eval_prefix_expression(operator: PrefixOperator, right: Object) -> Option<Object> {
    match operator {
        PrefixOperator::Not => match right {
            Object::Boolean(b) => Some(Object::Boolean(!b)),
            Object::Null => Some(Object::Boolean(true)),
            _ => Some(Object::Boolean(false)),
        },
        PrefixOperator::Negate => match right {
            Object::Integer(x) => Some(Object::Integer(-x)),
            _ => None,
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{lexer::Lexer, parser::Parser};

    #[test]
    fn eval_int() {
        let tests = [
            ("5", Object::Integer(5)),
            ("-5", Object::Integer(-5)),
            ("10", Object::Integer(10)),
            ("-10", Object::Integer(-10)),
        ];
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

    #[test]
    fn eval_bang() {
        let tests = [
            ("!true", Object::Boolean(false)),
            ("!false", Object::Boolean(true)),
            ("!!true", Object::Boolean(true)),
            ("!!false", Object::Boolean(false)),
            ("!5", Object::Boolean(false)),
            ("!!5", Object::Boolean(true)),
        ];
        for (input, expected) in tests.iter() {
            let mut parser = Parser::new(Lexer::new(input));
            let program = parser.parse().unwrap();
            let evaluated = eval(program).unwrap();
            assert_eq!(evaluated, *expected);
        }
    }

    #[test]
    fn eval_infix() {
        let tests = [
            ("5 + 5", Object::Integer(10)),
            ("5 - 5", Object::Integer(0)),
            ("5 * 5", Object::Integer(25)),
            ("5 / 5", Object::Integer(1)),
            ("12 * 3 / 4", Object::Integer(9)),
            ("1 + 2 * 4", Object::Integer(9)),
            ("(1 + 2) * 4", Object::Integer(12)),
            ("5 > 5", Object::Boolean(false)),
            ("5 < 5", Object::Boolean(false)),
            ("5 == 5", Object::Boolean(true)),
            ("5 != 5", Object::Boolean(false)),
            ("5 == 6", Object::Boolean(false)),
            ("5 != 6", Object::Boolean(true)),
        ];
        for (input, expected) in tests.iter() {
            let mut parser = Parser::new(Lexer::new(input));
            let program = parser.parse().unwrap();
            let evaluated = eval(program).unwrap();
            assert_eq!(evaluated, *expected);
        }
    }
}
