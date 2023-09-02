#![allow(dead_code)]

use std::fmt::Display;

use crate::{lexer::Token, parser::*};

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Int(i64),
    Boolean(bool),
    Null,
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Int(i) => write!(f, "{}", i),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Null => write!(f, "null"),
        }
    }
}

pub fn eval_program(Program(program): &Program) {
    for statement in program {
        let evaluated = eval(statement).unwrap_or_else(|e| panic!("Evaluator error: {}", e));
        println!("{}", evaluated);
    }
}

fn eval(statement: &Statement) -> Result<Object, String> {
    match statement {
        Statement::Expression(e) => eval_expression(e),
        _ => todo!(),
    }
}

fn eval_expression(expression: &Expression) -> Result<Object, String> {
    match expression {
        Expression::Int(i) => Ok(Object::Int(*i)),
        Expression::Boolean(b) => Ok(Object::Boolean(*b)),
        Expression::Prefix(op, e) => eval_prefix_expression(op, e),
        Expression::Infix(l, op, r) => eval_infix_expression(op, l, r),
        _ => todo!(),
    }
}

fn eval_prefix_expression(op: &Token, e: &Expression) -> Result<Object, String> {
    let right = eval_expression(e)?;

    let res = match op {
        Token::Bang => match right {
            Object::Int(i) => Object::Boolean(i == 0),
            Object::Boolean(b) => Object::Boolean(!b),
            Object::Null => Object::Boolean(true),
            // _ => return Err(format!("Unknown operator: {}{:?}", op, right)),
        },
        Token::Minus => match right {
            Object::Int(i) => Object::Int(-i),
            _ => return Err(format!("Unknown operator: {}{:?}", op, right)),
        },
        _ => unreachable!(),
    };
    Ok(res)
}

fn eval_infix_expression(op: &Token, l: &Expression, r: &Expression) -> Result<Object, String> {
    let l = eval_expression(l)?;
    let r = eval_expression(r)?;

    let res = match op {
        Token::Plus => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Int(l + r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Minus => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Int(l - r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Asterisk => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Int(l * r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Slash => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Int(l / r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Lt => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Boolean(l < r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Gt => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Boolean(l > r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::Eq => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Boolean(l == r),
            (Object::Boolean(l), Object::Boolean(r)) => Object::Boolean(l == r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        Token::NotEq => match (&l, &r) {
            (Object::Int(l), Object::Int(r)) => Object::Boolean(l != r),
            (Object::Boolean(l), Object::Boolean(r)) => Object::Boolean(l != r),
            _ => return Err(format!("Unknown operator: {:?} {} {:?}", l, op, r,)),
        },
        _ => unreachable!(),
    };
    Ok(res)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lexer::Lexer;

    #[test]
    fn int_expression() {
        let tests = vec![("5", Object::Int(5)), ("10", Object::Int(10))];
        test(tests);
    }

    #[test]
    fn bool_expresion() {
        let tests = vec![
            ("true", Object::Boolean(true)),
            ("false", Object::Boolean(false)),
        ];
        test(tests);
    }

    #[test]
    fn prefix_expression() {
        let tests = vec![
            ("!true", Object::Boolean(false)),
            ("!false", Object::Boolean(true)),
            ("!5", Object::Boolean(false)),
            ("!0", Object::Boolean(true)),
            ("!!true", Object::Boolean(true)),
            ("!!false", Object::Boolean(false)),
            ("!!5", Object::Boolean(true)),
            ("-5", Object::Int(-5)),
            ("-10", Object::Int(-10)),
            ("--5", Object::Int(5)),
            ("--10", Object::Int(10)),
        ];
        test(tests);
    }

    #[test]
    fn infix_expression() {
        let tests = vec![
            ("5 + 5", Object::Int(10)),
            ("5 - 5", Object::Int(0)),
            ("5 * 5", Object::Int(25)),
            ("5 / 5", Object::Int(1)),
            ("5 > 5", Object::Boolean(false)),
            ("5 < 5", Object::Boolean(false)),
            ("5 == 5", Object::Boolean(true)),
            ("5 != 5", Object::Boolean(false)),
            ("true == true", Object::Boolean(true)),
            ("true != true", Object::Boolean(false)),
            ("false == false", Object::Boolean(true)),
            ("false != false", Object::Boolean(false)),
            ("true == false", Object::Boolean(false)),
            ("true != false", Object::Boolean(true)),
            ("false == true", Object::Boolean(false)),
            ("false != true", Object::Boolean(true)),
            ("(5 + 5) * 2", Object::Int(20)),
            ("2 * (5 + 5)", Object::Int(20)),
            ("3 * 3 * 3 + 10", Object::Int(37)),
            ("3 * (3 * 3) + 10", Object::Int(37)),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", Object::Int(50)),
        ];
        test(tests);
    }

    fn test(tests: Vec<(&str, Object)>) {
        for (input, exp) in tests {
            let Program(program) = Parser::new(Lexer::new(input)).parse_program().unwrap();
            let evaluated = eval(&program[0]).unwrap_or_else(|e| panic!("Evaluator error: {}", e));

            assert_eq!(evaluated, exp, "Expected {:?}, got {:?}", exp, evaluated);
        }
    }
}
