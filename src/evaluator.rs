use crate::{
    ast::*,
    object::{Environment, Object},
};

type EvalResult = Result<Object, String>;

// Evaluates the root node of the AST
pub fn eval(b: Block, env: &mut Environment) -> EvalResult {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s, env)?;
        if let Object::Return(obj) = res {
            return Ok(*obj);
        }
    }

    Ok(res)
}

// Evaluates a block of statements
// Different from eval() in that it dose not return the inner object of a return value
fn eval_block(b: Block, env: &mut Environment) -> EvalResult {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s, env)?;
        if let Object::Return(_) = res {
            return Ok(res);
        }
    }

    Ok(res)
}

fn eval_statement(s: Statement, env: &mut Environment) -> EvalResult {
    match s {
        Statement::Expression { value: e } => eval_expression(e, env),
        Statement::Return { value: e } => Ok(Object::Return(Box::new(eval_expression(e, env)?))),
        Statement::Let { ident, value } => {
            let value = eval_expression(value, env)?;
            env.set(&ident.name, value);
            Ok(Object::Null)
        }
    }
}

fn eval_expression(e: Expression, env: &mut Environment) -> EvalResult {
    match e {
        Expression::Integer(x) => Ok(Object::Integer(x)),
        Expression::Boolean(b) => Ok(Object::Boolean(b)),
        Expression::Prefix { operator, right } => {
            let right = eval_expression(*right, env)?;
            eval_prefix_expression(operator, right, env)
        }
        Expression::Infix {
            left,
            operator,
            right,
        } => {
            let left = eval_expression(*left, env)?;
            let right = eval_expression(*right, env)?;
            eval_infix_expression(operator, left, right, env)
        }
        Expression::If {
            condition,
            consequence,
            alternative,
        } => {
            let condition = eval_expression(*condition, env)?;
            if condition.is_truthy() {
                eval_block(consequence, env)
            } else if let Some(alt) = alternative {
                eval_block(alt, env)
            } else {
                Ok(Object::Null)
            }
        }
        Expression::Identifier(ident) => match env.get(&ident.name) {
            Some(obj) => Ok(obj),
            None => Err(format!("Identifier not found: {}", ident.name)),
        },
        _ => Err("".into()),
    }
}

fn eval_infix_expression(
    operator: InfixOperator,
    left: Object,
    right: Object,
    env: &mut Environment,
) -> EvalResult {
    match operator {
        InfixOperator::Add => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x + y)),
            _ => {}
        },
        InfixOperator::Subtract => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x - y)),
            _ => {}
        },
        InfixOperator::Multiply => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x * y)),
            _ => {}
        },
        InfixOperator::Divide => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x / y)),
            _ => {}
        },
        InfixOperator::Equal => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x == y)),
            (Object::Boolean(x), Object::Boolean(y)) => return Ok(Object::Boolean(x == y)),
            _ => {}
        },
        InfixOperator::NotEqual => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x != y)),
            (Object::Boolean(x), Object::Boolean(y)) => return Ok(Object::Boolean(x != y)),
            _ => {}
        },
        InfixOperator::LessThan => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x < y)),
            _ => {}
        },
        InfixOperator::GreaterThan => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x > y)),
            _ => {}
        },
    };

    Err(format!(
        "Unknown operator: {} {} {}",
        left.type_name(),
        operator,
        right.type_name()
    ))
}

fn eval_prefix_expression(
    operator: PrefixOperator,
    right: Object,
    env: &mut Environment,
) -> EvalResult {
    match operator {
        PrefixOperator::Not => match right {
            Object::Boolean(b) => Ok(Object::Boolean(!b)),
            Object::Null => Ok(Object::Boolean(true)),
            _ => Ok(Object::Boolean(false)),
        },
        PrefixOperator::Negate => match right {
            Object::Integer(x) => Ok(Object::Integer(-x)),
            _ => Err(format!("Unknown operator: -{}", right.type_name())),
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
            ("5", Ok(Object::Integer(5))),
            ("-5", Ok(Object::Integer(-5))),
            ("10", Ok(Object::Integer(10))),
            ("-10", Ok(Object::Integer(-10))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_bool() {
        let tests = [
            ("true", Ok(Object::Boolean(true))),
            ("false", Ok(Object::Boolean(false))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_bang() {
        let tests = [
            ("!true", Ok(Object::Boolean(false))),
            ("!false", Ok(Object::Boolean(true))),
            ("!!true", Ok(Object::Boolean(true))),
            ("!!false", Ok(Object::Boolean(false))),
            ("!5", Ok(Object::Boolean(false))),
            ("!!5", Ok(Object::Boolean(true))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_infix() {
        let tests = [
            ("5 + 5", Ok(Object::Integer(10))),
            ("5 - 5", Ok(Object::Integer(0))),
            ("5 * 5", Ok(Object::Integer(25))),
            ("5 / 5", Ok(Object::Integer(1))),
            ("12 * 3 / 4", Ok(Object::Integer(9))),
            ("1 + 2 * 4", Ok(Object::Integer(9))),
            ("(1 + 2) * 4", Ok(Object::Integer(12))),
            ("5 > 5", Ok(Object::Boolean(false))),
            ("5 < 5", Ok(Object::Boolean(false))),
            ("5 == 5", Ok(Object::Boolean(true))),
            ("5 != 5", Ok(Object::Boolean(false))),
            ("5 == 6", Ok(Object::Boolean(false))),
            ("5 != 6", Ok(Object::Boolean(true))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_conditional() {
        let tests = [
            ("if (true) { 10 }", Ok(Object::Integer(10))),
            ("if (false) { 10 }", Ok(Object::Null)),
            ("if (1) { 10 }", Ok(Object::Integer(10))),
            ("if (1 < 2) { 10 }", Ok(Object::Integer(10))),
            ("if (1 > 2) { 10 }", Ok(Object::Null)),
            ("if (1 > 2) { 10 } else { 20 }", Ok(Object::Integer(20))),
            ("if (1 < 2) { 10 } else { 20 }", Ok(Object::Integer(10))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_return() {
        let tests = [
            ("return 10;", Ok(Object::Integer(10))),
            ("return 10; 9;", Ok(Object::Integer(10))),
            ("return 2 * 5; 9;", Ok(Object::Integer(10))),
            ("9; return 2 * 5; 9;", Ok(Object::Integer(10))),
            (
                "if (10 > 1) {
                    if (10 > 1) {
                        if (10 > 1) {
                            if (10 > 1) {
                                return 100;
                            }
                        }
                        return 10;
                    }
                    return 1;
                }",
                Ok(Object::Integer(100)),
            ),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_errors() {
        let tests = [
            ("-true", Err("Unknown operator: -BOOLEAN".into())),
            (
                "5 + true;",
                Err("Unknown operator: INTEGER + BOOLEAN".into()),
            ),
            (
                "5 + true; 5;",
                Err("Unknown operator: INTEGER + BOOLEAN".into()),
            ),
            (
                "true + false;",
                Err("Unknown operator: BOOLEAN + BOOLEAN".into()),
            ),
            (
                "5; true + false; 5",
                Err("Unknown operator: BOOLEAN + BOOLEAN".into()),
            ),
            (
                "if (10 > 1) { true + false; }",
                Err("Unknown operator: BOOLEAN + BOOLEAN".into()),
            ),
            (
                "if (10 > 1) {
                    if (10 > 1) {
                        return true + false;
                    }
                    return 1;
                }",
                Err("Unknown operator: BOOLEAN + BOOLEAN".into()),
            ),
            ("foobar", Err("Identifier not found: foobar".into())),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_let() {
        let tests = [
            ("let a = 10; a;", Ok(Object::Integer(10))),
            ("let a = 10 * 10; a;", Ok(Object::Integer(100))),
            ("let a = 10; let b = a; b;", Ok(Object::Integer(10))),
            (
                "let a = 10; let b = a; let c = a + b + 5; c;",
                Ok(Object::Integer(25)),
            ),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    fn test_input(input: &str, expected: EvalResult) {
        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse().unwrap();
        let mut env = Environment::new();
        let evaluated = eval(program, &mut env);
        assert_eq!(evaluated, expected);
    }
}
