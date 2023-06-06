use std::{cell::RefCell, rc::Rc};

use crate::{
    ast::*,
    object::{Builtin, Env, Environment, HashKey, HashPair, Object},
};

type EvalResult = Result<Object, String>;

// Evaluates the root node of the AST
pub fn eval(b: Block, env: &mut Env) -> EvalResult {
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
fn eval_block(b: Block, env: &mut Env) -> EvalResult {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s, env)?;
        if let Object::Return(_) = res {
            return Ok(res);
        }
    }

    Ok(res)
}

fn eval_statement(s: Statement, env: &mut Env) -> EvalResult {
    match s {
        Statement::Expression { value: e } => eval_expression(e, env),
        Statement::Return { value: e } => Ok(Object::Return(Box::new(eval_expression(e, env)?))),
        Statement::Let { ident, value } => {
            let value = eval_expression(value, env)?;
            env.borrow_mut().set(&ident.name, value);
            Ok(Object::Null)
        }
    }
}

fn eval_expression(e: Expression, env: &mut Env) -> EvalResult {
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
        Expression::Identifier(ident) => match env.borrow().get(&ident.name) {
            Some(obj) => Ok(obj),
            None => {
                if let Some(builtin) = Builtin::lookup(&ident.name) {
                    Ok(Object::Builtin(builtin))
                } else {
                    Err(format!("Identifier not found: {}", ident.name))
                }
            }
        },
        Expression::FunctionLiteral { params, body } => Ok(Object::Function {
            parameters: params,
            body,
            env: env.clone(),
        }),
        Expression::Call { function, args } => {
            let function = eval_expression(*function, env)?;
            let args = eval_expressions(args, env)?;

            match function {
                Object::Function {
                    parameters,
                    body,
                    env,
                } => {
                    let mut env = Rc::new(RefCell::new(Environment::new_enclosed(&env)));
                    for (param, arg) in parameters.into_iter().zip(args.into_iter()) {
                        env.borrow_mut().set(&param.name, arg);
                    }

                    Ok(eval_block(body, &mut env)?.unwrap_return())
                }
                Object::Builtin(b) => eval_builtin(b, args),
                _ => Err(format!("Not a function: {}", function.type_name()))?,
            }
        }
        Expression::ArrayLiteral { elements } => {
            let elements = eval_expressions(elements, env)?;
            Ok(Object::Array(elements))
        }
        Expression::Index { left, index } => {
            let left = eval_expression(*left, env)?;
            let index = eval_expression(*index, env)?;

            match (&left, &index) {
                (Object::Array(elements), Object::Integer(i)) => {
                    if *i < 0 || *i >= elements.len() as i64 {
                        return Err(format!("Index out of bounds: {}", i,));
                    }
                    Ok(elements[*i as usize].clone())
                }
                (Object::Hash(hash), key) => {
                    let key = HashKey::try_from(key)?;
                    match hash.get(&key) {
                        Some(pair) => Ok(pair.value.clone()),
                        None => Ok(Object::Null),
                    }
                }
                _ => Err(format!(
                    "Index operator not supported for {}",
                    left.type_name(),
                )),
            }
        }
        Expression::StringLiteral(s) => Ok(Object::String(s)),
        Expression::HashLiteral { pairs } => {
            let mut hash = std::collections::HashMap::new();
            for (key, value) in pairs {
                let key = eval_expression(key, env)?;
                let value = eval_expression(value, env)?;
                let hash_key = HashKey::try_from(&key)?;
                hash.insert(hash_key, HashPair { key, value });
            }
            Ok(Object::Hash(hash))
        }
    }
}

fn eval_expressions(exprs: Vec<Expression>, env: &mut Env) -> Result<Vec<Object>, String> {
    exprs.into_iter().map(|e| eval_expression(e, env)).collect()
}

fn eval_builtin(builtin: Builtin, args: Vec<Object>) -> EvalResult {
    match builtin {
        Builtin::Len => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'len'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::String(s) => Ok(Object::Integer(s.len() as i64)),
                Object::Array(elements) => Ok(Object::Integer(elements.len() as i64)),
                _ => Err(format!(
                    "Wrong argument to 'len'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::First => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'first'. Expected 1, got {}",
                    args.len()
                ));
            }

            match &args[0] {
                Object::Array(elements) => Ok(elements.first().unwrap_or(&Object::Null).clone()),
                _ => Err(format!(
                    "Wrong argument to 'first'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Last => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'last'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::Array(elements) => Ok(elements.last().unwrap_or(&Object::Null).clone()),
                _ => Err(format!(
                    "Wrong argument to 'last'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Rest => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'last'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::Array(elements) => {
                    if elements.is_empty() {
                        return Ok(Object::Null);
                    }
                    Ok(Object::Array(elements[1..].to_vec()))
                }
                _ => Err(format!(
                    "Wrong argument to 'rest'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Push => {
            if args.len() != 2 {
                return Err(format!(
                    "Wrong number of arguments to 'push'. Expected 1, got {}",
                    args.len()
                ));
            }

            match &args[0] {
                Object::Array(elements) => {
                    let mut elements = elements.clone();
                    elements.push(args[1].clone());
                    Ok(Object::Array(elements))
                }
                _ => Err(format!(
                    "Wrong argument to 'push'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Print => {
            for arg in args {
                println!("{}", arg);
            }
            Ok(Object::Null)
        }
    }
}

fn eval_infix_expression(
    operator: InfixOperator,
    left: Object,
    right: Object,
    _env: &mut Env,
) -> EvalResult {
    match operator {
        InfixOperator::Add => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x + y)),
            (Object::String(x), Object::String(y)) => {
                return Ok(Object::String(format!("{}{}", x, y)))
            }

            _ => {}
        },
        InfixOperator::Subtract => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x - y));
            }
        }
        InfixOperator::Multiply => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x * y));
            }
        }
        InfixOperator::Divide => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x / y));
            }
        }
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
        InfixOperator::LessThan => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Boolean(x < y));
            }
        }
        InfixOperator::GreaterThan => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Boolean(x > y));
            }
        }
    };

    Err(format!(
        "Unknown operator: {} {} {}",
        left.type_name(),
        operator,
        right.type_name()
    ))
}

fn eval_prefix_expression(operator: PrefixOperator, right: Object, _env: &mut Env) -> EvalResult {
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
    use crate::{
        lexer::Lexer,
        object::{Environment, HashKey, HashPair},
        parser::Parser,
    };
    use std::{cell::RefCell, rc::Rc};

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
            (
                r#""foobar" - "baz""#,
                Err("Unknown operator: STRING - STRING".into()),
            ),
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

    #[test]
    fn eval_fn() {
        let tests = [
            (
                "fn (x) { x + 2}; ",
                Ok(Object::Function {
                    parameters: vec![Identifier::new("x")],
                    body: Block {
                        statements: vec![Statement::Expression {
                            value: Expression::Infix {
                                left: Box::new(Expression::Identifier(Identifier::new("x"))),
                                operator: InfixOperator::Add,
                                right: Box::new(Expression::Integer(2)),
                            },
                        }],
                    },
                    env: Rc::new(RefCell::new(Environment::new())),
                }),
            ),
            (
                "let identity = fn(x) { x; }; identity(5);",
                Ok(Object::Integer(5)),
            ),
            (
                "let identity = fn(x) { return x; }; identity(5);",
                Ok(Object::Integer(5)),
            ),
            (
                "let double = fn(x) { x * 2; }; double(5);",
                Ok(Object::Integer(10)),
            ),
            (
                "let add = fn(x, y) { x + y; }; add(5, 5);",
                Ok(Object::Integer(10)),
            ),
            (
                "let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));",
                Ok(Object::Integer(20)),
            ),
            ("fn(x) { x; }(5)", Ok(Object::Integer(5))),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn closures() {
        let input = "
            let newAdder = fn(x) {
                fn(y) { x + y };
            };
            let addTwo = newAdder(2);
            addTwo(2);
        ";
        test_input(input, Ok(Object::Integer(4)));
    }

    #[test]
    fn eval_string() {
        let tests = [
            (
                r#""Hello World!""#,
                Ok(Object::String("Hello World!".into())),
            ),
            (
                r#""Hello" + " " + "World!""#,
                Ok(Object::String("Hello World!".into())),
            ),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_builtin_len() {
        let tests = [
            ("len(\"\")", Ok(Object::Integer(0))),
            ("len(\"four\")", Ok(Object::Integer(4))),
            ("len(\"hello world\")", Ok(Object::Integer(11))),
            ("len(1)", Err("Wrong argument to 'len'. Got INTEGER".into())),
            (
                "len(\"one\", \"two\")",
                Err("Wrong number of arguments to 'len'. Expected 1, got 2".into()),
            ),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_array_literal() {
        let input = "[1, 2 * 2, 3 + 3]";
        let expected = Ok(Object::Array(vec![
            Object::Integer(1),
            Object::Integer(4),
            Object::Integer(6),
        ]));

        test_input(input, expected);
    }

    #[test]
    fn eval_array_index() {
        let tests = [
            ("[1, 2, 3][0]", Ok(Object::Integer(1))),
            ("[1, 2, 3][1]", Ok(Object::Integer(2))),
            ("[1, 2, 3][2]", Ok(Object::Integer(3))),
            ("let i = 0; [1][i];", Ok(Object::Integer(1))),
            ("[1, 2, 3][1 + 1];", Ok(Object::Integer(3))),
            (
                "let myArray = [1, 2, 3]; myArray[2];",
                Ok(Object::Integer(3)),
            ),
            (
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
                Ok(Object::Integer(6)),
            ),
            (
                "let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]",
                Ok(Object::Integer(2)),
            ),
            ("[1, 2, 3][3]", Err("Index out of bounds: 3".into())),
            ("[1, 2, 3][-1]", Err("Index out of bounds: -1".into())),
        ];

        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn eval_array_builtin() {
        let tests = [
            ("let a = [1, 2, 3]; len(a)", Ok(Object::Integer(3))),
            ("let a = [1, 2, 3]; first(a)", Ok(Object::Integer(1))),
            ("let a = [1, 2, 3]; last(a)", Ok(Object::Integer(3))),
            (
                "let a = [1, 2, 3]; rest(a)",
                Ok(Object::Array(vec![Object::Integer(2), Object::Integer(3)])),
            ),
            (
                "let a = [1, 2, 3]; rest(rest(a))",
                Ok(Object::Array(vec![Object::Integer(3)])),
            ),
            (
                "let a = [1, 2, 3]; rest(rest(rest(a)))",
                Ok(Object::Array(vec![])),
            ),
            (
                "let a = [1, 2, 3]; rest(rest(rest(rest(a))))",
                Ok(Object::Null),
            ),
            (
                "let a = [1, 2, 3]; push(a, 4)",
                Ok(Object::Array(vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                ])),
            ),
        ];
        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    #[test]
    fn map_reduce() {
        let input = "
let map = fn(arr, f) {
    let iter = fn(arr, accumulated) {
        if (len(arr) == 0) {
            accumulated
        } else {
            iter(rest(arr), push(accumulated, f(first(arr))));
        }
    };
    iter(arr, []);
};
let a = [1, 2, 3, 4];
let double = fn (x) { x * 2 };
map(a, double)
";
        test_input(
            input,
            Ok(Object::Array(vec![
                Object::Integer(2),
                Object::Integer(4),
                Object::Integer(6),
                Object::Integer(8),
            ])),
        );
    }

    #[test]
    fn eval_hash_literal() {
        let input = r#"
let two = "two";
{
    "one": 10 - 9,
    two: 1 + 1,
    "thr" + "ee": 6 / 2,
    4: 4,
    true: 5,
    false: 6
}
"#;
        let expected = Ok(Object::Hash(
            vec![
                (
                    HashKey::String("one".into()),
                    HashPair {
                        key: Object::String("one".into()),
                        value: Object::Integer(1),
                    },
                ),
                (
                    HashKey::String("two".into()),
                    HashPair {
                        key: Object::String("two".into()),
                        value: Object::Integer(2),
                    },
                ),
                (
                    HashKey::String("three".into()),
                    HashPair {
                        key: Object::String("three".into()),
                        value: Object::Integer(3),
                    },
                ),
                (
                    HashKey::Integer(4),
                    HashPair {
                        key: Object::Integer(4),
                        value: Object::Integer(4),
                    },
                ),
                (
                    HashKey::Boolean(true),
                    HashPair {
                        key: Object::Boolean(true),
                        value: Object::Integer(5),
                    },
                ),
                (
                    HashKey::Boolean(false),
                    HashPair {
                        key: Object::Boolean(false),
                        value: Object::Integer(6),
                    },
                ),
            ]
            .into_iter()
            .collect(),
        ));
        test_input(input, expected);
    }

    #[test]
    fn illegal_hash_key() {
        let input = r#"
let badKey = fn() {};
{
    badKey: 1
}"#;
        let expected = Err("Unusable as hash key: FUNCTION".into());
        test_input(input, expected);
    }

    #[test]
    fn hash_index() {
        let tests = [
            (r#"let a = {"foo": 5}; a["foo"] "#, Ok(Object::Integer(5))),
            (r#"let a = {"foo": 5}; a["bar"] "#, Ok(Object::Null)),
            (r#"let a = {"foo": 5}; a[5] "#, Ok(Object::Null)),
            (
                r#" let key = "foo"; {key: 5}["foo"] "#,
                Ok(Object::Integer(5)),
            ),
            (r#"{}["foo"] "#, Ok(Object::Null)),
            (r#"{5: 5}[5] "#, Ok(Object::Integer(5))),
            (r#"{true: 5}[true] "#, Ok(Object::Integer(5))),
            (r#"{false: 5}[false] "#, Ok(Object::Integer(5))),
            (
                r#"{"name": "Monkey"}[fn(x) { x }];"#,
                Err("Unusable as hash key: FUNCTION".into()),
            ),
        ];

        for (input, expected) in tests {
            test_input(input, expected);
        }
    }

    fn test_input(input: &str, expected: EvalResult) {
        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse().unwrap();
        // println!("PARSED:\n{:#?}\n", program);
        let mut env = Rc::new(RefCell::new(Environment::new()));
        let evaluated = eval(program, &mut env);
        assert_eq!(evaluated, expected);
    }
}
