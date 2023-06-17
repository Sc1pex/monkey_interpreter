use interpreter::{
    ast::*,
    environment::Environment,
    evaluator::{eval, EvalResult},
    lexer::Lexer,
    object::*,
    parser::Parser,
};
use std::{cell::RefCell, rc::Rc};

evaluator_test!(
    ints,
    ("5", Ok(Object::Integer(5))),
    ("-5", Ok(Object::Integer(-5))),
    ("10", Ok(Object::Integer(10))),
    ("-10", Ok(Object::Integer(-10)))
);

evaluator_test!(
    bools,
    ("true", Ok(Object::Boolean(true))),
    ("false", Ok(Object::Boolean(false)))
);

evaluator_test!(
    bang_operator,
    ("!true", Ok(Object::Boolean(false))),
    ("!false", Ok(Object::Boolean(true))),
    ("!!true", Ok(Object::Boolean(true))),
    ("!!false", Ok(Object::Boolean(false))),
    ("!5", Ok(Object::Boolean(false))),
    ("!!5", Ok(Object::Boolean(true)))
);

evaluator_test!(
    infix_operators,
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
    ("5 != 6", Ok(Object::Boolean(true)))
);

evaluator_test!(
    conditionals,
    ("if (true) { 10 }", Ok(Object::Integer(10))),
    ("if (false) { 10 }", Ok(Object::Null)),
    ("if (1) { 10 }", Ok(Object::Integer(10))),
    ("if (1 < 2) { 10 }", Ok(Object::Integer(10))),
    ("if (1 > 2) { 10 }", Ok(Object::Null)),
    ("if (1 > 2) { 10 } else { 20 }", Ok(Object::Integer(20))),
    ("if (1 < 2) { 10 } else { 20 }", Ok(Object::Integer(10)))
);

evaluator_test!(
    returns,
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
        Ok(Object::Integer(100))
    )
);

evaluator_test!(
    errors,
    ("-true", Err("Unknown operator: -BOOLEAN".into())),
    (
        "5 + true;",
        Err("Unknown operator: INTEGER + BOOLEAN".into())
    ),
    (
        "5 + true; 5;",
        Err("Unknown operator: INTEGER + BOOLEAN".into())
    ),
    (
        "true + false;",
        Err("Unknown operator: BOOLEAN + BOOLEAN".into())
    ),
    (
        "5; true + false; 5",
        Err("Unknown operator: BOOLEAN + BOOLEAN".into())
    ),
    (
        "if (10 > 1) { true + false; }",
        Err("Unknown operator: BOOLEAN + BOOLEAN".into())
    ),
    (
        "if (10 > 1) {
                    if (10 > 1) {
                        return true + false;
                    }
                    return 1;
                }",
        Err("Unknown operator: BOOLEAN + BOOLEAN".into())
    ),
    ("foobar", Err("Identifier not found: foobar".into())),
    (
        r#""foobar" - "baz""#,
        Err("Unknown operator: STRING - STRING".into())
    )
);

evaluator_test!(
    let_statements,
    ("let a = 10; a;", Ok(Object::Integer(10))),
    ("let a = 10 * 10; a;", Ok(Object::Integer(100))),
    ("let a = 10; let b = a; b;", Ok(Object::Integer(10))),
    (
        "let a = 10; let b = a; let c = a + b + 5; c;",
        Ok(Object::Integer(25))
    )
);

evaluator_test!(
    functions,
    (
        "fn (x) { x + 2 }; ",
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
            env: Rc::new(RefCell::new(Environment::default())),
        })
    ),
    (
        "let identity = fn(x) { x; }; identity(5);",
        Ok(Object::Integer(5))
    ),
    (
        "let identity = fn(x) { return x; }; identity(5);",
        Ok(Object::Integer(5))
    ),
    (
        "let double = fn(x) { x * 2; }; double(5);",
        Ok(Object::Integer(10))
    ),
    (
        "let add = fn(x, y) { x + y; }; add(5, 5);",
        Ok(Object::Integer(10))
    ),
    (
        "let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));",
        Ok(Object::Integer(20))
    ),
    ("fn(x) { x; }(5)", Ok(Object::Integer(5)))
);

evaluator_test!(
    closures,
    (
        "let newAdder = fn(x) {
            fn(y) { x + y };
        };
        let addTwo = newAdder(2);
        addTwo(2);",
        Ok(Object::Integer(4))
    )
);

evaluator_test!(
    strings,
    (
        r#""Hello World!""#,
        Ok(Object::String("Hello World!".into()))
    ),
    (
        r#""Hello" + " " + "World!""#,
        Ok(Object::String("Hello World!".into()))
    )
);

evaluator_test!(
    string_builtins,
    ("len(\"\")", Ok(Object::Integer(0))),
    ("len(\"four\")", Ok(Object::Integer(4))),
    ("len(\"hello world\")", Ok(Object::Integer(11))),
    ("len(1)", Err("Wrong argument to 'len'. Got INTEGER".into())),
    (
        "len(\"one\", \"two\")",
        Err("Wrong number of arguments to 'len'. Expected 1, got 2".into())
    )
);

evaluator_test!(
    array_literal,
    (
        "[1, 2 * 2, 3 + 3]",
        Ok(Object::Array(vec![
            Object::Integer(1),
            Object::Integer(4),
            Object::Integer(6),
        ]))
    )
);

evaluator_test!(
    array_index,
    ("[1, 2, 3][0]", Ok(Object::Integer(1))),
    ("[1, 2, 3][1]", Ok(Object::Integer(2))),
    ("[1, 2, 3][2]", Ok(Object::Integer(3))),
    ("let i = 0; [1][i];", Ok(Object::Integer(1))),
    ("[1, 2, 3][1 + 1];", Ok(Object::Integer(3))),
    (
        "let myArray = [1, 2, 3]; myArray[2];",
        Ok(Object::Integer(3))
    ),
    (
        "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
        Ok(Object::Integer(6))
    ),
    (
        "let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]",
        Ok(Object::Integer(2))
    ),
    ("[1, 2, 3][3]", Err("Index out of bounds: 3".into())),
    ("[1, 2, 3][-1]", Err("Index out of bounds: -1".into()))
);

evaluator_test!(
    array_builtins,
    ("let a = [1, 2, 3]; len(a)", Ok(Object::Integer(3))),
    ("let a = [1, 2, 3]; first(a)", Ok(Object::Integer(1))),
    ("let a = [1, 2, 3]; last(a)", Ok(Object::Integer(3))),
    (
        "let a = [1, 2, 3]; rest(a)",
        Ok(Object::Array(vec![Object::Integer(2), Object::Integer(3)]))
    ),
    (
        "let a = [1, 2, 3]; rest(rest(a))",
        Ok(Object::Array(vec![Object::Integer(3)]))
    ),
    (
        "let a = [1, 2, 3]; rest(rest(rest(a)))",
        Ok(Object::Array(vec![]))
    ),
    (
        "let a = [1, 2, 3]; rest(rest(rest(rest(a))))",
        Ok(Object::Null)
    ),
    (
        "let a = [1, 2, 3]; push(a, 4)",
        Ok(Object::Array(vec![
            Object::Integer(1),
            Object::Integer(2),
            Object::Integer(3),
            Object::Integer(4),
        ]))
    )
);

evaluator_test!(
    map_reduce,
    (
        "let map = fn (arr, f) {
            let iter = fn (arr, accumulated) {
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
        map(a, double);",
        Ok(Object::Array(vec![
            Object::Integer(2),
            Object::Integer(4),
            Object::Integer(6),
            Object::Integer(8),
        ]))
    ),
    (
        "let reduce = fn (arr, initial, f) {
            let iter = fn (arr, result) {
                if (len(arr) == 0) {
                    result
                } else {
                    iter(rest(arr), f(result, first(arr)));
                }
            };
            iter(arr, initial);
        };
        let a = [1, 2, 3, 4];
        let sum = fn (x, y) { x + y };
        reduce(a, 0, sum);",
        Ok(Object::Integer(10))
    )
);

evaluator_test!(
    hash_literal,
    (
        r#"let two = "two";
    {
        "one": 10 - 9,
        two: 1 + 1,
        "thr" + "ee": 6 / 2,
        4: 4,
        true: 5,
        false: 6
    }
    "#,
        Ok(Object::Hash(
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
        ))
    )
);

evaluator_test!(
    illegal_hash_key,
    (
        r#"let badKey = fn() {};{ badKey: 1 }"#,
        Err("Unusable as hash key: FUNCTION".into())
    )
);

evaluator_test!(
    hash_index,
    (r#"let a = {"foo": 5}; a["foo"] "#, Ok(Object::Integer(5))),
    (r#"let a = {"foo": 5}; a["bar"] "#, Ok(Object::Null)),
    (r#"let a = {"foo": 5}; a[5] "#, Ok(Object::Null)),
    (
        r#" let key = "foo"; {key: 5}["foo"] "#,
        Ok(Object::Integer(5))
    ),
    (r#"{}["foo"] "#, Ok(Object::Null)),
    (r#"{5: 5}[5] "#, Ok(Object::Integer(5))),
    (r#"{true: 5}[true] "#, Ok(Object::Integer(5))),
    (r#"{false: 5}[false] "#, Ok(Object::Integer(5))),
    (
        r#"{"name": "Monkey"}[fn(x) { x }];"#,
        Err("Unusable as hash key: FUNCTION".into())
    )
);

#[macro_export]
macro_rules! evaluator_test {
    ($test_name:ident, $(($input:expr, $output:expr)),+) => {
        #[test]
        fn $test_name() {
            $(evaluator_test_input($input, $output);)*
        }
    };
}

fn evaluator_test_input(input: &str, expected: EvalResult) {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse().unwrap();
    let mut env = Rc::new(RefCell::new(Environment::default()));
    let evaluated = eval(program, &mut env);
    assert_eq!(evaluated, expected);
}
