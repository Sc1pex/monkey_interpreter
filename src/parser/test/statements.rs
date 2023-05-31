use super::*;

#[test]
fn let_statements() -> TestResult {
    let input = "let x = 5;
let y = true;
let foobar = y;";
    let expected = Block {
        statements: vec![
            Statement::Let {
                ident: Identifier::new("x"),
                value: Expression::Integer(5),
            },
            Statement::Let {
                ident: Identifier::new("y"),
                value: Expression::Boolean(true),
            },
            Statement::Let {
                ident: Identifier::new("foobar"),
                value: Expression::Identifier(Identifier::new("y")),
            },
        ],
    };

    test(input, expected)
}

#[test]
fn return_statements() -> TestResult {
    let input = "return 5;
return true;
return fn (x) { x + 10; };";
    let expected = Block {
        statements: vec![
            Statement::Return {
                value: Expression::Integer(5),
            },
            Statement::Return {
                value: Expression::Boolean(true),
            },
            Statement::Return {
                value: Expression::FunctionLiteral {
                    params: vec![Identifier::new("x")],
                    body: Block {
                        statements: vec![Statement::Expression {
                            value: Expression::Infix {
                                left: Box::new(Expression::Identifier(Identifier::new("x"))),
                                operator: InfixOperator::Add,
                                right: Box::new(Expression::Integer(10)),
                            },
                        }],
                    },
                },
            },
        ],
    };

    test(input, expected)
}

#[test]
fn to_string() {
    let program = Block {
        statements: vec![
            Statement::Let {
                ident: Identifier::new("var_1"),
                value: Expression::Identifier(Identifier::new("var_2")),
            },
            Statement::Return {
                value: Expression::Identifier(Identifier::new("var_1")),
            },
        ],
    };

    assert_eq!(program.to_string(), "let var_1 = var_2;\nreturn var_1;\n");
}
