use super::*;

#[test]
fn identifier_expression() -> TestResult {
    let input = "foobar;";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::Identifier(Identifier::new("foobar")),
        }],
    };

    test(input, expected)
}

#[test]
fn integer_literal_expression() -> TestResult {
    let input = "5;6;";
    let expected = Block {
        statements: vec![
            Statement::Expression {
                value: Expression::Integer(5),
            },
            Statement::Expression {
                value: Expression::Integer(6),
            },
        ],
    };

    test(input, expected)
}

#[test]
fn boolean_literal_expression() -> TestResult {
    let input = "true;false;";
    let expected = Block {
        statements: vec![
            Statement::Expression {
                value: Expression::Boolean(true),
            },
            Statement::Expression {
                value: Expression::Boolean(false),
            },
        ],
    };

    test(input, expected)
}

#[test]
fn prefix_expression() -> TestResult {
    let input = "!5;-15;!true;!false";
    let expected = Block {
        statements: vec![
            Statement::Expression {
                value: Expression::Prefix {
                    operator: PrefixOperator::Not,
                    right: Box::new(Expression::Integer(5)),
                },
            },
            Statement::Expression {
                value: Expression::Prefix {
                    operator: PrefixOperator::Negate,
                    right: Box::new(Expression::Integer(15)),
                },
            },
            Statement::Expression {
                value: Expression::Prefix {
                    operator: PrefixOperator::Not,
                    right: Box::new(Expression::Boolean(true)),
                },
            },
            Statement::Expression {
                value: Expression::Prefix {
                    operator: PrefixOperator::Not,
                    right: Box::new(Expression::Boolean(false)),
                },
            },
        ],
    };

    test(input, expected)
}

#[test]
fn infix_expression() -> TestResult {
    let input = "5 + 5
5 - 5
10 * 20
12 / 7
3 > 1
23 < 3
10 == 10
5 != 5
true == true
false != true";
    let expected = Block {
        statements: vec![
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Add,
                    left: Box::new(Expression::Integer(5)),
                    right: Box::new(Expression::Integer(5)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Subtract,
                    left: Box::new(Expression::Integer(5)),
                    right: Box::new(Expression::Integer(5)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Multiply,
                    left: Box::new(Expression::Integer(10)),
                    right: Box::new(Expression::Integer(20)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Divide,
                    left: Box::new(Expression::Integer(12)),
                    right: Box::new(Expression::Integer(7)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::GreaterThan,
                    left: Box::new(Expression::Integer(3)),
                    right: Box::new(Expression::Integer(1)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::LessThan,
                    left: Box::new(Expression::Integer(23)),
                    right: Box::new(Expression::Integer(3)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Equal,
                    left: Box::new(Expression::Integer(10)),
                    right: Box::new(Expression::Integer(10)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::NotEqual,
                    left: Box::new(Expression::Integer(5)),
                    right: Box::new(Expression::Integer(5)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::Equal,
                    left: Box::new(Expression::Boolean(true)),
                    right: Box::new(Expression::Boolean(true)),
                },
            },
            Statement::Expression {
                value: Expression::Infix {
                    operator: InfixOperator::NotEqual,
                    left: Box::new(Expression::Boolean(false)),
                    right: Box::new(Expression::Boolean(true)),
                },
            },
        ],
    };

    test(input, expected)
}

#[test]
fn if_expression() -> TestResult {
    let input = "if (x != y) { x }";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::If {
                condition: Box::new(Expression::Infix {
                    operator: InfixOperator::NotEqual,
                    left: Box::new(Expression::Identifier(Identifier::new("x"))),
                    right: Box::new(Expression::Identifier(Identifier::new("y"))),
                }),
                consequence: Block {
                    statements: vec![Statement::Expression {
                        value: Expression::Identifier(Identifier::new("x")),
                    }],
                },
                alternative: None,
            },
        }],
    };

    test(input, expected)
}

#[test]
fn if_else_expression() -> TestResult {
    let input = "if (x != y) { x } else { y }";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::If {
                condition: Box::new(Expression::Infix {
                    operator: InfixOperator::NotEqual,
                    left: Box::new(Expression::Identifier(Identifier::new("x"))),
                    right: Box::new(Expression::Identifier(Identifier::new("y"))),
                }),
                consequence: Block {
                    statements: vec![Statement::Expression {
                        value: Expression::Identifier(Identifier::new("x")),
                    }],
                },
                alternative: Some(Block {
                    statements: vec![Statement::Expression {
                        value: Expression::Identifier(Identifier::new("y")),
                    }],
                }),
            },
        }],
    };

    test(input, expected)
}

#[test]
fn function_literal() -> TestResult {
    let input = "fn (a, b, c) {a * b;}";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::FunctionLiteral {
                params: vec![
                    Identifier::new("a"),
                    Identifier::new("b"),
                    Identifier::new("c"),
                ],
                body: Block {
                    statements: vec![Statement::Expression {
                        value: Expression::Infix {
                            operator: InfixOperator::Multiply,
                            left: Box::new(Expression::Identifier(Identifier::new("a"))),
                            right: Box::new(Expression::Identifier(Identifier::new("b"))),
                        },
                    }],
                },
            },
        }],
    };

    test(input, expected)
}

#[test]
fn function_parameters() -> TestResult {
    let tests = [
        ("fn () {}", vec![]),
        ("fn (a) {}", vec![Identifier::new("a")]),
        (
            "fn (a, b) {}",
            vec![Identifier::new("a"), Identifier::new("b")],
        ),
        (
            "fn (a, b, c, d) {}",
            vec![
                Identifier::new("a"),
                Identifier::new("b"),
                Identifier::new("c"),
                Identifier::new("d"),
            ],
        ),
    ];

    for t in tests {
        let expected = Block {
            statements: vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: t.1,
                    body: Block { statements: vec![] },
                },
            }],
        };

        test(t.0, expected)?;
    }
    Ok(())
}

#[test]
fn call_expression() -> TestResult {
    let input = "add(1, 2 * 3, 4 + 5);";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::Call {
                function: Box::new(Expression::Identifier(Identifier::new("add"))),
                args: vec![
                    Expression::Integer(1),
                    Expression::Infix {
                        operator: InfixOperator::Multiply,
                        left: Box::new(Expression::Integer(2)),
                        right: Box::new(Expression::Integer(3)),
                    },
                    Expression::Infix {
                        operator: InfixOperator::Add,
                        left: Box::new(Expression::Integer(4)),
                        right: Box::new(Expression::Integer(5)),
                    },
                ],
            },
        }],
    };

    test(input, expected)
}

#[test]
fn string_literal() -> TestResult {
    let input = "\"hello world\"";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::StringLiteral("hello world".to_string()),
        }],
    };

    test(input, expected)
}

#[test]
fn array_literal() -> TestResult {
    let input = "[1, 2 * 2, 3 + 3]";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::ArrayLiteral {
                elements: vec![
                    Expression::Integer(1),
                    Expression::Infix {
                        operator: InfixOperator::Multiply,
                        left: Box::new(Expression::Integer(2)),
                        right: Box::new(Expression::Integer(2)),
                    },
                    Expression::Infix {
                        operator: InfixOperator::Add,
                        left: Box::new(Expression::Integer(3)),
                        right: Box::new(Expression::Integer(3)),
                    },
                ],
            },
        }],
    };

    test(input, expected)
}

#[test]
fn array_index() -> TestResult {
    let input = "myArray[1 + 1]";
    let expected = Block {
        statements: vec![Statement::Expression {
            value: Expression::Index {
                left: Box::new(Expression::Identifier(Identifier::new("myArray"))),
                index: Box::new(Expression::Infix {
                    operator: InfixOperator::Add,
                    left: Box::new(Expression::Integer(1)),
                    right: Box::new(Expression::Integer(1)),
                }),
            },
        }],
    };

    test(input, expected)
}

#[test]
fn hash_literals() -> TestResult {
    let tests = [
        (
            "{\"one\": 1, \"two\": 2, \"three\": 3}",
            Block {
                statements: vec![Statement::Expression {
                    value: Expression::HashLiteral {
                        pairs: vec![
                            (
                                Expression::StringLiteral("one".to_string()),
                                Expression::Integer(1),
                            ),
                            (
                                Expression::StringLiteral("two".to_string()),
                                Expression::Integer(2),
                            ),
                            (
                                Expression::StringLiteral("three".to_string()),
                                Expression::Integer(3),
                            ),
                        ],
                    },
                }],
            },
        ),
        (
            r#"{"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}"#,
            Block {
                statements: vec![Statement::Expression {
                    value: Expression::HashLiteral {
                        pairs: vec![
                            (
                                Expression::StringLiteral("one".to_string()),
                                Expression::Infix {
                                    operator: InfixOperator::Add,
                                    left: Box::new(Expression::Integer(0)),
                                    right: Box::new(Expression::Integer(1)),
                                },
                            ),
                            (
                                Expression::StringLiteral("two".to_string()),
                                Expression::Infix {
                                    operator: InfixOperator::Subtract,
                                    left: Box::new(Expression::Integer(10)),
                                    right: Box::new(Expression::Integer(8)),
                                },
                            ),
                            (
                                Expression::StringLiteral("three".to_string()),
                                Expression::Infix {
                                    operator: InfixOperator::Divide,
                                    left: Box::new(Expression::Integer(15)),
                                    right: Box::new(Expression::Integer(5)),
                                },
                            ),
                        ],
                    },
                }],
            },
        ),
        (
            "{}",
            Block {
                statements: vec![Statement::Expression {
                    value: Expression::HashLiteral { pairs: vec![] },
                }],
            },
        ),
    ];

    for t in tests {
        test(t.0, t.1)?;
    }
    Ok(())
}
