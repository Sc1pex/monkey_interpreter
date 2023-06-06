use interpreter::{ast::*, lexer::Lexer, parser::Parser};

type TestResult = Result<(), Vec<String>>;

fn assert_expected(expected: Block, program: Block) {
    assert_eq!(expected.statements.len(), program.statements.len());
    for (e, s) in expected.statements.iter().zip(program.statements.iter()) {
        assert_eq!(e, s);
    }
}

fn test(input: &str, expected: Block) -> TestResult {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse()?;
    assert_expected(expected, program);
    Ok(())
}

#[test]
fn opearator_precedence() -> TestResult {
    let tests = vec![
        ("-a * b", "((-a) * b)\n"),
        ("!-a", "(!(-a))\n"),
        ("a + b + c", "((a + b) + c)\n"),
        ("a + b - c", "((a + b) - c)\n"),
        ("a * b * c", "((a * b) * c)\n"),
        ("a * b / c", "((a * b) / c)\n"),
        ("a + b / c", "(a + (b / c))\n"),
        ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)\n"),
        ("3 + 4; -5 * 5", "(3 + 4)\n((-5) * 5)\n"),
        ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))\n"),
        ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))\n"),
        (
            "3 + 4 * 5 == 3 * 1 + 4 * 5",
            "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))\n",
        ),
        ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)\n"),
        (
            "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
            "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))\n",
        ),
        (
            "a * [1, 2, 3, 4][b * c] * d",
            "((a * ([1, 2, 3, 4][(b * c)])) * d)\n",
        ),
        (
            "add(a * b[2], b[1], 2 * [1, 2][1])",
            "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))\n",
        ),
    ];

    for t in tests {
        let mut parser = Parser::new(Lexer::new(t.0));
        let r = parser.parse()?.to_string();
        assert_eq!(r, t.1);
    }

    Ok(())
}

// Tests for statements

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

// Tests for expressions

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
