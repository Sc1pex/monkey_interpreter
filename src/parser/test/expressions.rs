use super::*;

#[test]
fn identifier_expression() {
    let input = "foobar;";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![Statement::Expression {
            value: Expression::Identifier(Identifier::new("foobar")),
        }];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn integer_literal_expression() {
    let input = "5;
6;";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
            Statement::Expression {
                value: Expression::Integer(5),
            },
            Statement::Expression {
                value: Expression::Integer(6),
            },
        ];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn boolean_literal_expression() {
    let input = "true;
false;";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
            Statement::Expression {
                value: Expression::Boolean(true),
            },
            Statement::Expression {
                value: Expression::Boolean(false),
            },
        ];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn prefix_expression() {
    let input = "!5;-15;!true;!false";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
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
        ];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn infix_expression() {
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

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
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
        ];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn if_expression() {
    let input = "if (x != y) { x }";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![Statement::Expression {
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
        }];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn if_else_expression() {
    let input = "if (x != y) { x } else { y }";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![Statement::Expression {
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
        }];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn function_literal() {
    let input = "fn (a, b, c) {a * b;}";

    let mut parser = Parser::new(Lexer::new(input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![Statement::Expression {
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
        }];

        assert_eq!(expected.len(), statements.len());
        for (e, s) in expected.iter().zip(statements.iter()) {
            assert_eq!(e, s);
        }
    } else {
        panic!("Parser did not return root node");
    }
}

#[test]
fn function_parameters() {
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
        let mut parser = Parser::new(Lexer::new(t.0));
        if let Node::Root(Block { statements }) = parser.parse() {
            check_errors(&parser);
            let expected = vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: t.1,
                    body: Block { statements: vec![] },
                },
            }];

            assert_eq!(expected.len(), statements.len());
            for (e, s) in expected.iter().zip(statements.iter()) {
                assert_eq!(e, s);
            }
        } else {
            panic!("Parser did not return root node");
        }
    }
}
