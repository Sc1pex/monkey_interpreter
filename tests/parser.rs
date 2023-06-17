use interpreter::{ast::*, lexer::Lexer, parser::Parser};

mod common;

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

#[test]
fn opearator_precedence() {
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
        let r = parser.parse().unwrap().to_string();
        assert_eq!(r, t.1);
    }
}

// Tests for statements

parser_test!(
    let_statements,
    (
        "let x = 5;
        let y = true;
        let foobar = y;",
        Block {
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
        }
    )
);

parser_test!(
    return_statements,
    (
        "return 5;
return true;
return fn (x) { x + 10; };",
        Block {
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
        }
    )
);

// Tests for expressions

parser_test!(
    identifier_expression,
    (
        "foobar;",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::Identifier(Identifier::new("foobar")),
            }],
        }
    )
);

parser_test!(
    integer_literal_expression,
    (
        "5;6;",
        Block {
            statements: vec![
                Statement::Expression {
                    value: Expression::Integer(5),
                },
                Statement::Expression {
                    value: Expression::Integer(6),
                },
            ],
        }
    )
);

parser_test!(
    boolean_literal_expression,
    (
        "true;false;",
        Block {
            statements: vec![
                Statement::Expression {
                    value: Expression::Boolean(true),
                },
                Statement::Expression {
                    value: Expression::Boolean(false),
                },
            ],
        }
    )
);

parser_test!(
    prefix_expression,
    (
        "!5;-15;!true;!false",
        Block {
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
        }
    )
);

parser_test!(
    infix_expression,
    (
        "5 + 5
5 - 5
10 * 20
12 / 7
3 > 1
23 < 3
10 == 10
5 != 5
true == true
false != true",
        Block {
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
        }
    )
);

parser_test!(
    if_expression,
    (
        "if (x != y) { x }",
        Block {
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
        }
    )
);

parser_test!(
    if_else_expression,
    (
        "if (x != y) { x } else { y }",
        Block {
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
        }
    )
);

parser_test!(
    function_literal,
    (
        "fn (a, b, c) {a * b;}",
        Block {
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
        }
    )
);

parser_test!(
    function_parameters,
    (
        "fn () {}",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: vec![],
                    body: Block { statements: vec![] }
                }
            }]
        }
    ),
    (
        "fn (a) {}",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: vec![Identifier::new("a")],
                    body: Block { statements: vec![] }
                }
            }]
        }
    ),
    (
        "fn (a, b) {}",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: vec![Identifier::new("a"), Identifier::new("b")],
                    body: Block { statements: vec![] }
                }
            }]
        }
    ),
    (
        "fn (a, b, c, d) {}",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::FunctionLiteral {
                    params: vec![
                        Identifier::new("a"),
                        Identifier::new("b"),
                        Identifier::new("c"),
                        Identifier::new("d"),
                    ],
                    body: Block { statements: vec![] }
                }
            }]
        }
    )
);

parser_test!(
    call_expression,
    (
        "add(1, 2 * 3, 4 + 5);",
        Block {
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
        }
    )
);

parser_test!(
    string_literal,
    (
        "\"hello world\"",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::StringLiteral("hello world".to_string()),
            }],
        }
    )
);

parser_test!(
    array_literal,
    (
        "[1, 2 * 2, 3 + 3]",
        Block {
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
        }
    )
);

parser_test!(
    array_index,
    (
        "myArray[1 + 1]",
        Block {
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
        }
    )
);

parser_test!(
    hash_literals,
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
        }
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
        }
    ),
    (
        "{}",
        Block {
            statements: vec![Statement::Expression {
                value: Expression::HashLiteral { pairs: vec![] },
            }],
        }
    )
);
