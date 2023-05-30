use super::*;

#[test]
fn let_statements() {
    let input = "let x = 5;
let y = true;
let foobar = y;";

    let mut parser = Parser::new(Lexer::new(&input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
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
fn return_statements() {
    let input = "return 5;
return true;
return fn (x) { x + 10; };";

    let mut parser = Parser::new(Lexer::new(&input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
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
fn to_string() {
    let program = Node::Root(Block {
        statements: vec![
            Statement::Let {
                ident: Identifier::new("var_1"),
                value: Expression::Identifier(Identifier::new("var_2")),
            },
            Statement::Return {
                value: Expression::Identifier(Identifier::new("var_1")),
            },
        ],
    });

    assert_eq!(program.to_string(), "let var_1 = var_2;\nreturn var_1;\n");
}
