use super::*;

#[test]
fn let_statements() {
    let input = "let x = 5;
let y = 10;
let foobar = 323232;";

    let mut parser = Parser::new(Lexer::new(&input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
            Statement::Let {
                ident: Identifier::new("x"),
                value: Expression::None,
            },
            Statement::Let {
                ident: Identifier::new("y"),
                value: Expression::None,
            },
            Statement::Let {
                ident: Identifier::new("foobar"),
                value: Expression::None,
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
return 10;
return 323232;";

    let mut parser = Parser::new(Lexer::new(&input));
    if let Node::Root(Block { statements }) = parser.parse() {
        check_errors(&parser);
        let expected = vec![
            Statement::Return {
                value: Expression::None,
            },
            Statement::Return {
                value: Expression::None,
            },
            Statement::Return {
                value: Expression::None,
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
