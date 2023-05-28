use crate::{ast::*, lexer::Lexer, token::Token};

#[derive(PartialEq, PartialOrd)]
pub enum Precedence {
    Lowest = 1,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

fn parse_ident(p: &mut Parser) -> Option<Expression> {
    let name = if let Token::Ident(s) = &p.cur_token {
        s.clone()
    } else {
        unreachable!()
    };
    Some(Expression::Identifier(Identifier { name }))
}

fn parse_integer_literal(p: &mut Parser) -> Option<Expression> {
    let value = if let Token::Int(i) = &p.cur_token {
        i
    } else {
        unreachable!()
    };
    Some(Expression::Integer(
        value.parse().expect("Failed to parse integer"),
    ))
}

fn prefix_parse_fn(t: &Token) -> Option<fn(&mut Parser) -> Option<Expression>> {
    match t {
        Token::Ident(_) => Some(parse_ident),
        Token::Int(_) => Some(parse_integer_literal),
        _ => None,
    }
}

fn infix_parse_fn(t: &Token) -> Option<fn(&mut Parser, &Expression) -> Option<Expression>> {
    match t {
        _ => None,
    }
}

pub struct Parser {
    lexer: Lexer,

    cur_token: Token,
    peek_token: Token,

    errors: Vec<String>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let mut s = Self {
            lexer,
            cur_token: Token::Illegal,
            peek_token: Token::Illegal,

            errors: vec![],
        };
        s.next_token();
        s.next_token();
        s
    }

    pub fn parse(&mut self) -> Node {
        let mut program = vec![];

        while !self.cur_token.same_variant(&Token::Eof) {
            if let Some(stmt) = self.parse_statement() {
                program.push(stmt);
            }
            self.next_token();
        }

        Node::Root(program)
    }
}

impl Parser {
    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next();
    }

    fn parse_statement(&mut self) -> Option<Statement> {
        match self.cur_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_ret_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression_statement(&mut self) -> Option<Statement> {
        let expression = self.parse_expression(Precedence::Lowest)?;
        if self.peek_token_is(&Token::Semicolon) {
            self.next_token();
        }

        return Some(Statement::Expression { value: expression });
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Option<Expression> {
        let prefix = prefix_parse_fn(&self.cur_token)?;

        prefix(self)
    }

    fn parse_ret_statement(&mut self) -> Option<Statement> {
        while !self.cur_token_is(&Token::Semicolon) {
            self.next_token();
        }

        Some(Statement::Return {
            value: Expression::None,
        })
    }

    fn parse_let_statement(&mut self) -> Option<Statement> {
        if !self.expect_peek(&Token::Ident("".into())) {
            return None;
        }
        let ident = if let Token::Ident(s) = &self.cur_token {
            s.clone()
        } else {
            unreachable!()
        };

        if !self.expect_peek(&Token::Assign) {
            return None;
        }

        while !self.cur_token_is(&Token::Semicolon) {
            self.next_token();
        }

        Some(Statement::Let {
            ident: Identifier { name: ident },
            value: Expression::None,
        })
    }

    fn cur_token_is(&self, t: &Token) -> bool {
        self.cur_token.same_variant(t)
    }

    fn peek_token_is(&self, t: &Token) -> bool {
        self.peek_token.same_variant(t)
    }

    fn expect_peek(&mut self, t: &Token) -> bool {
        if self.peek_token_is(t) {
            self.next_token();
            true
        } else {
            self.peek_error(t);
            false
        }
    }

    fn peek_error(&mut self, t: &Token) {
        self.errors.push(format!(
            "Expected next token to be {:?}, got {:?}",
            t, self.peek_token
        ))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn check_errors(p: &Parser) {
        assert_eq!(
            p.errors.len(),
            0,
            "Parser had {} errors:\n{:?}",
            p.errors.len(),
            p.errors
        );
    }

    #[test]
    fn let_statements() {
        let input = "let x = 5;
let y = 10;
let foobar = 323232;";

        let mut parser = Parser::new(Lexer::new(&input));
        if let Node::Root(statements) = parser.parse() {
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
        if let Node::Root(statements) = parser.parse() {
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
        let program = Node::Root(vec![
            Statement::Let {
                ident: Identifier::new("var_1"),
                value: Expression::Identifier(Identifier::new("var_2")),
            },
            Statement::Return {
                value: Expression::Identifier(Identifier::new("var_1")),
            },
        ]);

        assert_eq!(program.to_string(), "let var_1 = var_2;\nreturn var_1;\n");
    }

    #[test]
    fn identifier_expression() {
        let input = "foobar;";

        let mut parser = Parser::new(Lexer::new(input));
        if let Node::Root(statements) = parser.parse() {
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
        if let Node::Root(statements) = parser.parse() {
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
}
