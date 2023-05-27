use crate::{ast::*, lexer::Lexer, token::Token};

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
            _ => None,
        }
    }

    fn parse_let_statement(&mut self) -> Option<Statement> {
        if !self.expect_peek(&Token::Ident("".into())) {
            return None;
        }
        let ident = self.cur_token.clone();

        if !self.expect_peek(&Token::Assign) {
            return None;
        }

        while !self.cur_token_is(&Token::Semicolon) {
            self.next_token();
        }

        Some(Statement::Let(LetStatement {
            ident,
            value: Expression {},
        }))
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
                Statement::Let(LetStatement {
                    ident: Token::Ident("x".into()),
                    value: Expression {},
                }),
                Statement::Let(LetStatement {
                    ident: Token::Ident("y".into()),
                    value: Expression {},
                }),
                Statement::Let(LetStatement {
                    ident: Token::Ident("foobar".into()),
                    value: Expression {},
                }),
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
