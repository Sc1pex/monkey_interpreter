use crate::{ast::*, lexer::Lexer, token::Token};
use infix_expr::infix_parse_fn;
use prefix_expr::prefix_parse_fn;

#[cfg(test)]
mod test;

mod infix_expr;
mod prefix_expr;

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

        Node::Root(Block {
            statements: program,
        })
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

        Some(Statement::Expression { value: expression })
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Option<Expression> {
        let prefix = prefix_parse_fn(&self.cur_token).or_else(|| {
            self.prefix_parse_error(&self.cur_token.clone());
            None
        })?;
        let mut left = prefix(self)?;

        while !self.peek_token_is(&Token::Semicolon) && precedence < self.peek_precedence() {
            if let Some(infix) = infix_parse_fn(&self.peek_token) {
                self.next_token();
                left = infix(self, left)?;
            } else {
                return Some(left);
            }
        }

        Some(left)
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

    fn peek_precedence(&self) -> Precedence {
        self.peek_token.precedence()
    }

    fn cur_precedence(&self) -> Precedence {
        self.cur_token.precedence()
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

    fn prefix_parse_error(&mut self, t: &Token) {
        self.errors
            .push(format!("No prefix parse function for {:?}", t))
    }
}
