#![allow(dead_code)]

use crate::lexer::{Lexer, Token};

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(String, Expression),
    Return(Expression),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Todo,
}

pub type Program = Vec<Statement>;

pub struct Parser {
    lexer: Lexer,

    cur_token: Token,
    peek_token: Token,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let mut parser = Self {
            lexer,
            cur_token: Token::Illegal,
            peek_token: Token::Illegal,
        };

        parser.next_token();
        parser.next_token();

        parser
    }

    pub fn parse_program(&mut self) -> Result<Program, Vec<String>> {
        let mut program = vec![];
        let mut errors = vec![];

        while !matches!(self.cur_token, Token::Eof) {
            let statement = self.parse_statement();
            match statement {
                Ok(stmt) => program.push(stmt),
                Err(s) => errors.push(s),
            }
            self.next_token();
        }

        if errors.is_empty() {
            Ok(program)
        } else {
            Err(errors)
        }
    }
}

macro_rules! expect_peek {
    ($parser: ident, $token: pat) => {{
        if matches!($parser.peek_token, $token) {
            $parser.next_token();
            true
        } else {
            false
        }
    }};
}

impl Parser {
    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }

    fn parse_statement(&mut self) -> Result<Statement, String> {
        match self.cur_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => Err(format!("Unexpected token: {:?}", self.cur_token)),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Statement, String> {
        let ident = match &self.peek_token {
            Token::Ident(i) => i.clone(),
            t => return Err(format!("Expected identifier, got {t:?}")),
        };
        self.next_token();
        if !expect_peek!(self, Token::Assign) {
            return Err(format!("Expected =, got {:?}", self.peek_token));
        }

        // Skip the expression
        while !matches!(self.cur_token, Token::Semicolon) {
            self.next_token();
        }

        Ok(Statement::Let(ident, Expression::Todo))
    }

    fn parse_return_statement(&mut self) -> Result<Statement, String> {
        // Skip the expression
        while !matches!(self.cur_token, Token::Semicolon) {
            self.next_token();
        }

        Ok(Statement::Return(Expression::Todo))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn let_statement() {
        let input = r#"
            let x = 30;
            let foobar = 231269;
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![
            Statement::Let("x".into(), Expression::Todo),
            Statement::Let("foobar".into(), Expression::Todo),
        ];
        assert_eq!(
            program.len(),
            expected.len(),
            "Expected parsed program to contain {} statements, got {}",
            expected.len(),
            program.len()
        );

        for (e, s) in expected.iter().zip(program.iter()) {
            assert_eq!(e, s, "Expected {e:?}, got {s:?}");
        }
    }

    #[test]
    fn retrun_statement() {
        let input = r#"
            return 5;
            return 231269;
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![
            Statement::Return(Expression::Todo),
            Statement::Return(Expression::Todo),
        ];
        assert_eq!(
            program.len(),
            expected.len(),
            "Expected parsed program to contain {} statements, got {}",
            expected.len(),
            program.len()
        );

        for (_, stmt) in expected.iter().zip(program.iter()) {
            match stmt {
                Statement::Return(_) => {}
                _ => panic!("stmt is not Statement::Let. got={:?}", stmt),
            }
        }
    }
}
