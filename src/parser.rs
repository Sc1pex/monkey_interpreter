use crate::lexer::{Lexer, Token};
use std::fmt::Display;

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(String, Expression),
    Return(Expression),
    Expression(Expression),
    Block(Vec<Statement>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Ident(String),
    Int(i64),
    Boolean(bool),
    If(Box<Expression>, Box<Statement>, Option<Box<Statement>>),
    Prefix(Token, Box<Expression>),
    Infix(Box<Expression>, Token, Box<Expression>),
    Function(Vec<Expression>, Box<Statement>),
    Call(Box<Expression>, Vec<Expression>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Lowest,
    Equal,
    GtLt,
    Sum,
    Product,
    Prefix,
    Call,
}

pub struct Program(pub Vec<Statement>);

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for s in &self.0 {
            writeln!(f, "{s}")?;
        }
        Ok(())
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let(i, e) => write!(f, "let {} = {};", i, e),
            Statement::Return(e) => write!(f, "return {};", e),
            Statement::Expression(e) => write!(f, "{}", e),
            Statement::Block(v) => {
                writeln!(f, "{{")?;
                for s in v {
                    writeln!(f, "{s}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Ident(i) => write!(f, "{}", i),
            Expression::Int(i) => write!(f, "{}", i),
            Expression::Boolean(b) => write!(f, "{}", b),
            Expression::Prefix(op, expr) => write!(f, "({}{})", op, expr),
            Expression::Infix(left, op, right) => write!(f, "({} {} {})", left, op, right),
            Expression::If(cond, cons, alt) => {
                write!(f, "if ({}) {}", cond, cons)?;
                if let Some(alt) = alt {
                    write!(f, " else {}", alt)?;
                }
                Ok(())
            }
            Expression::Function(args, body) => {
                write!(f, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}", arg)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") {}", body)
            }
            Expression::Call(func, args) => {
                write!(f, "{}(", func)?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}", arg)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

pub struct Parser {
    lexer: Lexer,

    cur_token: Token,
    peek_token: Token,
}

fn token_precedence(t: &Token) -> Precedence {
    match t {
        Token::Eq | Token::NotEq => Precedence::Equal,
        Token::Lt | Token::Gt => Precedence::GtLt,
        Token::Plus | Token::Minus => Precedence::Sum,
        Token::Asterisk | Token::Slash => Precedence::Product,
        Token::LParen => Precedence::Call,
        _ => Precedence::Lowest,
    }
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
            Ok(Program(program))
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
            Token::LBrace => {
                self.next_token();
                let mut statements = vec![];

                while !matches!(self.cur_token, Token::RBrace) {
                    statements.push(self.parse_statement()?);
                    self.next_token();
                }
                Ok(Statement::Block(statements))
            }
            _ => self.parse_expression_statement(),
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

        self.next_token();
        let expr = self.parse_expression(Precedence::Lowest)?;
        if !expect_peek!(self, Token::Semicolon) {
            return Err(format!("Expected ;, got {:?}", self.peek_token));
        }

        Ok(Statement::Let(ident, expr))
    }

    fn parse_return_statement(&mut self) -> Result<Statement, String> {
        self.next_token();
        let expr = self.parse_expression(Precedence::Lowest)?;
        if !expect_peek!(self, Token::Semicolon) {
            return Err(format!("Expected ;, got {:?}", self.peek_token));
        }

        Ok(Statement::Return(expr))
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, String> {
        let expr = self.parse_expression(Precedence::Lowest)?;

        if matches!(self.peek_token, Token::Semicolon) {
            self.next_token();
        }

        Ok(Statement::Expression(expr))
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression, String> {
        let mut expr = self.parse_prefix_expression()?;

        while !matches!(self.peek_token, Token::Semicolon)
            && precedence < token_precedence(&self.peek_token)
        {
            self.next_token();

            expr = self.parse_infix_expression(Box::new(expr))?;
        }

        Ok(expr)
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression, String> {
        match &self.cur_token {
            Token::Ident(i) => Ok(Expression::Ident(i.clone())),
            Token::Int(x) => Ok(Expression::Int(*x)),
            Token::True => Ok(Expression::Boolean(true)),
            Token::False => Ok(Expression::Boolean(false)),
            Token::Bang | Token::Minus => {
                let op = self.cur_token.clone();
                self.next_token();

                let expr = self.parse_expression(Precedence::Prefix)?;
                Ok(Expression::Prefix(op, Box::new(expr)))
            }
            Token::LParen => {
                self.next_token();
                let expr = self.parse_expression(Precedence::Lowest)?;
                if !expect_peek!(self, Token::RParen) {
                    return Err(format!("Expected ), got {:?}", self.peek_token));
                }
                Ok(expr)
            }
            Token::If => {
                if !expect_peek!(self, Token::LParen) {
                    return Err(format!("Expected (, got {:?}", self.peek_token));
                }
                let cond = self.parse_expression(Precedence::Lowest)?;
                if !matches!(self.cur_token, Token::RParen) {
                    return Err(format!("Expected ), got {:?}", self.cur_token));
                }
                self.next_token();

                let block = self.parse_statement()?;
                if !matches!(block, Statement::Block(_)) {
                    return Err(format!("Expected block, got {:?}", block));
                }
                let else_block = if matches!(self.peek_token, Token::Else) {
                    self.next_token();
                    self.next_token();

                    let block = self.parse_statement()?;
                    if !matches!(block, Statement::Block(_)) {
                        return Err(format!("Expected block, got {:?}", block));
                    }
                    Some(Box::new(block))
                } else {
                    None
                };

                Ok(Expression::If(Box::new(cond), Box::new(block), else_block))
            }
            Token::Function => {
                if !expect_peek!(self, Token::LParen) {
                    return Err(format!("Expected (, got {:?}", self.peek_token));
                }
                let mut args = vec![];
                while !matches!(self.peek_token, Token::RParen) {
                    self.next_token();
                    let expr = self.parse_expression(Precedence::Lowest)?;
                    if !matches!(expr, Expression::Ident(_)) {
                        return Err(format!("Expected identifier, got {:?}", expr));
                    }
                    args.push(expr);

                    if !matches!(self.peek_token, Token::RParen)
                        && !expect_peek!(self, Token::Comma)
                    {
                        return Err(format!("Expected , or ), got {:?}", self.peek_token));
                    }
                }
                self.next_token();
                self.next_token();

                let block = self.parse_statement()?;
                if !matches!(block, Statement::Block(_)) {
                    return Err(format!("Expected block, got {:?}", block));
                }

                Ok(Expression::Function(args, Box::new(block)))
            }
            e => Err(format!("Unknown prefix expression: {e:?}")),
        }
    }

    fn parse_infix_expression(&mut self, right: Box<Expression>) -> Result<Expression, String> {
        match self.cur_token {
            Token::Plus
            | Token::Minus
            | Token::Asterisk
            | Token::Slash
            | Token::Gt
            | Token::Lt
            | Token::Eq
            | Token::NotEq => {
                let op = self.cur_token.clone();
                self.next_token();

                Ok(Expression::Infix(
                    right,
                    op.clone(),
                    Box::new(self.parse_expression(token_precedence(&op))?),
                ))
            }
            Token::LParen => {
                println!("AAAAAAAAAAAAAAAA");
                let mut args = vec![];
                while !matches!(self.peek_token, Token::RParen) {
                    self.next_token();
                    args.push(self.parse_expression(Precedence::Lowest)?);

                    if !matches!(self.peek_token, Token::RParen)
                        && !expect_peek!(self, Token::Comma)
                    {
                        return Err(format!("Expected , or ), got {:?}", self.peek_token));
                    }
                }
                self.next_token();

                Ok(Expression::Call(right, args))
            }
            _ => Err(format!("Unknown infix expression: {:?}", self.cur_token)),
        }
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
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![
            Statement::Let("x".into(), Expression::Int(30)),
            Statement::Let("foobar".into(), Expression::Int(231269)),
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
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![
            Statement::Return(Expression::Int(5)),
            Statement::Return(Expression::Int(231269)),
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
    fn ident_expression() {
        let input = "bazbar";

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![Statement::Expression(Expression::Ident("bazbar".into()))];
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
    fn integer_expression() {
        let input = "5";

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![Statement::Expression(Expression::Int(5))];
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
    fn bool_expresion() {
        let input = "true; false";

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = vec![
            Statement::Expression(Expression::Boolean(true)),
            Statement::Expression(Expression::Boolean(false)),
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
    fn prefix_expression() {
        let input = "!5; -10";

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [
            Statement::Expression(Expression::Prefix(
                Token::Bang,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Prefix(
                Token::Minus,
                Box::new(Expression::Int(10)),
            )),
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
    fn infix_expression() {
        let input = r#"
            5 + 5;
            5 - 5;
            5 * 5;
            5 / 5;
            5 > 5;
            5 < 5;
            5 == 5;
            5 != 5;
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Plus,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Minus,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Asterisk,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Slash,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Gt,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Lt,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::Eq,
                Box::new(Expression::Int(5)),
            )),
            Statement::Expression(Expression::Infix(
                Box::new(Expression::Int(5)),
                Token::NotEq,
                Box::new(Expression::Int(5)),
            )),
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
    fn block_expression() {
        let input = r#"
        {
            let a = 10;
            {
                let c = 40;
            }
            let b = 20;
            {
                {
                    let d = 30;
                }
            }
            return 1;
        }
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [Statement::Block(vec![
            Statement::Let("a".to_string(), Expression::Int(10)),
            Statement::Block(vec![Statement::Let("c".to_string(), Expression::Int(40))]),
            Statement::Let("b".to_string(), Expression::Int(20)),
            Statement::Block(vec![Statement::Block(vec![Statement::Let(
                "d".to_string(),
                Expression::Int(30),
            )])]),
            Statement::Return(Expression::Int(1)),
        ])];

        assert_eq!(
            program.len(),
            expected.len(),
            "Program does not contain {} statements. got={}",
            expected.len(),
            program.len()
        );
        assert_eq!(program[0], expected[0]);
    }

    #[test]
    fn if_else_expression() {
        let input = r#"
        if (a == 2) {
            let b = 10;
        } else {
            let c = 20;
        }
        if (d == 4) {
            let b = 20;
        }
        let c = 40;
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [
            Statement::Expression(Expression::If(
                Box::new(Expression::Infix(
                    Box::new(Expression::Ident("a".to_string())),
                    Token::Eq,
                    Box::new(Expression::Int(2)),
                )),
                Box::new(Statement::Block(vec![Statement::Let(
                    "b".to_string(),
                    Expression::Int(10),
                )])),
                Some(Box::new(Statement::Block(vec![Statement::Let(
                    "c".to_string(),
                    Expression::Int(20),
                )]))),
            )),
            Statement::Expression(Expression::If(
                Box::new(Expression::Infix(
                    Box::new(Expression::Ident("d".to_string())),
                    Token::Eq,
                    Box::new(Expression::Int(4)),
                )),
                Box::new(Statement::Block(vec![Statement::Let(
                    "b".to_string(),
                    Expression::Int(20),
                )])),
                None,
            )),
            Statement::Let("c".to_string(), Expression::Int(40)),
        ];

        assert_eq!(
            program.len(),
            expected.len(),
            "Program does not contain {} statements. got={}",
            expected.len(),
            program.len()
        );
        assert_eq!(program[0], expected[0]);
    }

    #[test]
    fn function_expression() {
        let input = r#"
            fn(x, y) {
                x + y;
            }
            fn (a, b, c) {
                let d = a * b;
                return d + c;
            }
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [
            Statement::Expression(Expression::Function(
                vec![
                    Expression::Ident("x".to_string()),
                    Expression::Ident("y".to_string()),
                ],
                Box::new(Statement::Block(vec![Statement::Expression(
                    Expression::Infix(
                        Box::new(Expression::Ident("x".to_string())),
                        Token::Plus,
                        Box::new(Expression::Ident("y".to_string())),
                    ),
                )])),
            )),
            Statement::Expression(Expression::Function(
                vec![
                    Expression::Ident("a".to_string()),
                    Expression::Ident("b".to_string()),
                    Expression::Ident("c".to_string()),
                ],
                Box::new(Statement::Block(vec![
                    Statement::Let(
                        "d".to_string(),
                        Expression::Infix(
                            Box::new(Expression::Ident("a".to_string())),
                            Token::Asterisk,
                            Box::new(Expression::Ident("b".to_string())),
                        ),
                    ),
                    Statement::Return(Expression::Infix(
                        Box::new(Expression::Ident("d".to_string())),
                        Token::Plus,
                        Box::new(Expression::Ident("c".to_string())),
                    )),
                ])),
            )),
        ];

        assert_eq!(
            program.len(),
            expected.len(),
            "Program does not contain {} statements. got={}",
            expected.len(),
            program.len()
        );
        assert_eq!(program[0], expected[0]);
    }

    #[test]
    fn call_expression() {
        let input = r#"
            add(1, 2, 3);
            add(1, 2 * 3, 4 + 5);
            fn(x, y) {
                x + y;
            }(1, 2);
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let Program(program) = parser.parse_program().unwrap_or_else(|v| {
            panic!(
                "\nParser had {} errors:\n{}",
                v.len(),
                v.into_iter()
                    .map(|s| s + "\n")
                    .fold(String::new(), |a, b| a + &b)
            )
        });

        let expected = [
            Statement::Expression(Expression::Call(
                Box::new(Expression::Ident("add".to_string())),
                vec![Expression::Int(1), Expression::Int(2), Expression::Int(3)],
            )),
            Statement::Expression(Expression::Call(
                Box::new(Expression::Ident("add".to_string())),
                vec![
                    Expression::Int(1),
                    Expression::Infix(
                        Box::new(Expression::Int(2)),
                        Token::Asterisk,
                        Box::new(Expression::Int(3)),
                    ),
                    Expression::Infix(
                        Box::new(Expression::Int(4)),
                        Token::Plus,
                        Box::new(Expression::Int(5)),
                    ),
                ],
            )),
            Statement::Expression(Expression::Call(
                Box::new(Expression::Function(
                    vec![
                        Expression::Ident("x".to_string()),
                        Expression::Ident("y".to_string()),
                    ],
                    Box::new(Statement::Block(vec![Statement::Expression(
                        Expression::Infix(
                            Box::new(Expression::Ident("x".to_string())),
                            Token::Plus,
                            Box::new(Expression::Ident("y".to_string())),
                        ),
                    )])),
                )),
                vec![Expression::Int(1), Expression::Int(2)],
            )),
        ];

        assert_eq!(
            program.len(),
            expected.len(),
            "Program does not contain {} statements. got={}",
            expected.len(),
            program.len()
        );
        assert_eq!(program[0], expected[0]);
    }

    #[test]
    fn operator_precedence() {
        let tests = [
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)\n((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
        ];

        for (input, expected) in tests {
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

            assert_eq!(program.to_string().trim_end(), expected);
        }
    }
}
