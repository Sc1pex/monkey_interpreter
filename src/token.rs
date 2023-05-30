use std::fmt::Display;

use crate::parser::Precedence;

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Token {
    Ident(String),
    Int(String),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,

    Lt,
    Gt,

    Eq,
    NotEq,

    // Delimiters
    Comma,
    Semicolon,

    LParen,
    RParen,
    LBrace,
    RBrace,

    // Keywords
    Let,
    Function,
    Return,
    If,
    Else,
    True,
    False,

    // Special
    Illegal,
    Eof,
}

impl Token {
    pub fn lookup(s: &[u8]) -> Token {
        match s {
            b"fn" => Token::Function,
            b"let" => Token::Let,
            b"if" => Token::If,
            b"else" => Token::Else,
            b"true" => Token::True,
            b"false" => Token::False,
            b"return" => Token::Return,
            _ => Token::Ident(String::from_utf8_lossy(s).into()),
        }
    }

    pub fn same_variant(&self, t: &Token) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(t)
    }

    pub fn precedence(&self) -> Precedence {
        match self {
            Token::Eq => Precedence::Equals,
            Token::NotEq => Precedence::Equals,
            Token::Lt => Precedence::LessGreater,
            Token::Gt => Precedence::LessGreater,
            Token::Plus => Precedence::Sum,
            Token::Minus => Precedence::Sum,
            Token::Slash => Precedence::Product,
            Token::Asterisk => Precedence::Product,
            Token::LParen => Precedence::Call,
            _ => Precedence::Lowest,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Ident(s) => write!(f, "{s}"),
            Token::Int(s) => write!(f, "{s}"),
            Token::Assign => write!(f, "="),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Bang => write!(f, "!"),
            Token::Asterisk => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::Eq => write!(f, "=="),
            Token::NotEq => write!(f, "!="),
            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Let => write!(f, "let"),
            Token::Function => write!(f, "fn"),
            Token::Return => write!(f, "return"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Illegal => write!(f, ""),
            Token::Eof => write!(f, ""),
        }
    }
}
