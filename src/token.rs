#[derive(Debug, PartialEq)]
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
}
