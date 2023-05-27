#[derive(Debug, PartialEq)]
pub enum Token {
    Ident(String),
    Int(String),

    // Operators
    Assign,
    Plus,

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

    // Special
    Illegal,
    Eof,
}

impl Token {
    pub fn lookup(s: &[u8]) -> Token {
        match s {
            b"fn" => Token::Function,
            b"let" => Token::Let,
            _ => Token::Ident(String::from_utf8_lossy(s).into()),
        }
    }
}
