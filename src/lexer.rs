use crate::token::Token;

pub struct Lexer {
    input: Vec<u8>,
    pos: usize,
    read_pos: usize,
    ch: u8,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        let mut s = Self {
            input: input.as_bytes().into(),
            pos: 0,
            read_pos: 0,
            ch: 0,
        };
        s.read();

        s
    }

    pub fn next(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.ch {
            b'=' => {
                if self.peek_char() == b'=' {
                    self.read();
                    Token::Eq
                } else {
                    Token::Assign
                }
            }
            b'+' => Token::Plus,
            b',' => Token::Comma,
            b';' => Token::Semicolon,
            b':' => Token::Colon,
            b'{' => Token::LBrace,
            b'}' => Token::RBrace,
            b'(' => Token::LParen,
            b')' => Token::RParen,
            b'[' => Token::LBracket,
            b']' => Token::RBracket,
            b'!' => {
                if self.peek_char() == b'=' {
                    self.read();
                    Token::NotEq
                } else {
                    Token::Bang
                }
            }
            b'-' => Token::Minus,
            b'/' => Token::Slash,
            b'>' => Token::Gt,
            b'<' => Token::Lt,
            b'*' => Token::Asterisk,
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => return Token::lookup(self.read_ident()),
            b'0'..=b'9' => return Token::Int(String::from_utf8_lossy(self.read_number()).into()),
            b'"' => Token::String(self.read_string()),
            0 => Token::Eof,
            _ => Token::Illegal,
        };

        self.read();
        token
    }
}

impl Lexer {
    fn read(&mut self) {
        self.ch = *self.input.get(self.read_pos).unwrap_or(&0);
        self.pos = self.read_pos;
        self.read_pos += 1;
    }

    fn peek_char(&self) -> u8 {
        *self.input.get(self.read_pos).unwrap_or(&0)
    }

    fn read_ident(&mut self) -> &[u8] {
        let pos = self.pos;
        while matches!(self.ch, b'a'..=b'z' | b'A'..=b'Z' | b'_') {
            self.read();
        }

        &self.input[pos..self.pos]
    }

    fn read_number(&mut self) -> &[u8] {
        let pos = self.pos;
        while self.ch.is_ascii_digit() {
            self.read();
        }

        &self.input[pos..self.pos]
    }

    fn read_string(&mut self) -> String {
        let mut s = String::new();
        self.read();
        while self.ch != b'"' && self.ch != 0 {
            s.push(self.ch as char);
            self.read();
        }
        s
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_ascii_whitespace() {
            self.read();
        }
    }
}
