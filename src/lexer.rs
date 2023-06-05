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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basics() {
        let input = "=+(){},;";

        let mut lexer = Lexer::new(input);
        let expected = [
            Token::Assign,
            Token::Plus,
            Token::LParen,
            Token::RParen,
            Token::LBrace,
            Token::RBrace,
            Token::Comma,
            Token::Semicolon,
            Token::Eof,
        ];
        for t in expected {
            assert_eq!(t, lexer.next());
        }
    }

    #[test]
    fn basic_code() {
        let input = "let five = 5;
let ten = 10;

let add = fn(x, y) {
    x + y;
};

let result = add(five, ten);
\"foobar\"
\"foo bar\"
[1, 2];";

        let mut lexer = Lexer::new(input);
        let expected = [
            Token::Let,
            Token::Ident("five".into()),
            Token::Assign,
            Token::Int("5".into()),
            Token::Semicolon,
            Token::Let,
            Token::Ident("ten".into()),
            Token::Assign,
            Token::Int("10".into()),
            Token::Semicolon,
            Token::Let,
            Token::Ident("add".into()),
            Token::Assign,
            Token::Function,
            Token::LParen,
            Token::Ident("x".into()),
            Token::Comma,
            Token::Ident("y".into()),
            Token::RParen,
            Token::LBrace,
            Token::Ident("x".into()),
            Token::Plus,
            Token::Ident("y".into()),
            Token::Semicolon,
            Token::RBrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident("result".into()),
            Token::Assign,
            Token::Ident("add".into()),
            Token::LParen,
            Token::Ident("five".into()),
            Token::Comma,
            Token::Ident("ten".into()),
            Token::RParen,
            Token::Semicolon,
            Token::String("foobar".into()),
            Token::String("foo bar".into()),
            Token::LBracket,
            Token::Int("1".into()),
            Token::Comma,
            Token::Int("2".into()),
            Token::RBracket,
            Token::Semicolon,
            Token::Eof,
        ];
        for t in expected {
            assert_eq!(t, lexer.next());
        }
    }

    #[test]
    fn operators() {
        let input = "!-/*5;
5 < 10 > 5;";

        let mut lexer = Lexer::new(input);
        let expected = [
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Int("5".into()),
            Token::Semicolon,
            Token::Int("5".into()),
            Token::Lt,
            Token::Int("10".into()),
            Token::Gt,
            Token::Int("5".into()),
            Token::Semicolon,
            Token::Eof,
        ];
        for t in expected {
            assert_eq!(t, lexer.next());
        }
    }

    #[test]
    fn conditionals() {
        let input = "if (5 < 10) {
    return true;
} else {
    return false;
}";

        let mut lexer = Lexer::new(input);
        let expected = [
            Token::If,
            Token::LParen,
            Token::Int("5".into()),
            Token::Lt,
            Token::Int("10".into()),
            Token::RParen,
            Token::LBrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::RBrace,
            Token::Else,
            Token::LBrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::RBrace,
            Token::Eof,
        ];
        for t in expected {
            assert_eq!(t, lexer.next());
        }
    }

    #[test]
    fn boolean_operations() {
        let input = "10 == 10;
10 != 9;";

        let mut lexer = Lexer::new(input);
        let expected = [
            Token::Int("10".into()),
            Token::Eq,
            Token::Int("10".into()),
            Token::Semicolon,
            Token::Int("10".into()),
            Token::NotEq,
            Token::Int("9".into()),
            Token::Semicolon,
            Token::Eof,
        ];
        for t in expected {
            assert_eq!(t, lexer.next());
        }
    }
}
