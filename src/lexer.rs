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
            b'=' => Token::Assign,
            b'+' => Token::Plus,
            b',' => Token::Comma,
            b';' => Token::Semicolon,
            b'{' => Token::LBrace,
            b'}' => Token::RBrace,
            b'(' => Token::LParen,
            b')' => Token::RParen,
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => return Token::lookup(self.read_ident()),
            b'0'..=b'9' => return Token::Int(String::from_utf8_lossy(self.read_number()).into()),
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

let result = add(five, ten);";

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
            Token::Eof,
        ];
        for t in expected {
            let t1 = lexer.next();
            println!("Got {:?}, expected {:?}", t1, t);
            assert_eq!(t, t1);
            // assert_eq!(t, lexer.next());
        }
    }
}
