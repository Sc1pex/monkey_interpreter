use interpreter::lexer::Lexer;
use interpreter::token::Token;

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
[1, 2];
{\"foo\": \"bar\"}";

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
        Token::LBrace,
        Token::String("foo".into()),
        Token::Colon,
        Token::String("bar".into()),
        Token::RBrace,
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
