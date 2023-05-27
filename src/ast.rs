use crate::token::Token;

#[derive(Debug)]
pub enum Node {
    Root(Vec<Statement>),
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Let(LetStatement),
    Return,
}

#[derive(Debug, PartialEq)]
pub struct LetStatement {
    pub ident: Token,
    pub value: Expression,
}

#[derive(Debug, PartialEq)]
pub struct Expression {}
