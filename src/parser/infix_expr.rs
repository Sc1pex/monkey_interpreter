use super::*;

pub fn infix_parse_fn(t: &Token) -> Option<fn(&mut Parser, Expression) -> Option<Expression>> {
    match t {
        Token::Plus
        | Token::Minus
        | Token::Slash
        | Token::Asterisk
        | Token::Lt
        | Token::Gt
        | Token::Eq
        | Token::NotEq => Some(parse_infix_expression),
        Token::LParen => Some(parse_call_args),
        Token::LBracket => Some(parse_index_expression),
        _ => None,
    }
}

fn parse_index_expression(p: &mut Parser, left: Expression) -> Option<Expression> {
    p.next_token();
    let index = p.parse_expression(Precedence::Lowest)?;
    if !p.expect_peek(&Token::RBracket) {
        return None;
    }
    Some(Expression::Index {
        left: Box::new(left),
        index: Box::new(index),
    })
}

fn parse_call_args(p: &mut Parser, left: Expression) -> Option<Expression> {
    let args = p.parse_call_args()?;
    Some(Expression::Call {
        function: Box::new(left),
        args,
    })
}

fn parse_infix_expression(p: &mut Parser, left: Expression) -> Option<Expression> {
    let operator = match &p.cur_token {
        Token::Plus => InfixOperator::Add,
        Token::Minus => InfixOperator::Subtract,
        Token::Slash => InfixOperator::Divide,
        Token::Asterisk => InfixOperator::Multiply,
        Token::Lt => InfixOperator::LessThan,
        Token::Gt => InfixOperator::GreaterThan,
        Token::Eq => InfixOperator::Equal,
        Token::NotEq => InfixOperator::NotEqual,
        _ => return None,
    };

    let precedence = p.cur_precedence();
    p.next_token();

    Some(Expression::Infix {
        left: Box::new(left),
        operator,
        right: Box::new(p.parse_expression(precedence)?),
    })
}
