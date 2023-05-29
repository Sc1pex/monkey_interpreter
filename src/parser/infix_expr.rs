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
        _ => None,
    }
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
