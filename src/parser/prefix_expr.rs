use super::*;

pub fn prefix_parse_fn(t: &Token) -> Option<fn(&mut Parser) -> Option<Expression>> {
    match t {
        Token::Ident(_) => Some(parse_ident),
        Token::Int(_) => Some(parse_integer_literal),
        Token::Bang | Token::Minus => Some(parse_prefix_expression),
        Token::True | Token::False => Some(parse_bool),
        Token::LParen => Some(parse_group),
        _ => None,
    }
}

fn parse_ident(p: &mut Parser) -> Option<Expression> {
    let name = if let Token::Ident(s) = &p.cur_token {
        s.clone()
    } else {
        unreachable!()
    };
    Some(Expression::Identifier(Identifier { name }))
}

fn parse_integer_literal(p: &mut Parser) -> Option<Expression> {
    let value = if let Token::Int(i) = &p.cur_token {
        i
    } else {
        unreachable!()
    };
    Some(Expression::Integer(
        value.parse().expect("Failed to parse integer"),
    ))
}

fn parse_bool(p: &mut Parser) -> Option<Expression> {
    let value = match &p.cur_token {
        Token::True => true,
        Token::False => false,
        _ => return None,
    };
    Some(Expression::Boolean(value))
}

fn parse_group(p: &mut Parser) -> Option<Expression> {
    p.next_token();
    let expr = p.parse_expression(Precedence::Lowest)?;
    if !p.expect_peek(&Token::RParen) {
        return None;
    }
    Some(expr)
}

fn parse_prefix_expression(p: &mut Parser) -> Option<Expression> {
    let operator = match &p.cur_token {
        Token::Bang => PrefixOperator::Not,
        Token::Minus => PrefixOperator::Negate,
        _ => return None,
    };
    p.next_token();

    let right = p.parse_expression(Precedence::Prefix)?;
    Some(Expression::Prefix {
        operator,
        right: Box::new(right),
    })
}
