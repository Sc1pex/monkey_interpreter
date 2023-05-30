use super::*;

pub fn prefix_parse_fn(t: &Token) -> Option<fn(&mut Parser) -> Option<Expression>> {
    match t {
        Token::Ident(_) => Some(parse_ident),
        Token::Int(_) => Some(parse_integer_literal),
        Token::Bang | Token::Minus => Some(parse_prefix_expression),
        Token::True | Token::False => Some(parse_bool),
        Token::LParen => Some(parse_group),
        Token::If => Some(parse_if),
        Token::Function => Some(parse_fn),
        _ => None,
    }
}

fn parse_fn(p: &mut Parser) -> Option<Expression> {
    if !p.expect_peek(&Token::LParen) {
        return None;
    }
    let params = p.parse_fn_params()?;
    eprintln!("PARAMS: {:?}", params);
    if !p.expect_peek(&Token::LBrace) {
        return None;
    }
    let body = p.parse_block_statement()?;
    Some(Expression::FunctionLiteral { params, body })
}

fn parse_if(p: &mut Parser) -> Option<Expression> {
    if !p.expect_peek(&Token::LParen) {
        return None;
    }
    p.next_token();

    let condition = p.parse_expression(Precedence::Lowest)?;

    if !p.expect_peek(&Token::RParen) {
        return None;
    }
    if !p.expect_peek(&Token::LBrace) {
        return None;
    }

    let consequence = p.parse_block_statement()?;
    let alternative = if p.peek_token_is(&Token::Else) {
        p.next_token();
        if !p.expect_peek(&Token::LBrace) {
            return None;
        }
        Some(p.parse_block_statement()?)
    } else {
        None
    };

    Some(Expression::If {
        condition: Box::new(condition),
        consequence,
        alternative,
    })
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
