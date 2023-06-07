use self::builtin::{eval_builtin, Builtin};
use crate::{
    ast::*,
    environment::{Env, Environment},
    object::{HashKey, HashPair, Object},
};
use std::{cell::RefCell, rc::Rc};

pub mod builtin;

pub type EvalResult = Result<Object, String>;

// Evaluates the root node of the AST
pub fn eval(b: Block, env: &mut Env) -> EvalResult {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s, env)?;
        if let Object::Return(obj) = res {
            return Ok(*obj);
        }
    }

    Ok(res)
}

// Evaluates a block of statements
// Different from eval() in that it dose not return the inner object of a return value
fn eval_block(b: Block, env: &mut Env) -> EvalResult {
    let mut res = Object::Null;

    for s in b.statements {
        res = eval_statement(s, env)?;
        if let Object::Return(_) = res {
            return Ok(res);
        }
    }

    Ok(res)
}

fn eval_statement(s: Statement, env: &mut Env) -> EvalResult {
    match s {
        Statement::Expression { value: e } => eval_expression(e, env),
        Statement::Return { value: e } => Ok(Object::Return(Box::new(eval_expression(e, env)?))),
        Statement::Let { ident, value } => {
            let value = eval_expression(value, env)?;
            env.borrow_mut().set(&ident.name, value);
            Ok(Object::Null)
        }
    }
}

fn eval_expression(e: Expression, env: &mut Env) -> EvalResult {
    match e {
        Expression::Integer(x) => Ok(Object::Integer(x)),
        Expression::Boolean(b) => Ok(Object::Boolean(b)),
        Expression::Prefix { operator, right } => {
            let right = eval_expression(*right, env)?;
            eval_prefix_expression(operator, right, env)
        }
        Expression::Infix {
            left,
            operator,
            right,
        } => {
            let left = eval_expression(*left, env)?;
            let right = eval_expression(*right, env)?;
            eval_infix_expression(operator, left, right, env)
        }
        Expression::If {
            condition,
            consequence,
            alternative,
        } => {
            let condition = eval_expression(*condition, env)?;
            if condition.is_truthy() {
                eval_block(consequence, env)
            } else if let Some(alt) = alternative {
                eval_block(alt, env)
            } else {
                Ok(Object::Null)
            }
        }
        Expression::Identifier(ident) => match env.borrow().get(&ident.name) {
            Some(obj) => Ok(obj),
            None => {
                if let Some(builtin) = Builtin::lookup(&ident.name) {
                    Ok(Object::Builtin(builtin))
                } else {
                    Err(format!("Identifier not found: {}", ident.name))
                }
            }
        },
        Expression::FunctionLiteral { params, body } => Ok(Object::Function {
            parameters: params,
            body,
            env: env.clone(),
        }),
        Expression::Call { function, args } => {
            let function = eval_expression(*function, env)?;
            let args = eval_expressions(args, env)?;

            match function {
                Object::Function {
                    parameters,
                    body,
                    env,
                } => {
                    let mut env = Rc::new(RefCell::new(Environment::new_enclosed(&env)));
                    for (param, arg) in parameters.into_iter().zip(args.into_iter()) {
                        env.borrow_mut().set(&param.name, arg);
                    }

                    Ok(eval_block(body, &mut env)?.unwrap_return())
                }
                Object::Builtin(b) => eval_builtin(b, args),
                _ => Err(format!("Not a function: {}", function.type_name()))?,
            }
        }
        Expression::ArrayLiteral { elements } => {
            let elements = eval_expressions(elements, env)?;
            Ok(Object::Array(elements))
        }
        Expression::Index { left, index } => {
            let left = eval_expression(*left, env)?;
            let index = eval_expression(*index, env)?;

            match (&left, &index) {
                (Object::Array(elements), Object::Integer(i)) => {
                    if *i < 0 || *i >= elements.len() as i64 {
                        return Err(format!("Index out of bounds: {}", i,));
                    }
                    Ok(elements[*i as usize].clone())
                }
                (Object::Hash(hash), key) => {
                    let key = HashKey::try_from(key)?;
                    match hash.get(&key) {
                        Some(pair) => Ok(pair.value.clone()),
                        None => Ok(Object::Null),
                    }
                }
                _ => Err(format!(
                    "Index operator not supported for {}",
                    left.type_name(),
                )),
            }
        }
        Expression::StringLiteral(s) => Ok(Object::String(s)),
        Expression::HashLiteral { pairs } => {
            let mut hash = std::collections::HashMap::new();
            for (key, value) in pairs {
                let key = eval_expression(key, env)?;
                let value = eval_expression(value, env)?;
                let hash_key = HashKey::try_from(&key)?;
                hash.insert(hash_key, HashPair { key, value });
            }
            Ok(Object::Hash(hash))
        }
    }
}

fn eval_expressions(exprs: Vec<Expression>, env: &mut Env) -> Result<Vec<Object>, String> {
    exprs.into_iter().map(|e| eval_expression(e, env)).collect()
}

fn eval_infix_expression(
    operator: InfixOperator,
    left: Object,
    right: Object,
    _env: &mut Env,
) -> EvalResult {
    match operator {
        InfixOperator::Add => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Integer(x + y)),
            (Object::String(x), Object::String(y)) => {
                return Ok(Object::String(format!("{}{}", x, y)))
            }

            _ => {}
        },
        InfixOperator::Subtract => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x - y));
            }
        }
        InfixOperator::Multiply => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x * y));
            }
        }
        InfixOperator::Divide => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Integer(x / y));
            }
        }
        InfixOperator::Equal => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x == y)),
            (Object::Boolean(x), Object::Boolean(y)) => return Ok(Object::Boolean(x == y)),
            _ => {}
        },
        InfixOperator::NotEqual => match (&left, &right) {
            (Object::Integer(x), Object::Integer(y)) => return Ok(Object::Boolean(x != y)),
            (Object::Boolean(x), Object::Boolean(y)) => return Ok(Object::Boolean(x != y)),
            _ => {}
        },
        InfixOperator::LessThan => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Boolean(x < y));
            }
        }
        InfixOperator::GreaterThan => {
            if let (Object::Integer(x), Object::Integer(y)) = (&left, &right) {
                return Ok(Object::Boolean(x > y));
            }
        }
    };

    Err(format!(
        "Unknown operator: {} {} {}",
        left.type_name(),
        operator,
        right.type_name()
    ))
}

fn eval_prefix_expression(operator: PrefixOperator, right: Object, _env: &mut Env) -> EvalResult {
    match operator {
        PrefixOperator::Not => match right {
            Object::Boolean(b) => Ok(Object::Boolean(!b)),
            Object::Null => Ok(Object::Boolean(true)),

            _ => Ok(Object::Boolean(false)),
        },
        PrefixOperator::Negate => match right {
            Object::Integer(x) => Ok(Object::Integer(-x)),
            _ => Err(format!("Unknown operator: -{}", right.type_name())),
        },
    }
}
