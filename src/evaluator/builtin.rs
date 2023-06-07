use super::EvalResult;
use crate::object::Object;

#[derive(Debug, PartialEq, Clone)]
pub enum Builtin {
    Len,
    First,
    Last,
    Rest,
    Push,
    Print,
}

impl Builtin {
    pub fn lookup(name: &str) -> Option<Builtin> {
        match name {
            "len" => Some(Builtin::Len),
            "first" => Some(Builtin::First),
            "last" => Some(Builtin::Last),
            "rest" => Some(Builtin::Rest),
            "push" => Some(Builtin::Push),
            "print" => Some(Builtin::Print),
            _ => None,
        }
    }
}

pub fn eval_builtin(builtin: Builtin, args: Vec<Object>) -> EvalResult {
    match builtin {
        Builtin::Len => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'len'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::String(s) => Ok(Object::Integer(s.len() as i64)),
                Object::Array(elements) => Ok(Object::Integer(elements.len() as i64)),
                _ => Err(format!(
                    "Wrong argument to 'len'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::First => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'first'. Expected 1, got {}",
                    args.len()
                ));
            }

            match &args[0] {
                Object::Array(elements) => Ok(elements.first().unwrap_or(&Object::Null).clone()),
                _ => Err(format!(
                    "Wrong argument to 'first'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Last => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'last'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::Array(elements) => Ok(elements.last().unwrap_or(&Object::Null).clone()),
                _ => Err(format!(
                    "Wrong argument to 'last'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Rest => {
            if args.len() != 1 {
                return Err(format!(
                    "Wrong number of arguments to 'last'. Expected 1, got {}",
                    args.len()
                ));
            }
            match &args[0] {
                Object::Array(elements) => {
                    if elements.is_empty() {
                        return Ok(Object::Null);
                    }
                    Ok(Object::Array(elements[1..].to_vec()))
                }
                _ => Err(format!(
                    "Wrong argument to 'rest'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Push => {
            if args.len() != 2 {
                return Err(format!(
                    "Wrong number of arguments to 'push'. Expected 1, got {}",
                    args.len()
                ));
            }

            match &args[0] {
                Object::Array(elements) => {
                    let mut elements = elements.clone();
                    elements.push(args[1].clone());
                    Ok(Object::Array(elements))
                }
                _ => Err(format!(
                    "Wrong argument to 'push'. Got {}",
                    args[0].type_name()
                )),
            }
        }
        Builtin::Print => {
            for arg in args {
                println!("{}", arg);
            }
            Ok(Object::Null)
        }
    }
}
