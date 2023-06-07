use crate::{
    ast::{Block, Identifier},
    environment::Env,
    evaluator::builtin::Builtin,
};
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Return(Box<Object>),
    Function {
        parameters: Vec<Identifier>,
        body: Block,
        env: Env,
    },
    Builtin(Builtin),
    String(String),
    Array(Vec<Object>),
    Hash(HashMap<HashKey, HashPair>),
    Null,
}

impl Object {
    pub fn is_truthy(&self) -> bool {
        match self {
            Object::Boolean(b) => *b,
            Object::Null => false,
            _ => true,
        }
    }

    pub fn unwrap_return(self) -> Object {
        match self {
            Object::Return(x) => *x,
            _ => self,
        }
    }

    pub fn type_name(&self) -> String {
        match self {
            Object::Integer(_) => "INTEGER".into(),
            Object::Boolean(_) => "BOOLEAN".into(),
            Object::Return(_) => "RETURN".into(),
            Object::Function { .. } => "FUNCTION".into(),
            Object::String(_) => "STRING".into(),
            Object::Builtin(_) => "BUILTIN".into(),
            Object::Array(_) => "ARRAY".into(),
            Object::Hash(_) => "HASH".into(),
            Object::Null => "NULL".into(),
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Integer(x) => write!(f, "{}", x),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Return(x) => write!(f, "{}", x),
            Object::Function {
                parameters, body, ..
            } => {
                write!(f, "fn(")?;
                let mut first = true;
                for param in parameters {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param.name)?;
                    first = false;
                }
                write!(f, ") {{")?;
                write!(f, "{}", body)?;
                write!(f, "}}")
            }
            Object::Builtin(b) => write!(f, "{:?}", b),
            Object::String(s) => write!(f, "{}", s),
            Object::Array(a) => {
                write!(f, "[")?;
                let mut first = true;
                for item in a {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                    first = false;
                }
                write!(f, "]")
            }
            Object::Hash(h) => {
                write!(f, "{{")?;
                let mut first = true;
                for value in h.values() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", value.key, value.value)?;
                    first = false;
                }
                write!(f, "}}")
            }
            Object::Null => write!(f, "null"),
        }
    }
}

#[derive(Hash, Debug, PartialEq, Eq, Clone)]
pub enum HashKey {
    Integer(i64),
    Boolean(bool),
    String(String),
}

impl TryFrom<&Object> for HashKey {
    type Error = String;

    fn try_from(value: &Object) -> Result<Self, Self::Error> {
        match value {
            Object::Integer(x) => Ok(HashKey::Integer(*x)),
            Object::Boolean(b) => Ok(HashKey::Boolean(*b)),
            Object::String(s) => Ok(HashKey::String(s.clone())),
            _ => Err(format!("Unusable as hash key: {}", value.type_name())),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct HashPair {
    pub key: Object,
    pub value: Object,
}
