use std::{collections::HashMap, fmt::Display};

use crate::ast::{Block, Identifier};

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Return(Box<Object>),
    Function {
        parameters: Vec<Identifier>,
        body: Block,
        env: Environment,
    },
    Builtin(Builtin),
    String(String),
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
            Object::Null => write!(f, "null"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Builtin {
    Len,
}

impl Builtin {
    pub fn lookup(name: &str) -> Option<Builtin> {
        match name {
            "len" => Some(Builtin::Len),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Environment {
    store: HashMap<String, Object>,
    outer: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            outer: None,
        }
    }

    pub fn new_enclosed(outer: &Environment) -> Self {
        Self {
            store: HashMap::new(),
            outer: Some(Box::new(outer.clone())),
        }
    }

    pub fn get(&self, name: &str) -> Option<Object> {
        self.store
            .get(name)
            .cloned()
            .or_else(|| self.outer.as_ref().and_then(|outer| outer.get(name)))
    }

    pub fn set(&mut self, name: &str, value: Object) {
        self.store.insert(name.into(), value);
    }
}
