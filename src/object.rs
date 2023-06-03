use std::fmt::Display;

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Return(Box<Object>),
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
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Integer(x) => write!(f, "{}", x),
            Object::Boolean(b) => write!(f, "{}", b),
            Object::Return(x) => write!(f, "{}", x),
            Object::Null => write!(f, "null"),
        }
    }
}
