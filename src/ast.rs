use std::fmt::Display;

#[derive(Debug)]
pub enum Node {
    Root(Vec<Statement>),
    Statement(Statement),
    Expression(Expression),
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Root(s) => {
                for s in s {
                    writeln!(f, "{s}").unwrap();
                }
                Ok(())
            }
            Node::Statement(s) => write!(f, "{s}"),
            Node::Expression(e) => write!(f, "{e}"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Identifier {
    pub name: String,
}

impl Identifier {
    pub fn new(name: &str) -> Self {
        Self { name: name.into() }
    }
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Let {
        ident: Identifier,
        value: Expression,
    },
    Return {
        value: Expression,
    },
    Expression {
        value: Expression,
    },
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let { ident, value } => write!(f, "let {} = {};", ident.name, value),
            Statement::Return { value } => write!(f, "return {};", value),
            Statement::Expression { value } => write!(f, "{}", value),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum PrefixOperator {
    Not,
    Negate,
}

impl Display for PrefixOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrefixOperator::Not => write!(f, "!"),
            PrefixOperator::Negate => write!(f, "-"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum InfixOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
}

impl Display for InfixOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InfixOperator::Add => write!(f, "+"),
            InfixOperator::Subtract => write!(f, "-"),
            InfixOperator::Multiply => write!(f, "*"),
            InfixOperator::Divide => write!(f, "/"),
            InfixOperator::Equal => write!(f, "=="),
            InfixOperator::NotEqual => write!(f, "!="),
            InfixOperator::LessThan => write!(f, "<"),
            InfixOperator::GreaterThan => write!(f, ">"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    None,
    Identifier(Identifier),
    Integer(i64),
    Prefix {
        operator: PrefixOperator,
        right: Box<Expression>,
    },
    Infix {
        left: Box<Expression>,
        operator: InfixOperator,
        right: Box<Expression>,
    },
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::None => todo!(),
            Expression::Identifier(i) => write!(f, "{}", i.name),
            Expression::Integer(i) => write!(f, "{i}"),
            Expression::Prefix { operator, right } => write!(f, "({operator}{right})"),
            Expression::Infix {
                left,
                operator,
                right,
            } => write!(f, "({left} {operator} {right})"),
        }
    }
}
