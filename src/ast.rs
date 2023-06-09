use std::fmt::Display;

#[derive(Debug, PartialEq, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for s in &self.statements {
            writeln!(f, "{s}")?;
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Identifier(Identifier),
    Integer(i64),
    Boolean(bool),
    StringLiteral(String),
    Prefix {
        operator: PrefixOperator,
        right: Box<Expression>,
    },
    Infix {
        left: Box<Expression>,
        operator: InfixOperator,
        right: Box<Expression>,
    },
    If {
        condition: Box<Expression>,
        consequence: Block,
        alternative: Option<Block>,
    },
    FunctionLiteral {
        params: Vec<Identifier>,
        body: Block,
    },
    Call {
        function: Box<Expression>,
        args: Vec<Expression>,
    },
    ArrayLiteral {
        elements: Vec<Expression>,
    },
    Index {
        left: Box<Expression>,
        index: Box<Expression>,
    },
    HashLiteral {
        pairs: Vec<(Expression, Expression)>,
    },
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier(i) => write!(f, "{}", i.name),
            Expression::Integer(i) => write!(f, "{i}"),
            Expression::StringLiteral(s) => write!(f, "\"{s}\""),
            Expression::Prefix { operator, right } => write!(f, "({operator}{right})"),
            Expression::Infix {
                left,
                operator,
                right,
            } => write!(f, "({left} {operator} {right})"),
            Expression::Boolean(b) => write!(f, "{b}"),
            Expression::If {
                condition,
                consequence,
                alternative,
            } => {
                write!(f, "if {} {}", condition, consequence)?;
                if let Some(alt) = alternative {
                    write!(f, "else {}", alt)?;
                }
                Ok(())
            }
            Expression::FunctionLiteral { params, body } => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p.name)?;
                }
                write!(f, ")\n{}", body)
            }
            Expression::Call { function, args } => {
                write!(f, "{}(", function)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", a)?;
                }
                write!(f, ")")
            }
            Expression::ArrayLiteral { elements } => {
                write!(f, "[")?;
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "]")
            }
            Expression::Index { left, index } => write!(f, "({left}[{index}])"),
            Expression::HashLiteral { pairs } => {
                write!(f, "{{")?;
                for (i, (k, v)) in pairs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Identifier {
    pub name: String,
}

impl Identifier {
    pub fn new(name: &str) -> Self {
        Self { name: name.into() }
    }
}

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
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
