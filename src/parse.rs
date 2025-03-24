use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableName(Arc<str>);

impl VariableName {
    /// Accesses the inner string.
    pub fn as_inner(&self) -> &str {
        self.0.as_ref()
    }

    /// Creates a variable name.
    pub fn from_str_unchecked<Str: Into<Arc<str>>>(s: Str) -> Self {
        Self(s.into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment {
    variable: VariableName,
    expression: Expression,
}

impl Assignment {
    /// Accesses the variable that is being defined.
    pub fn variable(&self) -> &VariableName {
        &self.variable
    }

    /// Accesses the expression that returns a value that is assigned to the defined variable.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Constant(Arc<[u8]>),
    Call(Call),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    name: FunctionName,
    arguments: Arc<[VariableName]>,
}

impl Call {
    /// Accesses the name of the called function.
    pub fn name(&self) -> &FunctionName {
        &self.name
    }

    /// Accesses the arguments of the function call.
    pub fn arguments(&self) -> &[VariableName] {
        &self.arguments
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionName {
    Add,
    Verify,
}
