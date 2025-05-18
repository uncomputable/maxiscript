use chumsky::prelude::SimpleSpan;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Diagnostic {
    top: Context,
    contexts: Vec<Context>,
    contexts2: Vec<Context>,
    note: Option<String>,
    severity: Severity,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Severity {
    Error,
    Warning,
}

impl Diagnostic {
    fn new<Str: ToString>(message: Str, span: SimpleSpan, severity: Severity) -> Self {
        Self {
            top: Context {
                message: message.to_string(),
                span,
            },
            contexts: Vec::new(),
            contexts2: Vec::new(),
            note: None,
            severity,
        }
    }

    pub fn error<Str: ToString>(message: Str, span: SimpleSpan) -> Self {
        Self::new(message, span, Severity::Error)
    }

    pub fn warning<Str: ToString>(message: Str, span: SimpleSpan) -> Self {
        Self::new(message, span, Severity::Warning)
    }

    pub fn in_context<Str: ToString>(mut self, message: Str, span: SimpleSpan) -> Self {
        self.contexts.push(Context {
            message: message.to_string(),
            span,
        });
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: self.note,
            severity: self.severity,
        }
    }

    pub fn in_context2<Str: ToString>(mut self, message: Str, span: SimpleSpan) -> Self {
        self.contexts2.push(Context {
            message: message.to_string(),
            span,
        });
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: self.note,
            severity: self.severity,
        }
    }

    pub fn with_note<Str: ToString>(self, message: Str) -> Self {
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: Some(message.to_string()),
            severity: self.severity,
        }
    }

    pub fn top(&self) -> &Context {
        &self.top
    }

    pub fn contexts(&self) -> &[Context] {
        &self.contexts
    }

    pub fn contexts2(&self) -> &[Context] {
        &self.contexts2
    }

    pub fn note(&self) -> Option<&String> {
        self.note.as_ref()
    }

    pub fn severity(&self) -> Severity {
        self.severity
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Context {
    message: String,
    span: SimpleSpan,
}

impl Context {
    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn span(&self) -> SimpleSpan {
        self.span
    }
}
