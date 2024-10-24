use crate::lurk::parser::position::Pos;

/// OCaml's Lambda IR after parsing
#[derive(Clone, Debug, PartialEq)]
pub enum LambdaSyntax {
    // Trivial forms
    Ident(Pos, String), // TODO: Do we want to use a SymbolRef here, or should this mapping happen later in the pipeline?
    Int(Pos, bool, u64),
    Float(Pos, f64),
    Char(Pos, char),
    String(Pos, String),

    // Composite forms and primitives
    Record(Pos, u64, Vec<LambdaSyntax>),
    Setglobal(Pos, Box<LambdaSyntax>, Box<LambdaSyntax>),
    Seq(Pos, Vec<LambdaSyntax>),
    Makeblock(Pos, u64, Vec<LambdaSyntax>),
    Let(Pos, Vec<(LambdaSyntax, LambdaSyntax)>, Box<LambdaSyntax>),
    Letrec(Pos, Vec<(LambdaSyntax, LambdaSyntax)>, Box<LambdaSyntax>),
    Function(Pos, Vec<LambdaSyntax>, Box<LambdaSyntax>),
    Apply(Pos, Box<LambdaSyntax>, Vec<LambdaSyntax>),

    // These represent fallback forms/primitives that aren't specially handled above
    FallbackPrimitive(Pos, String, Vec<LambdaSyntax>),
    FallbackLiteral(Pos, String),
}

impl LambdaSyntax {
    pub fn get_pos(&self) -> &Pos {
        match self {
            LambdaSyntax::Ident(p, _)
            | LambdaSyntax::Int(p, _, _)
            | LambdaSyntax::Float(p, _)
            | LambdaSyntax::Char(p, _)
            | LambdaSyntax::String(p, _)
            | LambdaSyntax::Record(p, _, _)
            | LambdaSyntax::Setglobal(p, _, _)
            | LambdaSyntax::Seq(p, _)
            | LambdaSyntax::Makeblock(p, _, _)
            | LambdaSyntax::Let(p, _, _)
            | LambdaSyntax::Letrec(p, _, _)
            | LambdaSyntax::Function(p, _, _)
            | LambdaSyntax::Apply(p, _, _)
            | LambdaSyntax::FallbackPrimitive(p, _, _)
            | LambdaSyntax::FallbackLiteral(p, _) => p,
        }
    }
}
