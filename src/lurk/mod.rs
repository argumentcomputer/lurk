//! This module is an implementation of Lurk using Lair as the backend.

pub mod cli;
pub mod eval;
#[cfg(test)]
mod eval_tests;
pub mod package;
pub mod parser;
pub mod state;
pub mod symbol;
pub mod syntax;
pub mod tag;
pub mod zstore;
