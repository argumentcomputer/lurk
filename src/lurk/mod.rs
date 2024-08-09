//! This module is an implementation of Lurk using Lair as the backend.

pub mod chipset;
pub mod cli;
pub mod compile;
pub mod eval;
pub mod eval_compiled;
#[cfg(test)]
mod eval_tests;
pub mod ingress;
pub mod package;
pub mod parser;
pub mod poseidon;
pub mod state;
pub mod symbol;
pub mod syntax;
pub mod tag;
pub mod u64;
pub mod zstore;
