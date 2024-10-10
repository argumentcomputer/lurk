//! This module is an implementation of Lurk using Lair as the backend.

pub mod big_num;
pub mod chipset;
pub mod cli;
pub mod eval;
pub mod lang;
pub mod package;
pub mod parser;
pub mod poseidon;
pub mod stark_machine;
pub mod state;
pub mod symbol;
pub mod syntax;
pub mod tag;
pub mod u64;
pub mod zstore;

#[cfg(test)]
mod tests;
