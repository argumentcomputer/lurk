#![allow(non_snake_case)]
use serde::{Deserialize, Serialize};
//use std::convert::TryFrom;
use std::fmt::Formatter;
use std::str::FromStr;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct SKI {
    pub src: String,
}

#[derive(Debug)]
pub struct ParseTermError;

impl FromStr for SKI {
    type Err = ParseTermError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self { src: s.into() })
    }
}

impl std::fmt::Display for SKI {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.src)
    }
}
