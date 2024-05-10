use std::collections::{HashMap, HashSet};

use crate::loam::algebra::{Algebra, AlgebraError};
use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::relation::{Rel, Relation, SimpleRelation};
use crate::loam::tuple::{SimpleTuple, Tuple};
use crate::loam::{Attribute, Type, Value};

#[derive(Clone, Debug, PartialEq)]
enum Quoted<A: Attribute, T: Type, V: Value> {
    And(SimpleHeading<A, T, V>, Box<Self>),
    Or(SimpleHeading<A, T, V>, Box<Self>),
    Not(SimpleHeading<A, T, V>, Box<Self>),
    Project(SimpleHeading<A, T, V>, Vec<A>),
    Remove(SimpleHeading<A, T, V>, Vec<A>),
    Rename(SimpleHeading<A, T, V>, HashMap<A, A>),
    Compose(SimpleHeading<A, T, V>, Box<Self>),
    Rel(Rel<A, T, V>),
}

impl<A: Attribute, T: Type, V: Value> Algebra<A, V> for Quoted<A, T, V> {
    fn and(&self, _other: &Self) -> Self {
        todo!()
    }
    fn or(&self, _other: &Self) -> Self {
        todo!()
    }
    fn not(&self) -> Self {
        todo!()
    }
    fn project<I: Into<HashSet<A>>>(&self, _attrs: I) -> Self {
        todo!()
    }
    fn remove<I: Into<HashSet<A>>>(&self, _attrs: I) -> Self {
        todo!()
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, _mapping: I) -> Result<Self, AlgebraError> {
        todo!()
    }
    fn compose(&self, _other: &Self) -> Self {
        todo!()
    }
    fn is_negated(&self) -> bool {
        todo!()
    }
}
