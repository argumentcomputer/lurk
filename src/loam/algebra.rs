use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::Attribute;

pub trait Algebra<A: Attribute, T>: PartialEq {
    fn and(&self, other: &Self) -> Self;
    fn or(&self, other: &Self) -> Self;
    fn not(&self) -> Self;
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self;
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self;
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Self;
    fn compose(&self, other: &Self) -> Self;

    fn is_negated(&self) -> bool;
    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, T>>>;
}
