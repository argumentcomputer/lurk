use std::collections::{HashMap, HashSet};

use super::{AlgebraHeading, Attribute, Type};

pub trait Algebra<A: Attribute, T: Type> {
    fn and(&self, other: &impl AlgebraHeading<A, T>) -> Self;
    fn or(&self, other: &impl AlgebraHeading<A, T>) -> Self;
    fn equal(&self, other: &impl AlgebraHeading<A, T>) -> bool;
    fn not(&self) -> Self;
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self;
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self;
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Self;
    fn compose(&self, other: &impl AlgebraHeading<A, T>) -> Self;
}
