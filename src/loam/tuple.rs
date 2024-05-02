use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::{Algebra, AlgebraHeading, Attribute, Type};

#[derive(Clone, Debug)]
struct Tuple<A, T> {
    heading: SimpleHeading<A, T>,
    values: BTreeMap<A, T>,
}

impl<A: Attribute, T: Type> Heading<A, T> for Tuple<A, T> {
    fn attributes(&self) -> BTreeSet<&A> {
        self.heading.attributes()
    }
    fn attribute_type(&self, attr: A) -> Option<&T> {
        self.heading.attribute_type(attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        self.heading.attribute_types()
    }
    fn arity(&self) -> usize {
        self.heading.arity()
    }
}

impl<A: Attribute, T: Type> Algebra<A, T> for Tuple<A, T> {
    fn and(&self, other: &impl AlgebraHeading<A, T>) -> Self {
        todo!();
    }
    fn or(&self, other: &impl AlgebraHeading<A, T>) -> Self {
        todo!();
    }
    fn equal(&self, other: &impl AlgebraHeading<A, T>) -> bool {
        todo!();
    }
    fn not(&self) -> Self {
        todo!();
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        todo!();
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        todo!();
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Self {
        todo!();
    }
    fn compose(&self, other: &impl AlgebraHeading<A, T>) -> Self {
        todo!();
    }

    // TODO: Move this and disjunction to Algebra.
    fn is_negated(&self) -> bool {
        todo!();
    }

    fn disjunction(&self) -> &BTreeSet<BTreeMap<A, T>> {
        todo!();
    }
}
