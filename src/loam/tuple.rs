use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::schema::{LoamElement, LoamValue};
use crate::loam::{Algebra, Attribute, Type, Value};

#[derive(Clone, Debug)]
pub struct Tuple<A, T, V> {
    pub(crate) heading: SimpleHeading<A, T>,
    pub(crate) values: BTreeMap<A, V>,
}

impl<A: Attribute, T: Type, V: Value> Tuple<A, T, V> {
    pub fn get(&self, attr: A) -> Option<&V> {
        self.values.get(&attr)
    }
}

impl Tuple<LoamElement, LoamElement, LoamValue<LoamElement>> {
    pub fn new<I: IntoIterator<Item = (LoamElement, LoamValue<LoamElement>)>>(
        vals: I,
    ) -> Tuple<LoamElement, LoamElement, LoamValue<LoamElement>> {
        let mut heading = SimpleHeading::new(false);
        let mut values = BTreeMap::<LoamElement, LoamValue<LoamElement>>::new();

        for (attr, value) in vals.into_iter() {
            let typ = value.type_of();
            heading.add_attribute(attr, typ);
            values.insert(attr, value);
        }
        Tuple { heading, values }
    }
}

impl<A: Attribute, T: Type, V: Value> Heading<A, T> for Tuple<A, T, V> {
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

impl<A: Attribute, T: Type, V: Value> Algebra<A, T> for Tuple<A, T, V> {
    fn and(&self, other: &Self) -> Self {
        let heading = self.heading.and(&other.heading);
        let mut values = BTreeMap::<A, V>::new();

        for attr in heading.attributes() {
            let value = self
                .values
                .get(attr)
                .or_else(|| other.values.get(attr))
                .unwrap();

            values.insert(attr.clone(), value.clone());
        }
        Self { heading, values }
    }
    fn or(&self, other: &Self) -> Self {
        todo!();
    }
    fn equal(&self, other: &Self) -> bool {
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
    fn compose(&self, other: &Self) -> Self {
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tuple() {
        let tuple = Tuple::new([
            (5, LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8])),
            (6, LoamValue::Ptr(9, 10)),
        ]);

        assert_eq!(2, tuple.arity());
        assert_eq!(2, *tuple.attribute_type(5).unwrap());
        assert_eq!(1, *tuple.attribute_type(6).unwrap());
        assert_eq!(
            LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8]),
            *tuple.get(5).unwrap()
        );
        assert_eq!(LoamValue::Ptr(9, 10), *tuple.get(6).unwrap());
    }
}
