use std::collections::BTreeMap;
use thiserror::Error;

use crate::loam::algebra::Algebra;
use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::tuple::{SimpleTuple, Tuple};
use crate::loam::{Attribute, Type, Value};

#[derive(Error, Debug, PartialEq)]
pub enum RelationError {
    #[error("Duplicate Tuple")]
    DuplicateTuple,
}

pub trait Relation<A: Attribute, T: Type, V: Value> {
    // Infinite or unmaterialized relations may lack a reportable cardinality.
    fn cardinality(&self) -> Option<usize>;
    fn key(&self) -> Vec<A>;
    // If key is unspecified, all attributes will be used, in arbitrary order.
    fn new<I: IntoIterator<Item = Tup>, Tup: Tuple<A, T, V> + Algebra<A, V>>(
        tuples: I,
        key: Option<Vec<A>>,
    ) -> Result<Self, RelationError>
    where
        Self: Sized;
    fn empty(heading: SimpleHeading<A, T, V>, key: Option<Vec<A>>) -> Self;

    // The same tuple can be inserted more than once without changing the relation. If a distinct tuple with an existing
    // key is inserted, a RelationError::DuplicateTuple error is returned.
    fn insert(&mut self, tuple: (impl Tuple<A, T, V> + Algebra<A, V>))
        -> Result<(), RelationError>;
}

#[derive(Clone, Debug, PartialEq)]
pub struct SimpleRelation<A: Attribute, T: Type, V: Value> {
    pub(crate) heading: SimpleHeading<A, T, V>,
    pub(crate) tuples: BTreeMap<Vec<V>, SimpleTuple<A, T, V>>,
    pub(crate) key: Vec<A>,
}

impl<A: Attribute, T: Type, V: Value> Relation<A, T, V> for SimpleRelation<A, T, V> {
    fn cardinality(&self) -> Option<usize> {
        Some(self.tuples.len())
    }
    fn key(&self) -> Vec<A> {
        self.key.clone()
    }
    fn new<I: IntoIterator<Item = Tup>, Tup: Tuple<A, T, V> + Algebra<A, V>>(
        tuples: I,
        key: Option<Vec<A>>,
    ) -> Result<Self, RelationError> {
        let mut tuples = tuples.into_iter();
        let first_tuple = tuples.next();

        let heading = first_tuple
            .as_ref()
            .map(|t| SimpleHeading::from_tuple(t))
            .unwrap_or_else(|| SimpleHeading::new(false));
        let mut relation = Self::empty(heading, key);

        if let Some(t) = first_tuple {
            relation.insert(t)?;
        }
        for tuple in tuples {
            relation.insert(tuple)?;
        }
        Ok(relation)
    }
    fn empty(heading: SimpleHeading<A, T, V>, key: Option<Vec<A>>) -> Self {
        let key = key.unwrap_or_else(|| heading.attributes().into_iter().cloned().collect());

        Self {
            heading,
            tuples: Default::default(),
            key,
        }
    }
    fn insert(
        &mut self,
        tuple: (impl Tuple<A, T, V> + Algebra<A, V>),
    ) -> Result<(), RelationError> {
        let simple_tuple = SimpleTuple::from_tuple(&tuple);

        let k = self
            .key
            .iter()
            .map(|attr| tuple.get(*attr).unwrap().clone())
            .collect::<Vec<_>>();

        if let Some(found) = self.tuples.get(&k) {
            if found != &simple_tuple {
                return Err(RelationError::DuplicateTuple);
            }
        }
        let _ = self.tuples.insert(k.clone(), simple_tuple);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::loam::schema::{LoamElement, LoamValue};
    use crate::loam::{Attr, Typ};

    type V = LoamValue<LoamElement>;

    #[test]
    fn test_simple_relation() {
        let empty_heading = SimpleHeading::<Attr, Typ, V>::default();
        assert_eq!(0, empty_heading.arity());
        let mut r: SimpleRelation<Attr, Typ, V> = SimpleRelation::empty(empty_heading, None);

        assert_eq!(Some(0), r.cardinality());
        assert_eq!(Vec::<Attr>::new(), r.key());

        let empty_tuple = SimpleTuple::new([]);
        r.insert(empty_tuple.clone()).unwrap();

        let r2 = SimpleRelation::new([empty_tuple], None).unwrap();
        assert_eq!(r, r2);

        let w1 = LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8]);
        let w2 = LoamValue::Wide([10, 20, 30, 40, 50, 60, 70, 80]);
        let p1 = LoamValue::Ptr(9, 10);
        let p2 = LoamValue::Ptr(11, 12);

        let wt = w1.type_of();
        let pt = p1.type_of();

        let (a1, a2, a3) = (5, 6, 7);

        let r3 = SimpleRelation::new(
            [
                SimpleTuple::new([(a1, w1), (a2, p1)]),
                SimpleTuple::new([(a1, w1), (a2, p1)]),
            ],
            Some(vec![a1]),
        )
        .unwrap();
        assert_eq!(Some(1), r3.cardinality());

        let r4 = SimpleRelation::new(
            [
                SimpleTuple::new([(a1, w1), (a2, p1)]),
                SimpleTuple::new([(a1, w1), (a2, p2)]),
            ],
            Some(vec![a1]),
        );
        assert_eq!(Err(RelationError::DuplicateTuple), r4);
    }
}
