use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::loam::algebra::{Algebra, AlgebraError};
use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::schema::{LoamElement, LoamValue};
use crate::loam::tuple::{SimpleTuple, Tuple};
use crate::loam::{Attribute, Type, Value};

pub trait Relation<A: Attribute, T: Type, V: Value> {
    fn cardinality(&self) -> Option<usize>;
    fn key(&self) -> Option<BTreeSet<A>>;
    fn empty(heading: SimpleHeading<A, T>) -> Self;
    fn new<I: Into<HashSet<impl Tuple<A, T, V>>>>(tuples: I) -> Self;
    fn insert(&mut self, tuple: (impl Tuple<A, T, V> + Algebra<A, V>));
}

#[derive(Clone, Debug)]
pub struct SimpleRelation<A: Attribute, T: Type, V: Value> {
    pub(crate) heading: SimpleHeading<A, T>,
    pub(crate) tuples: BTreeSet<SimpleTuple<A, T, V>>,
    pub(crate) key: Option<BTreeSet<A>>,
}

impl<A: Attribute, T: Type, V: Value> Relation<A, T, V> for SimpleRelation<A, T, V> {
    fn cardinality(&self) -> Option<usize> {
        Some(self.tuples.len())
    }
    fn key(&self) -> Option<BTreeSet<A>> {
        self.key.clone()
    }
    fn empty(heading: SimpleHeading<A, T>) -> Self {
        Self {
            heading,
            tuples: Default::default(),
            key: None,
        }
    }
    fn new<I: Into<HashSet<impl Tuple<A, T, V>>>>(tuples: I) -> Self {
        // let tuples = tuples.into();
        // if let Some(tuple) = tuples.get(0) {
        //     todo!();
        // }
        // Self {
        //     heading: tuple.heading,
        //     tuples: tuples.into(),
        //     key: None,
        // }
        todo!()
    }
    fn insert(&mut self, tuple: (impl Tuple<A, T, V> + Algebra<A, V>)) {
        let heading = SimpleHeading::from_tuple(&tuple);

        let mut simple_tuple = SimpleTuple {
            heading,
            values: Default::default(),
        };

        for attr in tuple.attributes().iter() {
            if let Some(v) = tuple.get(**attr) {
                simple_tuple.values.insert(**attr, v.clone());
            }
        }

        self.tuples.insert(simple_tuple);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::loam::schema::{LoamElement, LoamValue};
    use crate::loam::{Attr, Typ};

    #[test]
    fn test_simple_relation() {
        let empty_heading = SimpleHeading::<Attr, Typ>::default();
        assert_eq!(0, empty_heading.arity());
        let mut r: SimpleRelation<Attr, Typ, LoamValue<LoamElement>> =
            SimpleRelation::empty(empty_heading);

        assert_eq!(Some(0), r.cardinality());
        assert_eq!(None, r.key());

        let empty_tuple = SimpleTuple::new([]);
        r.insert(empty_tuple.clone());

        //        let r2 = SimpleRelation::new([empty_tuple]);
    }
}
