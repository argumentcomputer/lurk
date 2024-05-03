use std::collections::BTreeMap;
use std::fmt::Debug;
use std::hash::Hash;

use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::tuple::Tuple;
use crate::loam::{Algebra, Attribute, Type, Value};

use super::BubbaBear;

pub type LoamElement = BubbaBear;

#[derive(Default)]
pub struct Schema {}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialOrd, PartialEq)]
pub enum LoamValue<T> {
    Ptr(T, T),
    Wide([T; 8]),
    #[default]
    Dummy,
}

impl Value for BubbaBear {}
impl<T: Value> Value for LoamValue<T> {}

impl LoamValue<LoamElement> {
    pub fn type_of(&self) -> LoamElement {
        match self {
            Self::Ptr(_, _) => 1,
            Self::Wide(_) => 2,
            Self::Dummy => unimplemented!(),
        }
    }
}

// impl<T: Copy + Debug + Hash + Ord> Attribute for LoamValue<T> {}
// impl<T: Copy + Debug + Hash + Ord> Type for LoamValue<T> {}

impl Schema {
    fn tuple<I: IntoIterator<Item = (LoamElement, LoamValue<LoamElement>)>>(
        &self,
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_schema() {
        let schema = Schema::default();
        let tuple = schema.tuple([
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
