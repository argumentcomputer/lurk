use std::collections::BTreeMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use crate::loam::heading::SimpleHeading;
use crate::loam::tuple::{SimpleTuple, Tuple};
use crate::loam::Value;

use super::BubbaBear;

pub type LoamElement = BubbaBear;

#[derive(Default)]
pub struct Schema<T: Default> {
    _p: PhantomData<T>,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialOrd, PartialEq)]
pub enum LoamValue<T: Copy> {
    Ptr(T, T),
    Wide([T; 8]),
    F(T),
    #[default]
    Dummy,
}

impl Value for BubbaBear {}
impl<T: Value> Value for LoamValue<T> {}

impl LoamValue<LoamElement> {
    pub fn type_of(&self) -> LoamElement {
        match self {
            Self::F(_) => 0,
            Self::Ptr(_, _) => 1,
            Self::Wide(_) => 2,
            Self::Dummy => unimplemented!(),
        }
    }
}

impl<T: Copy> LoamValue<T> {
    pub fn f_val(&self) -> Option<T> {
        match self {
            Self::F(x) => Some(*x),
            _ => None,
        }
    }
    pub fn wide_val(&self) -> Option<&[T; 8]> {
        match self {
            Self::Wide(x) => Some(x),
            _ => None,
        }
    }
}

impl Schema<SimpleTuple<LoamElement, LoamElement, LoamValue<LoamElement>>> {
    fn tuple<I: IntoIterator<Item = (LoamElement, LoamValue<LoamElement>)>>(
        &self,
        vals: I,
    ) -> SimpleTuple<LoamElement, LoamElement, LoamValue<LoamElement>> {
        let mut heading = SimpleHeading::new(false);
        let mut values = BTreeMap::<LoamElement, LoamValue<LoamElement>>::new();

        for (attr, value) in vals.into_iter() {
            let typ = value.type_of();
            heading.add_attribute(attr, typ);
            values.insert(attr, value);
        }
        SimpleTuple { heading, values }
    }
}

type SimpleSchema = Schema<SimpleTuple<LoamElement, LoamElement, LoamValue<LoamElement>>>;

#[cfg(test)]
mod test {
    use super::*;
    use crate::loam::Heading;

    #[test]
    fn test_schema() {
        let schema = SimpleSchema::default();
        let tuple = schema.tuple([
            (5, LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8])),
            (6, LoamValue::Ptr(9, 10)),
        ]);

        assert_eq!(2, tuple.arity());
        assert_eq!(2, *tuple.get_type(5).unwrap());
        assert_eq!(1, *tuple.get_type(6).unwrap());
        assert_eq!(
            LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8]),
            *tuple.get(5).unwrap()
        );
        assert_eq!(LoamValue::Ptr(9, 10), *tuple.get(6).unwrap());
    }
}
