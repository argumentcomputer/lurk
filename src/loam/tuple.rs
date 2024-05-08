use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::loam::algebra::{Algebra, AlgebraError};
use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::schema::{LoamElement, LoamValue};
use crate::loam::{Attribute, Type, Value};

pub trait Tuple<A: Attribute, T: Type, V: Value>: Heading<A, T, V> + Algebra<A, V> {
    fn get(&self, attr: A) -> Option<&V>;
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialOrd, Hash)]
pub struct SimpleTuple<A: Attribute, T: Type, V: Value> {
    pub(crate) heading: SimpleHeading<A, T, V>,
    pub(crate) values: BTreeMap<A, V>,
}

impl<A: Attribute, T: Type, V: Value> Tuple<A, T, V> for SimpleTuple<A, T, V> {
    fn get(&self, attr: A) -> Option<&V> {
        self.values.get(&attr)
    }
}

impl SimpleTuple<LoamElement, LoamElement, LoamValue<LoamElement>> {
    pub fn new<I: IntoIterator<Item = (LoamElement, LoamValue<LoamElement>)>>(
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

impl<A: Attribute, T: Type, V: Value> Heading<A, T, V> for SimpleTuple<A, T, V> {
    fn attributes(&self) -> BTreeSet<&A> {
        self.heading.attributes()
    }
    fn get_type(&self, attr: A) -> Option<&T> {
        self.heading.get_type(attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        self.heading.attribute_types()
    }
    fn arity(&self) -> usize {
        let arity = self.heading.arity();
        assert_eq!(arity, self.values.len());
        arity
    }
    fn from_tuple(tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self {
        let mut heading = SimpleHeading::from_tuple(tuple);
        let values = tuple
            .attributes()
            .iter()
            .map(|attr| (**attr, tuple.get(**attr).unwrap().clone()))
            .collect();
        Self { heading, values }
    }
}

impl<A: Attribute, T: Type, V: Value> PartialEq for SimpleTuple<A, T, V> {
    fn eq(&self, other: &Self) -> bool {
        self.heading == other.heading && self.values == other.values
    }
}

impl<A: Attribute, T: Type, V: Value> Algebra<A, V> for SimpleTuple<A, T, V> {
    fn and(&self, other: &Self) -> Option<Self> {
        if !self.is_negated() && !other.is_negated() {
            if self.disjunction().is_some() || other.disjunction().is_some() {
                // Defer dealing with this case
                unimplemented!("conjunction of disjunctions");
            }

            let Some(heading) = self.heading.and(&other.heading) else {
                return None;
            };
            let common = self.common_attributes(&other);

            for attr in common.iter() {
                if self.get_type(*attr) != other.get_type(*attr) {
                    return None;
                }
                if self.get(*attr) != other.get(*attr) {
                    return None;
                }
            }
            let mut values = BTreeMap::<A, V>::new();

            for attr in heading.attributes() {
                let value = self
                    .values
                    .get(attr)
                    .or_else(|| other.values.get(attr))
                    .unwrap();

                values.insert(attr.clone(), value.clone());
            }
            Some(Self { heading, values })
        } else {
            unimplemented!()
        }
    }
    fn or(&self, other: &Self) -> Self {
        unimplemented!();
    }
    fn not(&self) -> Self {
        Self {
            heading: self.heading.not(),
            values: self.values.clone(),
        }
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        // if self.disjunction().is_some() {
        //     unimplemented!("tuple disjunction is not yet implemented")
        // }
        let attrs = attrs.into();
        self.project_aux(&attrs)

        // let heading = self.heading.project(attrs.clone());
        // let mut values = self.values.clone();
        // values.retain(|k, _v| attrs.contains(k));

        // Self { heading, values }
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        if self.disjunction().is_some() {
            unimplemented!("tuple disjunction")
        }
        let attrs = attrs.into();
        let heading = self.heading.remove(attrs.clone());
        let mut values = self.values.clone();
        values.retain(|k, _v| !attrs.contains(k));

        Self { heading, values }
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Result<Self, AlgebraError> {
        if self.disjunction().is_some() {
            unimplemented!("tuple disjunction")
        }
        let mapping = mapping.into();
        let heading = self.heading.rename(mapping.clone())?;

        let mut values = BTreeMap::new();
        for (k, v) in self.values.iter() {
            let new_k = mapping.get(k).unwrap_or(k).clone();

            values.insert(new_k, v.clone());
        }
        let renamed = Self { heading, values };
        if self.arity() == renamed.arity() {
            Ok(renamed)
        } else {
            Err(AlgebraError::DuplicateAttribute)
        }
    }
    fn compose(&self, other: &Self) -> Option<Self> {
        let common = self.heading.common_attributes(&other.heading);

        // This can be optimized.
        self.and(&other).map(|r| r.remove(common))
    }

    fn is_negated(&self) -> bool {
        self.heading.is_negated()
    }

    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, V>>> {
        if self.heading.disjunction().is_none() {
            &None
        } else {
            unimplemented!("tuple disjunction")
        }
    }
}

impl<A: Attribute, T: Type, V: Value> SimpleTuple<A, T, V> {
    pub fn project_aux(&self, attrs: &HashSet<A>) -> Self {
        if self.disjunction().is_some() {
            unimplemented!("tuple disjunction is not yet implemented")
        }
        let heading = self.heading.project(attrs.clone());
        let mut values = self.values.clone();
        values.retain(|k, _v| attrs.contains(k));

        Self { heading, values }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tuple() {
        let w1 = LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8]);
        let p1 = LoamValue::Ptr(9, 10);
        let p2 = LoamValue::Ptr(11, 12);

        let wt = w1.type_of();
        let pt = p1.type_of();
        assert_eq!(1, pt);
        assert_eq!(2, wt);

        let (a1, a2, a3) = (5, 6, 7);

        let t1 = SimpleTuple::new([(a1, w1), (a2, p1)]);

        assert_eq!(2, t1.arity());
        assert_eq!(wt, *t1.get_type(a1).unwrap());
        assert_eq!(pt, *t1.get_type(a2).unwrap());
        assert_eq!(w1, *t1.get(a1).unwrap());
        assert_eq!(p1, *t1.get(a2).unwrap());

        assert!(t1 != t1.not());
        assert_eq!(t1, t1.not().not());

        let t2 = SimpleTuple::new([(a2, p1), (a3, p2)]);
        let t1andt2 = t1.and(&t2).unwrap();
        let t2andt1 = t2.and(&t1).unwrap();
        assert_eq!(t1andt2, t2andt1);
        assert_eq!(3, t1andt2.arity());
        assert_eq!(w1, *t1andt2.get(a1).unwrap());
        assert_eq!(p1, *t1andt2.get(a2).unwrap());
        assert_eq!(p2, *t1andt2.get(a3).unwrap());

        let t3 = t1.project([(a1)]);
        assert_eq!(1, t3.arity());
        assert_eq!(w1, *t3.get(a1).unwrap());
        assert_eq!(wt, *t3.get_type(a1).unwrap());
        assert_eq!(None, t3.get(a2));

        let t4 = t1.remove([(a2)]);
        assert_eq!(1, t4.arity());
        assert_eq!(w1, *t4.get(a1).unwrap());
        assert_eq!(wt, *t4.get_type(a1).unwrap());
        assert_eq!(None, t4.get(a2));
        assert_eq!(t3, t4);

        let t5 = t1.rename([(a1, a3), (a2, a1)]).unwrap();
        assert_eq!(2, t1.arity());
        assert_eq!(w1, *t5.get(a3).unwrap());
        assert_eq!(p1, *t5.get(a1).unwrap());
        assert_eq!(wt, *t5.get_type(a3).unwrap());
        assert_eq!(pt, *t5.get_type(a1).unwrap());

        let t6 = t1.rename([(a1, a2), (a2, a1)]).unwrap();
        assert_eq!(2, t1.arity());
        assert_eq!(w1, *t6.get(a2).unwrap());
        assert_eq!(p1, *t6.get(a1).unwrap());
        assert_eq!(wt, *t6.get_type(a2).unwrap());
        assert_eq!(pt, *t6.get_type(a1).unwrap());

        assert_eq!(Err(AlgebraError::DuplicateAttribute), t1.rename([(a1, a2)]));

        let t8 = t1.compose(&t2).unwrap();
        let t8a = t2.compose(&t1).unwrap();
        assert_eq!(t8, t8a);
        assert_eq!(2, t8.arity());
        assert_eq!(w1, *t8.get(a1).unwrap());
        assert_eq!(None, t8.get(a2));
        assert_eq!(p2, *t8.get(a3).unwrap());
    }
}
