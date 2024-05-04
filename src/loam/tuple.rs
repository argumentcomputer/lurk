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

impl<A: Attribute, T: Type, V: Value> PartialEq for Tuple<A, T, V> {
    fn eq(&self, other: &Self) -> bool {
        self.heading == other.heading && self.values == other.values
    }
}

impl<A: Attribute, T: Type, V: Value> Algebra<A, V> for Tuple<A, T, V> {
    fn and(&self, other: &Self) -> Self {
        if !self.is_negated() && !other.is_negated() {
            if self.disjunction().is_some() || other.disjunction().is_some() {
                // Defer dealing with this case
                unimplemented!("conjunction of disjunctions");
            }

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
        let attrs = attrs.into();
        let heading = self.heading.project(attrs.clone());
        let mut values = self.values.clone();
        values.retain(|k, _v| attrs.contains(k));

        Self { heading, values }
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attrs = attrs.into();
        let heading = self.heading.remove(attrs.clone());
        let mut values = self.values.clone();
        values.retain(|k, _v| !attrs.contains(k));

        Self { heading, values }
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Self {
        todo!();
    }
    fn compose(&self, other: &Self) -> Self {
        todo!();
    }

    // TODO: Move this and disjunction to Algebra.
    fn is_negated(&self) -> bool {
        self.heading.is_negated()
    }

    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, V>>> {
        if self.heading.disjunction().is_none() {
            &None
        } else {
            unimplemented!()
        }
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

        let t1 = Tuple::new([(a1, w1), (a2, p1)]);

        assert_eq!(2, t1.arity());
        assert_eq!(wt, *t1.attribute_type(a1).unwrap());
        assert_eq!(pt, *t1.attribute_type(a2).unwrap());
        assert_eq!(w1, *t1.get(a1).unwrap());
        assert_eq!(p1, *t1.get(a2).unwrap());

        assert!(t1 != t1.not());
        assert_eq!(t1, t1.not().not());

        let t2 = Tuple::new([(a2, p1), (a3, p2)]);
        let t1andt2 = t1.and(&t2);
        let t2andt1 = t2.and(&t1);
        assert_eq!(t1andt2, t2andt1);
        assert_eq!(3, t1andt2.arity());
        assert_eq!(w1, *t1andt2.get(a1).unwrap());
        assert_eq!(p1, *t1andt2.get(a2).unwrap());
        assert_eq!(p2, *t1andt2.get(a3).unwrap());

        let t3 = t1.project([(a1)]);
        assert_eq!(1, t3.arity());
        assert_eq!(w1, *t3.get(a1).unwrap());
        assert_eq!(wt, *t3.attribute_type(a1).unwrap());
        assert_eq!(None, t3.get(a2));

        let t4 = t1.remove([(a2)]);
        assert_eq!(1, t4.arity());
        assert_eq!(w1, *t4.get(a1).unwrap());
        assert_eq!(wt, *t4.attribute_type(a1).unwrap());
        assert_eq!(None, t4.get(a2));

        assert_eq!(t3, t4);
    }
}
