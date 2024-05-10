use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use thiserror::Error;

use crate::loam::algebra::{Algebra, AlgebraError};
use crate::loam::heading::{Heading, SimpleHeading};
use crate::loam::tuple::{SimpleTuple, Tuple};
use crate::loam::{Attribute, Type, Value};

use super::schema::{LoamElement, LoamValue};

#[derive(Error, Debug, PartialEq)]
pub enum RelationError {
    #[error("Duplicate Key")]
    DuplicateKey,
    #[error("Incompatible Sense")]
    IncompatibleSense,
    #[error("Incompatible Heading")]
    IncompatibleHeading,
}

pub trait Relation<A: Attribute, T: Type, V: Value>: Heading<A, T, V> + Algebra<A, V> {
    // Infinite or unmaterialized relations may lack a reportable cardinality.
    fn cardinality(&self) -> Option<usize>;
    fn key(&self) -> &Vec<A>;
    // If key is unspecified, all attributes will be used, in arbitrary order.
    fn new<I: IntoIterator<Item = Tup>, Tup: Tuple<A, T, V> + Algebra<A, V>>(
        tuples: I,
        key: Option<Vec<A>>,
    ) -> Result<Self, RelationError>
    where
        Self: Sized;
    fn empty(heading: SimpleHeading<A, T, V>, key: Option<Vec<A>>) -> Self;

    // The same tuple can be inserted more than once without changing the relation. If a distinct tuple with an existing
    // key is inserted, a RelationError::DuplicateKey error is returned.
    fn insert(&mut self, tuple: (impl Tuple<A, T, V> + Algebra<A, V>))
        -> Result<(), RelationError>;
}

#[derive(Clone, Debug, PartialEq)]
pub struct SimpleRelation<A: Attribute, T: Type, V: Value> {
    pub(crate) heading: SimpleHeading<A, T, V>,
    pub(crate) key: Vec<A>,
    pub(crate) is_negated: bool,
    pub(crate) tuples: BTreeMap<Vec<V>, SimpleTuple<A, T, V>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ComputedRelation<A: Attribute, T: Type, V: Value> {
    pub(crate) heading: SimpleHeading<A, T, V>,
    pub(crate) key: Vec<A>,
    pub(crate) is_negated: bool,
    pub(crate) predicate: Option<fn(&SimpleTuple<A, T, V>) -> bool>,
    // - A hint is a function from a set of attributes to a tuple intended to satisfy the predicate.
    // - The result will be checked by the predicate, so theoretically need not satisfy.
    // - In theory, there could be multiple hints for a given input tuple shape (the attributes).
    // - Hints could also return relations.
    // - If all these changes were made, hints could function as guessing strategies.
    // - TODO: The input shape should be specified as a Heading (including types), not just by the input attributes.
    pub(crate) hints:
        BTreeMap<BTreeSet<A>, fn(&SimpleTuple<A, T, V>) -> Option<SimpleTuple<A, T, V>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Rel<A: Attribute, T: Type, V: Value> {
    Simple(SimpleRelation<A, T, V>),
    Computed(ComputedRelation<A, T, V>),
}

impl<A: Attribute, T: Type, V: Value> From<SimpleRelation<A, T, V>> for Rel<A, T, V> {
    fn from(simple: SimpleRelation<A, T, V>) -> Self {
        Self::Simple(simple)
    }
}

impl<A: Attribute, T: Type, V: Value> From<ComputedRelation<A, T, V>> for Rel<A, T, V> {
    fn from(computed: ComputedRelation<A, T, V>) -> Self {
        Self::Computed(computed)
    }
}

impl<A: Attribute, T: Type, V: Value> Relation<A, T, V> for SimpleRelation<A, T, V> {
    fn cardinality(&self) -> Option<usize> {
        Some(self.tuples.len())
    }
    fn key(&self) -> &Vec<A> {
        &self.key
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
        let mut key = key.unwrap_or_else(|| heading.attributes().into_iter().collect());
        key.sort();

        Self {
            heading,
            tuples: Default::default(),
            key,
            is_negated: false,
        }
    }

    // This does not type-check the tuple itself. Tuple is assumed to conform to its own header.
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

        self.insert_with_key(k, simple_tuple)?;

        Ok(())
    }
}
impl<A: Attribute, T: Type, V: Value> Relation<A, T, V> for Rel<A, T, V> {
    fn cardinality(&self) -> Option<usize> {
        match self {
            Self::Simple(r) => r.cardinality(),
            Self::Computed(_) => None,
        }
    }
    fn key(&self) -> &Vec<A> {
        match self {
            Self::Simple(r) => &r.key,
            Self::Computed(r) => &r.key,
        }
    }
    fn new<I: IntoIterator<Item = Tup>, Tup: Tuple<A, T, V> + Algebra<A, V>>(
        tuples: I,
        key: Option<Vec<A>>,
    ) -> Result<Self, RelationError> {
        Ok(Self::Simple(SimpleRelation::new(tuples, key)?))
    }
    fn empty(heading: SimpleHeading<A, T, V>, key: Option<Vec<A>>) -> Self {
        Self::Simple(SimpleRelation::empty(heading, key))
    }

    // This does not type-check the tuple itself. Tuple is assumed to conform to its own header.
    fn insert(
        &mut self,
        tuple: (impl Tuple<A, T, V> + Algebra<A, V>),
    ) -> Result<(), RelationError> {
        match self {
            Self::Simple(r) => r.insert(tuple),
            Self::Computed(_) => unimplemented!(),
        }
    }
}

impl SimpleRelation<LoamElement, LoamElement, LoamValue<LoamElement>> {
    fn make<I: IntoIterator<Item = Vec<(LoamElement, LoamValue<LoamElement>)>>>(
        tuples: I,
        key: Option<Vec<LoamElement>>,
    ) -> Result<Self, RelationError> {
        Self::new(tuples.into_iter().map(SimpleTuple::new), key)
    }
}
impl Rel<LoamElement, LoamElement, LoamValue<LoamElement>> {
    fn make<I: IntoIterator<Item = Vec<(LoamElement, LoamValue<LoamElement>)>>>(
        tuples: I,
        key: Option<Vec<LoamElement>>,
    ) -> Result<Self, RelationError> {
        Ok(Self::Simple(SimpleRelation::make(tuples, key)?))
    }
}
impl<A: Attribute, T: Type, V: Value> Rel<A, T, V> {
    // tuple heading is assumed to match self.heading.
    pub fn contains(&self, tuple: &SimpleTuple<A, T, V>) -> bool {
        match self {
            Self::Computed(r) => {
                if let Some(predicate) = r.predicate {
                    predicate(tuple)
                } else {
                    true
                }
            }
            Self::Simple(r) => r.contains(tuple),
        }
    }
}

impl<A: Attribute, T: Type, V: Value> SimpleRelation<A, T, V> {
    // tuple heading is assumed to match self.heading.
    pub fn contains(&self, tuple: &SimpleTuple<A, T, V>) -> bool {
        let key_values: Vec<V> = self
            .key
            .clone()
            .iter()
            .map(|attr| tuple.get(*attr).unwrap().clone())
            .collect();

        self.tuples.contains_key(&key_values)
    }

    fn insert_with_key(
        &mut self,
        key: Vec<V>,
        tuple: SimpleTuple<A, T, V>,
    ) -> Result<(), RelationError> {
        if tuple.is_negated() != self.is_negated() {
            return Err(RelationError::IncompatibleSense);
        }
        if tuple.attributes() != self.attributes() {
            return Err(RelationError::IncompatibleHeading);
        }
        for attr in tuple.attributes() {
            if tuple.get_type(attr) != self.get_type(attr) {
                return Err(RelationError::IncompatibleHeading);
            }
        }

        if let Some(found) = self.tuples.get(&key) {
            if found != &tuple {
                return Err(RelationError::DuplicateKey);
            }
        }
        let _ = self.tuples.insert(key, tuple);

        Ok(())
    }
}
impl<A: Attribute, T: Type, V: Value> ComputedRelation<A, T, V> {
    fn new(
        heading: SimpleHeading<A, T, V>,
        key: Option<Vec<A>>,
        is_negated: bool,
        predicate: Option<fn(&SimpleTuple<A, T, V>) -> bool>,
        hints: Option<
            BTreeMap<BTreeSet<A>, fn(&SimpleTuple<A, T, V>) -> Option<SimpleTuple<A, T, V>>>,
        >,
    ) -> Self {
        let mut key = key.unwrap_or_else(|| heading.attributes().into_iter().collect());
        key.sort();

        Self {
            heading,
            key,
            is_negated,
            predicate,
            hints: hints.unwrap_or_else(|| Default::default()),
        }
    }
    fn is_negated(&self) -> bool {
        self.is_negated
    }

    fn not(&self) -> Self {
        Self {
            heading: self.heading.clone(),
            key: self.key.clone(),
            is_negated: self.is_negated,
            predicate: self.predicate,
            hints: Default::default(),
        }
    }

    pub fn contains(&self, tuple: &SimpleTuple<A, T, V>) -> bool {
        if let Some(predicate) = self.predicate {
            predicate(tuple)
        } else {
            true
        }
    }

    pub fn and_tuple(&self, tuple: &SimpleTuple<A, T, V>) -> Option<SimpleTuple<A, T, V>> {
        let common = self.common_attributes(tuple);

        for attr in common.iter() {
            if self.get_type(*attr) != tuple.get_type(*attr) {
                return None;
            };
        }

        let projected = tuple.project(common.clone());

        if self.attributes().is_subset(&common) {
            if let Some(predicate) = self.predicate {
                predicate(&projected).then_some(tuple.clone())
            } else {
                Some(tuple.clone())
            }
        } else {
            let common = common.into_iter().collect::<BTreeSet<_>>();

            self.hints.get(&common).and_then(|hint| {
                hint(tuple).and_then(|extended| {
                    if let Some(predicate) = self.predicate {
                        if predicate(&extended) {
                            extended.and(&projected)
                        } else {
                            None
                        }
                    } else {
                        extended.and(&projected)
                    }
                })
            })
        }
    }
}
impl<A: Attribute, T: Type, V: Value> Heading<A, T, V> for SimpleRelation<A, T, V> {
    fn attributes(&self) -> HashSet<A> {
        self.heading.attributes()
    }
    fn get_type(&self, attr: A) -> Option<&T> {
        self.heading.get_type(attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        self.heading.attribute_types()
    }
    fn arity(&self) -> usize {
        self.heading.arity()
    }
    fn from_tuple(tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self {
        let heading = SimpleHeading::from_tuple(tuple);
        let mut relation = Self::empty(heading, None);

        relation.insert(tuple.clone()).unwrap();
        relation
    }
}
impl<A: Attribute, T: Type, V: Value> Heading<A, T, V> for ComputedRelation<A, T, V> {
    fn attributes(&self) -> HashSet<A> {
        self.heading.attributes()
    }
    fn get_type(&self, attr: A) -> Option<&T> {
        self.heading.get_type(attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        self.heading.attribute_types()
    }
    fn arity(&self) -> usize {
        self.heading.arity()
    }
    fn from_tuple(_tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self {
        unimplemented!();
    }
}
impl<A: Attribute, T: Type, V: Value> Heading<A, T, V> for Rel<A, T, V> {
    fn attributes(&self) -> HashSet<A> {
        match self {
            Self::Computed(r) => r.attributes(),
            Self::Simple(r) => r.attributes(),
        }
    }
    fn get_type(&self, attr: A) -> Option<&T> {
        match self {
            Self::Computed(r) => r.get_type(attr),
            Self::Simple(r) => r.get_type(attr),
        }
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        match self {
            Self::Computed(r) => r.attribute_types(),
            Self::Simple(r) => r.attribute_types(),
        }
    }
    fn arity(&self) -> usize {
        match self {
            Self::Computed(r) => r.arity(),
            Self::Simple(r) => r.arity(),
        }
    }
    fn from_tuple(tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self {
        Self::Simple(SimpleRelation::from_tuple(tuple))
    }
}

impl<A: Attribute, T: Type, V: Value> Algebra<A, V> for SimpleRelation<A, T, V> {
    fn and(&self, other: &Self) -> Option<Self> {
        if !self.is_negated() && !other.is_negated() {
            if self.disjunction().is_some() || other.disjunction().is_some() {
                // Defer dealing with this case
                unimplemented!("conjunction of disjunctions");
            }

            let Some(heading) = self.heading.and(&other.heading) else {
                return None;
            };

            let key = if self.key == other.key {
                Some(self.key.clone())
            } else {
                let mut key = self.key().clone();
                key.extend(&other.key);
                key.dedup();

                Some(key)
            };

            let (a, b) = if self.cardinality() <= other.cardinality() {
                (self, other)
            } else {
                (other, self)
            };

            let mut relation = Self::empty(heading, key);

            if self.heading == other.heading {
                // Intersection

                for (key, tuple) in a.tuples.iter() {
                    if b.contains(tuple) {
                        relation
                            .insert_with_key(key.clone(), tuple.clone())
                            .unwrap();
                    }
                }
            } else {
                for (_, tuplea) in a.tuples.iter() {
                    // TODO: Use indexes to avoid enumerating the whole product.
                    for (_, tupleb) in b.tuples.iter() {
                        if let Some(and_tuple) = tuplea.and(tupleb) {
                            relation.insert(and_tuple).unwrap();
                        }
                    }
                }
            }
            Some(relation)
        } else {
            let (positive, negative) = match (self.is_negated(), other.is_negated()) {
                (false, true) => (self, other),
                (true, false) => (other, self),
                (true, true) => unimplemented!(),
                (false, false) => unreachable!(),
            };

            assert_eq!(
                positive.heading, negative.heading,
                "incompatible headings for relation difference"
            );

            assert_eq!(
                positive.key, negative.key,
                "incompatible keys for relation difference"
            );

            let mut relation = Self::empty(positive.heading.clone(), Some(positive.key.clone()));

            for (k, tuple) in positive.tuples.iter() {
                // Less optimized but clearer: if !negative.contains(tuple) {
                if !negative.tuples.contains_key(k) {
                    relation.insert_with_key(k.to_vec(), tuple.clone()).unwrap();
                }
            }
            Some(relation)
        }
    }
    fn or(&self, other: &Self) -> Self {
        if self.heading != other.heading || self.is_negated() != other.is_negated() {
            // This can be implemented eventually.
            unimplemented!("disjunction of non-congruent relations is unimplemented")
        };

        let (a, b) = if self.cardinality() <= other.cardinality() {
            (self, other)
        } else {
            (other, self)
        };

        let mut relation = b.clone();

        for (_, tuple) in a.tuples.iter() {
            relation.insert(tuple.clone()).unwrap();
        }

        relation
    }
    fn not(&self) -> Self {
        Self {
            heading: self.heading.clone(),
            tuples: self.tuples.clone(),
            is_negated: !self.is_negated,
            key: self.key.clone(),
        }
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attributes = attrs.into();
        let heading = self.heading.project(attributes.clone());
        let key = if self.key.iter().all(|attr| attributes.contains(attr)) {
            self.key
                .iter()
                .cloned()
                .filter(|attr| attributes.contains(attr))
                .collect::<Vec<_>>()
        } else {
            heading.attributes().iter().cloned().collect::<Vec<_>>()
        };
        let mut relation = Self::empty(heading, Some(key.clone()));

        for tuple in self
            .tuples
            .values()
            .map(|tuple| tuple.project_aux(&attributes))
        {
            let key_values = key
                .clone()
                .iter()
                .map(|attr| tuple.get(*attr).unwrap().clone())
                .collect();

            match relation.insert_with_key(key_values, tuple) {
                Err(RelationError::DuplicateKey) => (),
                Ok(()) => (),
                Err(e) => panic!("{:?}", e),
            }
        }
        relation
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attributes = attrs.into();
        let to_project: HashSet<A> = self
            .attributes()
            .into_iter()
            .filter(|attr| !attributes.contains(attr))
            .collect();

        self.project(to_project)
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Result<Self, AlgebraError> {
        // TODO: This is very expensive because we rename all the tuples. A representation that stores tuples as vectors
        // ordered by a canonical attribute-order from the heading will not have that problem.

        let mapping = mapping.into();
        let heading = self.heading.rename(mapping.clone())?;
        let key = self
            .key
            .iter()
            .map(|attr| *mapping.get(attr).unwrap_or(attr))
            .collect::<Vec<_>>();

        let tuples = self
            .tuples
            .iter()
            .map(|(_k, tuple)| {
                let tuple = tuple.rename(mapping.clone()).unwrap();
                let key = key
                    .iter()
                    .map(|attr| tuple.get(*attr).unwrap().clone())
                    .collect::<Vec<_>>();
                (key, tuple)
            })
            .collect::<BTreeMap<_, _>>();

        Ok(Self {
            heading,
            key,
            is_negated: self.is_negated,
            tuples,
        })
    }
    fn compose(&self, other: &Self) -> Option<Self> {
        let common = self.heading.common_attributes(&other.heading);

        // This can be optimized.
        self.and(other).map(|r| r.remove(common))
    }
    fn is_negated(&self) -> bool {
        self.is_negated
    }
    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, V>>> {
        // Only the difference case is currently supported, so there will be no 'residual disjunction'.
        &None
    }
}
impl<A: Attribute, T: Type, V: Value> Algebra<A, V> for Rel<A, T, V> {
    fn and(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Simple(s), Self::Simple(c)) => s.and(c).map(Into::into), //|r| r.into()),
            (Self::Simple(s), Self::Computed(c)) | (Self::Computed(c), Self::Simple(s)) => {
                if !s.is_negated() && !c.is_negated() {
                    if s.disjunction().is_some() {
                        // Defer dealing with this case
                        unimplemented!("conjunction of disjunctions");
                    }

                    let Some(heading) = s.heading.and(&c.heading) else {
                        return None;
                    };

                    let key = if s.key == c.key {
                        Some(s.key.clone())
                    } else {
                        let mut key = s.key().clone();
                        key.extend(&c.key);
                        key.sort();
                        key.dedup();
                        Some(key)
                    };

                    let mut relation = SimpleRelation::empty(heading, key);

                    if s.heading == c.heading {
                        // Intersection

                        for (key, tuple) in s.tuples.iter() {
                            if c.contains(tuple) {
                                relation
                                    .insert_with_key(key.clone(), tuple.clone())
                                    .unwrap();
                            }
                        }
                    } else {
                        for (key, tuple) in s.tuples.iter() {
                            if let Some(and_tuple) = c.and_tuple(tuple) {
                                relation
                                    .insert_with_key(key.clone(), and_tuple.clone())
                                    .unwrap();
                            }
                        }
                    }
                    Some(relation.into())
                } else {
                    todo!()
                }
            }
            (Self::Computed(_s), Self::Computed(_c)) => unimplemented!(),
        }
    }
    fn or(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Simple(s), Self::Simple(c)) => s.or(c).into(),
            (Self::Simple(_s), Self::Computed(_c)) | (Self::Computed(_c), Self::Simple(_s)) => {
                todo!()
            }
            (Self::Computed(_s), Self::Computed(_c)) => unimplemented!(),
        }
    }
    fn not(&self) -> Self {
        match self {
            Self::Simple(r) => r.not().into(),
            Self::Computed(r) => r.not().into(),
        }
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        match self {
            Self::Simple(r) => Self::Simple(r.project(attrs)),
            Self::Computed(_r) => unimplemented!(),
        }
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        match self {
            Self::Simple(r) => Self::Simple(r.remove(attrs)),
            Self::Computed(_r) => unimplemented!(),
        }
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Result<Self, AlgebraError> {
        match self {
            Self::Simple(r) => r.rename(mapping).map(Self::Simple),
            Self::Computed(_r) => unimplemented!(),
        }
    }
    fn compose(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Simple(s), Self::Simple(c)) => s.compose(c).map(Into::into),
            (Self::Simple(s), Self::Computed(c)) => {
                let common = s.heading.common_attributes(&c.heading);
                self.and(other).map(|r| r.remove(common))
            }
            (Self::Computed(c), Self::Simple(s)) => {
                let common = s.heading.common_attributes(&c.heading);
                other.and(self).map(|r| r.remove(common))
            }
            (Self::Computed(_s), Self::Computed(_c)) => unimplemented!(),
        }
    }
    fn is_negated(&self) -> bool {
        match self {
            Self::Simple(r) => r.is_negated(),
            Self::Computed(r) => r.is_negated(),
        }
    }
    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, V>>> {
        // Only the difference case is currently supported, so there will be no 'residual disjunction'.
        &None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::loam::schema::{LoamElement, LoamValue};

    type LE = LoamElement;
    type LT = LoamElement;
    type LV = LoamValue<LoamElement>;

    #[test]
    fn test_simple_relation() {
        let empty_heading = SimpleHeading::<LE, LT, LV>::default();
        assert_eq!(0, empty_heading.arity());
        let mut r: SimpleRelation<LE, LT, LV> = SimpleRelation::empty(empty_heading, None);

        assert_eq!(Some(0), r.cardinality());
        assert_eq!(Vec::<LE>::new(), *r.key());

        let empty_tuple = SimpleTuple::new([]);
        r.insert(empty_tuple.clone()).unwrap();

        let r2 = SimpleRelation::new([empty_tuple], None).unwrap();
        assert_eq!(r, r2);

        let w1 = LoamValue::Wide([1, 2, 3, 4, 5, 6, 7, 8]);
        let w2 = LoamValue::Wide([10, 20, 30, 40, 50, 60, 70, 80]);
        let w3 = LoamValue::Wide([100, 200, 300, 400, 500, 600, 700, 800]);
        let p1 = LoamValue::Ptr(9, 10);
        let p2 = LoamValue::Ptr(11, 12);

        let wt = w1.type_of();
        let pt = p1.type_of();

        let (a1, a2, a3) = (5, 6, 7);

        // a1 | a2
        //--------
        // w1 | p1
        let r3 = SimpleRelation::new(
            [
                SimpleTuple::new([(a1, w1), (a2, p1)]),
                SimpleTuple::new([(a1, w1), (a2, p1)]),
            ],
            Some(vec![a1]),
        )
        .unwrap();
        assert_eq!(Some(1), r3.cardinality());
        assert_eq!(2, r3.attributes().len());

        // Heading
        assert_eq!(wt, *r3.get_type(a1).unwrap());
        assert_eq!(pt, *r3.get_type(a2).unwrap());

        // a1 | a2
        //--------
        // w1 | p1
        let r3a = SimpleRelation::make([vec![(a1, w1), (a2, p1)]], Some(vec![a1])).unwrap();
        assert_eq!(r3, r3a);

        let r4 = SimpleRelation::make(
            [vec![(a1, w1), (a2, p1)], vec![(a1, w1), (a2, p2)]],
            Some(vec![a1]),
        );
        assert_eq!(Err(RelationError::DuplicateKey), r4);

        // a1 | a2
        //--------
        // w2 | p1
        let r5 = SimpleRelation::make([vec![(a1, w2), (a2, p1)]], Some(vec![a1])).unwrap();

        // a1 | a2
        //--------
        // w1 | p1
        // w2 | p1
        let r3_or_r5 = r3.or(&r5);
        assert_eq!(Some(2), r3_or_r5.cardinality());

        // a1
        //---
        // w1
        // w2
        let r6 = r3_or_r5.project([a1]);
        assert_eq!(Some(2), r6.cardinality());
        assert_eq!(r6, r3_or_r5.remove([a2]));

        // a2
        //---
        // p1
        let r7 = r3_or_r5.project([a2]);
        assert_eq!(Some(1), r7.cardinality());
        assert_eq!(r7, r3_or_r5.remove([a1]));

        // Intersection
        assert_eq!(r3, r3_or_r5.and(&r3).unwrap());
        assert_eq!(r5, r3_or_r5.and(&r5).unwrap());

        // Difference: a.and(b.not())

        // a1 | a2
        //--------
        // w1 | p1
        assert_eq!(r3, r3_or_r5.and(&r5.not()).unwrap());

        // a1 | a2
        //--------
        // w2 | p1
        assert_eq!(r5, r3_or_r5.and(&r3.not()).unwrap());

        // a2 | a3
        //--------
        // p1 | w1
        // p2 | w2
        // p1 | w3
        let r8 = SimpleRelation::make(
            [
                vec![(a2, p1), (a3, w1)],
                vec![(a2, p2), (a3, w2)],
                vec![(a2, p1), (a3, w3)],
            ],
            Some(vec![a3]),
        )
        .unwrap();

        let r9 = r3_or_r5.and(&r8).unwrap();
        assert_eq!(3, r9.arity());
        assert_eq!(Some(4), r9.cardinality());

        let r10 = r8.rename([(a2, a3), (a3, a2)]).unwrap();
        assert_eq!(2, r10.arity());
        assert_eq!(Some(3), r10.cardinality());
        assert_eq!(pt, *r10.get_type(a3).unwrap());
        assert_eq!(wt, *r10.get_type(a2).unwrap());
        assert_eq!(Some(2), r10.project([a3]).cardinality());
    }

    #[test]
    fn test_simple_relation_predicate() {
        let (a1, a2, a3, a4) = (1, 2, 3, 4);
        let (w1, w2, w3, w4) = (
            LoamValue::Wide([1, 0, 0, 0, 0, 0, 0, 0]),
            LoamValue::Wide([2, 0, 0, 0, 0, 0, 0, 0]),
            LoamValue::Wide([3, 0, 0, 0, 0, 0, 0, 0]),
            LoamValue::Wide([4, 0, 0, 0, 0, 0, 0, 0]),
        );

        let mut heading = SimpleHeading::<LE, LT, LV>::default();
        heading.add_attribute(1, 2);
        heading.add_attribute(2, 2);
        heading.add_attribute(3, 2);

        let r = Rel::Computed(ComputedRelation {
            heading: heading.clone(),
            key: vec![a1, a2],
            is_negated: false,
            predicate: None,
            hints: Default::default(),
        });

        // a1 | a2 | a3
        //-------------
        // w1 | w2 | w3
        let r2 = Rel::make([vec![(a1, w1), (a2, w2), (a3, w3)]], Some(vec![a1, a2])).unwrap();

        let r3 = r.and(&r2).unwrap();
        let r3a = r2.and(&r).unwrap();
        assert_eq!(Some(1), r3.cardinality());
        assert_eq!(Some(1), r3a.cardinality());
        assert_eq!(r3, r3a);
        // join with unconstrained ComputedRelation (predicate none) yields self.
        assert_eq!(r2, r3);

        // Wrong heading. Panics.
        // let r4 =
        //     SimpleRelation::make([vec![(a1, w1), (a2, w2), (a4, w3)]], Some(vec![a1, a2])).unwrap();
        // let r5 = r.and(&r4).unwrap();

        let hints = {
            let mut hints = BTreeMap::default();

            fn hint(tuple: &SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>> {
                let a = tuple.get(1).and_then(LoamValue::wide_val).unwrap()[0];
                let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                let c = LoamValue::Wide([a + b, 0, 0, 0, 0, 0, 0, 0]);

                // TODO: better tuple manipulation API
                let mut extended = tuple.clone();
                extended.heading.add_attribute(3, 2);
                extended.values.insert(3, c);

                Some(extended)
            };

            hints.insert(
                BTreeSet::from([a1, a2]),
                hint as fn(&SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>>,
            );

            hints
        };

        let addition = Rel::Computed(ComputedRelation {
            heading,
            key: vec![a1, a2],
            is_negated: false,
            predicate: Some(|tuple| {
                let a = tuple.get(1).and_then(LoamValue::wide_val).unwrap()[0];
                let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                let c = tuple.get(3).and_then(LoamValue::wide_val).unwrap()[0];

                a + b == c
            }),
            hints,
        });

        // 1 + 2 = 3
        let r4 = r2.and(&addition).unwrap();
        assert_eq!(3, r4.arity());
        assert_eq!(Some(1), r4.cardinality());
        // r2 really does contain only an addition tuple.
        assert_eq!(r2, r4);
        // computational `and` is commutative
        assert_eq!(r4, addition.and(&r2).unwrap());
        // r2 is defined above to hold the correct result
        assert_eq!(r2, r4);

        let r5 = Rel::make([vec![(a1, w1), (a2, w2), (a3, w1)]], Some(vec![a1, a2])).unwrap();
        // 1 + 2 = 1
        let r6 = r5.and(&addition).unwrap();
        assert_eq!(3, r6.arity());
        assert_eq!(Some(0), r6.cardinality());

        // 1 + 1
        //
        // a1 | a2
        //--------
        // w1 | w2
        let r7 = Rel::make([vec![(a1, w1), (a2, w2)]], Some(vec![a1, a2])).unwrap();
        let r8 = r7.compose(&addition).unwrap();

        // a3
        //---
        // w3
        let r9 = Rel::make([vec![(a3, w3)]], Some(vec![a3])).unwrap();
        assert_eq!(1, r8.arity());
        assert_eq!(Some(1), r8.cardinality());
        assert_eq!(r9, r8);

        let r10 = Rel::make([vec![(a1, w1), (a2, w2), (a4, w4)]], Some(vec![a1, a2])).unwrap();
        let r11 = r10.and(&addition).unwrap();
        let r12 = r10.compose(&addition).unwrap();

        assert_eq!(4, r11.arity());
        assert_eq!(2, r12.arity());
        // Result is as expected when the extra a4 attribute is removed.
        assert_eq!(r2, r11.remove([a4]));

        // a4
        //---
        // w4
        let r13 = Rel::make([vec![(a4, w4)]], Some(vec![a4])).unwrap();

        // The a4 attribute has its original value.
        assert_eq!(r13, r11.project([a4]));

        let (hints, bad_hints) = {
            let mut hints = BTreeMap::default();
            let mut bad_hints = BTreeMap::default();

            // This contrived example will extend a tuple by adding a 4 attribute whose
            // values is 2 + its 2 attribute.
            fn extend_hint(tuple: &SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>> {
                let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                let d = LoamValue::Wide([b + 2, 0, 0, 0, 0, 0, 0, 0]);

                // TODO: better tuple manipulation API
                let mut extended = tuple.clone();
                extended.heading.add_attribute(4, 2);
                extended.values.insert(4, d);

                Some(extended)
            };

            // Like `extend_hint`, except this adds 3 -- which disagrees with the predicate relation below.
            fn bad_extend_hint(tuple: &SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>> {
                let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                let d = LoamValue::Wide([b + 3, 0, 0, 0, 0, 0, 0, 0]);

                // TODO: better tuple manipulation API
                let mut extended = tuple.clone();
                extended.heading.add_attribute(4, 2);
                extended.values.insert(4, d);

                Some(extended)
            };

            hints.insert(
                BTreeSet::from([a2]),
                extend_hint as fn(&SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>>,
            );

            bad_hints.insert(
                BTreeSet::from([a2]),
                bad_extend_hint as fn(&SimpleTuple<LE, LT, LV>) -> Option<SimpleTuple<LE, LT, LV>>,
            );

            (hints, bad_hints)
        };

        let extend = {
            let mut heading = SimpleHeading::<LE, LT, LV>::default();
            heading.add_attribute(2, 2);
            heading.add_attribute(4, 2);

            // This computed relation ensures that its 4 attribute is 2 + its 2 attribute.
            Rel::Computed(ComputedRelation {
                heading,
                key: vec![a2],
                is_negated: false,
                predicate: Some(|tuple| {
                    let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                    let d = tuple.get(4).and_then(LoamValue::wide_val).unwrap()[0];

                    d == b + 2
                }),
                hints: hints.clone(),
            })
        };
        let bad_extend = {
            let mut heading = SimpleHeading::<LE, LT, LV>::default();
            heading.add_attribute(2, 2);
            heading.add_attribute(4, 2);

            // This computed relation ensures that its 4 attribute is 2 + its 2 attribute.
            Rel::Computed(ComputedRelation {
                heading,
                key: vec![a2],
                is_negated: false,
                predicate: Some(|tuple| {
                    let b = tuple.get(2).and_then(LoamValue::wide_val).unwrap()[0];
                    let d = tuple.get(4).and_then(LoamValue::wide_val).unwrap()[0];

                    d == b + 2
                }),
                hints: bad_hints,
            })
        };

        // If we trust hints, we don't need to supply a predicate.
        let easy_extend = {
            let mut heading = SimpleHeading::<LE, LT, LV>::default();
            heading.add_attribute(2, 2);
            heading.add_attribute(4, 2);

            // This computed relation ensures that its 4 attribute is 2 + its 2 attribute.
            Rel::Computed(ComputedRelation {
                heading,
                key: vec![a2],
                is_negated: false,
                predicate: None,
                hints,
            })
        };

        assert_eq!(r11, r2.and(&extend).unwrap());
        // extend and easy_extend give the same result.
        assert_eq!(r11, r2.and(&easy_extend).unwrap());
        // Joining with bad_extend yields an empty relation.
        assert_eq!(Some(0), r2.and(&bad_extend).unwrap().cardinality());
    }
}
