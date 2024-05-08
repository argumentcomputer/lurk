use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::marker::PhantomData;

use crate::loam::algebra::{Algebra, AlgebraError};
use crate::loam::tuple::Tuple;
use crate::loam::{Attribute, Type, Value};

pub trait Heading<A: Attribute, T: Type, V: Value>: Debug + Sized + Clone {
    fn attributes(&self) -> BTreeSet<&A>;
    fn get_type(&self, attr: A) -> Option<&T>;
    fn attribute_types(&self) -> &BTreeMap<A, T>;
    fn arity(&self) -> usize;
    fn common_attributes<'a, 'b>(&'a self, other: &'b Self) -> HashSet<A>
    where
        'b: 'a,
    {
        let mut common = HashSet::new();

        if self.arity() <= other.arity() {
            for attr in self.attributes() {
                if other.get_type(*attr).is_some() {
                    common.insert(*attr);
                }
            }
            common
        } else {
            other.common_attributes(self)
        }
    }
    fn from_tuple(tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self;
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialOrd)]
pub struct SimpleHeading<A: Attribute, T: Type, V: Value> {
    pub(crate) attributes: BTreeMap<A, T>,
    is_negated: bool,
    disjunction: Option<BTreeSet<BTreeMap<A, T>>>,
    _p: PhantomData<V>,
}

impl<A: Attribute, T: Type, V: Value> SimpleHeading<A, T, V> {
    pub fn new(is_negated: bool) -> Self {
        SimpleHeading {
            attributes: Default::default(),
            is_negated,
            disjunction: None,
            _p: Default::default(),
        }
    }

    pub(crate) fn add_attribute(&mut self, attr: A, typ: T) {
        self.attributes.insert(attr, typ);
    }
}
impl<A: Attribute, T: Type, V: Value> Heading<A, T, V> for SimpleHeading<A, T, V> {
    // TODO: implement iterator
    fn attributes(&self) -> BTreeSet<&A> {
        // Make this OnceOnly, after heading is frozen.
        let mut set = BTreeSet::new();

        for key in self.attributes.keys() {
            set.insert(key);
        }
        set
    }
    fn get_type(&self, attr: A) -> Option<&T> {
        self.attributes.get(&attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        &self.attributes
    }

    fn arity(&self) -> usize {
        self.attributes.len()
    }
    fn from_tuple(tuple: &(impl Tuple<A, T, V> + Algebra<A, V>)) -> Self {
        let mut heading = SimpleHeading::new(tuple.is_negated());

        for attr in tuple.attributes().iter() {
            if let Some(t) = tuple.get_type(**attr) {
                heading.attributes.insert(**attr, *t);
            }
        }

        heading
    }
}

impl<A: Attribute, T: Type, V: Value> PartialEq for SimpleHeading<A, T, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.arity() != other.arity() {
            return false;
        };

        if self.is_negated != other.is_negated {
            return false;
        }

        let common = self.common_attributes(other);

        if common.len() != self.arity() {
            return false;
        };

        common
            .iter()
            .all(|attr| self.get_type(*attr) == other.get_type(*attr))
            && &self.disjunction == other.disjunction()
    }
}

impl<A: Attribute, T: Type, V: Value> Algebra<A, T> for SimpleHeading<A, T, V> {
    fn not(&self) -> Self {
        Self {
            attributes: self.attributes.clone(),
            is_negated: !self.is_negated,
            disjunction: self.disjunction.clone(),
            _p: Default::default(),
        }
    }
    fn and(&self, other: &Self) -> Option<Self> {
        if !self.is_negated() && !other.is_negated() {
            if self.disjunction.is_some() || other.disjunction.is_some() {
                // Defer dealing with this case
                unimplemented!("conjunction of disjunctions");
            }
            let common = self.common_attributes(other);
            let mut new_heading = Self::new(self.is_negated());
            let compatible = common
                .iter()
                .all(|attr| self.get_type(*attr) == other.get_type(*attr));

            if !compatible {
                // Empty heading, not None.
                return Some(new_heading);
            };

            for attr in self.attributes().iter() {
                new_heading.add_attribute(**attr, *self.get_type(**attr).unwrap());
            }
            for attr in other.attributes().iter() {
                if common.get(attr).is_none() {
                    new_heading.add_attribute(**attr, *other.get_type(**attr).unwrap());
                }
            }
            Some(new_heading)
        } else if self.is_negated() {
            if other.is_negated() {
                // DeMorgan's
                Some(self.not().or(&other.not()).not())
            } else {
                todo!("negated heading and non-negated heading");
            }
        } else {
            let mut new_heading = Self::new(false);

            for attr in self.attributes().iter() {
                if other.get_type(**attr).is_some() {
                    continue;
                }

                let mut a = true;

                if let Some(o) = other.disjunction() {
                    for d in o.iter() {
                        if d.get(*attr).is_some() {
                            a = false;
                            continue;
                        }
                        if !a {
                            continue;
                        }
                    }
                }
                if a {
                    new_heading.add_attribute(**attr, *self.get_type(**attr).unwrap())
                }
            }

            Some(new_heading)
        }
    }
    fn or(&self, other: &Self) -> Self {
        if self == other {
            // If we can require that constructed headings are frozen, we can avoid this duplication.
            self.clone()
        } else {
            let mut disjunction = self
                .disjunction
                .as_ref()
                .map(|d| d.clone())
                .unwrap_or(Default::default());

            if other.is_negated() {
                unimplemented!("disjunction with negation");
            }

            disjunction.insert(other.attribute_types().clone());

            Self {
                attributes: self.attributes.clone(),
                is_negated: self.is_negated(),
                disjunction: Some(disjunction),
                _p: Default::default(),
            }
        }
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attrs = attrs.into();
        let mut attributes = self.attributes.clone();
        if !self.is_negated() {
            attributes.retain(|k, _v| attrs.contains(k));
        }

        let disjunction = self.disjunction.as_ref().and_then(|disj| {
            let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
            for d in disj.iter() {
                let mut a = d.clone();
                a.retain(|k, _v| attrs.contains(k));
                disjunction.insert(a);
            }
            if disjunction.is_empty() {
                None
            } else {
                Some(disjunction)
            }
        });

        Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
            _p: Default::default(),
        }
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attrs = attrs.into();
        let mut attributes = self.attributes.clone();
        if !self.is_negated() {
            attributes.retain(|k, _v| !attrs.contains(k));
        }

        let disjunction = self.disjunction.as_ref().and_then(|disj| {
            let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
            for d in disj.iter() {
                let mut a = d.clone();
                a.retain(|k, _v| !attrs.contains(k));
                disjunction.insert(a);
            }
            if disjunction.is_empty() {
                None
            } else {
                Some(disjunction)
            }
        });
        Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
            _p: Default::default(),
        }
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Result<Self, AlgebraError> {
        let mapping = mapping.into();
        let mut attributes = BTreeMap::new();
        for (k, v) in self.attributes.iter() {
            let new_k = mapping.get(k).unwrap_or(k).clone();

            attributes.insert(new_k, v.clone());
        }

        if attributes.len() != self.attributes.len() {
            Err(AlgebraError::DuplicateAttribute)?;
        }

        let disjunction = self.disjunction.as_ref().and_then(|disj| {
            let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
            for d in disj.iter() {
                let mut a = BTreeMap::new();
                for (k, v) in d.iter() {
                    let new_k = mapping.get(k).unwrap_or(k).clone();

                    a.insert(new_k, v.clone());
                }
                disjunction.insert(a);
            }
            if disjunction.is_empty() {
                None
            } else {
                Some(disjunction)
            }
        });
        Ok(Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
            _p: Default::default(),
        })
    }
    fn compose(&self, other: &Self) -> Option<Self> {
        let common = self.common_attributes(other);

        // This can be optimized.
        self.and(other).map(|r| r.remove(common))
    }
    fn is_negated(&self) -> bool {
        self.is_negated
    }
    fn disjunction(&self) -> &Option<BTreeSet<BTreeMap<A, T>>> {
        &self.disjunction
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loam::{Attr, BubbaBear, Typ};
    //    use crate::schema::{LoamElement, LoamValue};

    type V = BubbaBear;

    #[test]
    fn test_heading() {
        let heading0 = SimpleHeading::<Attr, Typ, V>::default();
        assert_eq!(0, heading0.arity());

        let mut heading1 = SimpleHeading::<Attr, Typ, V>::default();
        heading1.add_attribute(1, 100);

        let mut heading2 = SimpleHeading::<Attr, Typ, V>::default();
        heading2.add_attribute(2, 200);

        let mut heading3 = SimpleHeading::<Attr, Typ, V>::default();
        heading3.add_attribute(3, 300);

        let mut heading1_2 = SimpleHeading::<Attr, Typ, V>::default();
        heading1_2.add_attribute(1, 100);
        heading1_2.add_attribute(2, 200);

        let mut heading1x_3 = SimpleHeading::<Attr, Typ, V>::default();
        heading1x_3.add_attribute(1, 101);
        heading1x_3.add_attribute(3, 300);

        let mut heading1_2_3 = SimpleHeading::<Attr, Typ, V>::default();
        heading1_2_3.add_attribute(1, 100);
        heading1_2_3.add_attribute(2, 200);
        heading1_2_3.add_attribute(3, 300);

        let heading1and_1_2 = heading1.and(&heading1_2).unwrap();
        let heading1x_3and1_2 = heading1x_3.and(&heading1_2).unwrap();
        let heading1_2and_not1 = heading1_2.and(&heading1.not()).unwrap();
        let heading1_2or1_2 = heading1_2.or(&heading1_2);
        let heading1or2 = heading1.or(&heading2);
        let heading1_2_3and_not1_2 = heading1_2_3.and(&heading1or2.not()).unwrap();

        // unimplemented
        // let heading1or2and_3 = heading1or2.and(&heading3);
        // let heading3and_1or2 = heading3.and(&heading1or2);

        // arity
        assert_eq!(1, heading1.arity());
        assert_eq!(2, heading1_2.arity());
        assert_eq!(3, heading1_2_3.arity());

        // project
        assert_eq!(heading0, heading1.project([]));
        assert_eq!(heading1, heading1.project([1]));
        assert_eq!(heading1_2, heading1_2_3.project([1, 2]));
        // TODO: Should this be an error?
        assert_eq!(heading1_2, heading1_2_3.project([1, 2, 12345]));

        // remove
        assert_eq!(heading0, heading1.remove([1]));
        assert_eq!(heading3, heading1_2_3.remove([1, 2]));
        assert_eq!(heading3, heading1_2_3.remove([1, 2, 12345]));

        // rename
        let h = heading1_2_3.rename([(1, 9), (2, 10)]).unwrap();
        assert_eq!(3, h.arity());
        assert_eq!(heading3, h.project([3]));
        assert!(h.get_type(1).is_none());
        assert!(h.get_type(2).is_none());
        assert_eq!(Some(100), h.get_type(9).cloned());
        assert_eq!(Some(200), h.get_type(10).cloned());
        assert_eq!(
            Err(AlgebraError::DuplicateAttribute),
            heading1_2_3.rename([(1, 2)])
        );

        // compose
        assert_eq!(heading2, heading1.compose(&heading1_2).unwrap());
        assert_eq!(heading1_2, heading3.compose(&heading1_2_3).unwrap());

        // get_type
        assert_eq!(Some(100), heading1.get_type(1).cloned());
        assert_eq!(Some(100), heading1_2.get_type(1).cloned());
        assert_eq!(Some(200), heading1_2.get_type(2).cloned());

        // common_attributes
        assert_eq!(1, heading1.common_attributes(&heading1_2).len());
        assert!(heading1 != heading1_2);
        assert_eq!(2, heading1_2_3.common_attributes(&heading1_2).len());

        // and
        assert!(heading1 != heading1and_1_2);
        assert_eq!(heading1and_1_2, heading1_2);
        assert_eq!(heading1and_1_2, heading1_2);
        assert_eq!(heading2, heading1_2and_not1);
        assert_eq!(heading3, heading1_2_3and_not1_2);
        // Type mismatch on common attribute yields empty conjunction.
        assert_eq!(heading0, heading1x_3and1_2);

        // or
        assert_eq!(heading1_2, heading1_2or1_2);
        assert!(heading1_2or1_2 != heading1);
        assert!(heading1or2 != heading1);
        assert!(heading2 != heading1or2);
        assert!(heading1_2 != heading1or2);

        // not
        assert!(heading1 != heading1.not());
        assert_eq!(heading1, heading1.not().not());
    }
}
