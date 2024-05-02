use crate::loam::algebra::Algebra;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

mod algebra;

pub trait Attribute: Copy + Default + Eq + PartialEq + Hash + Debug + Ord {}
pub trait Type: Copy + Eq + Hash + Debug + Ord {}
pub trait AlgebraHeading<A: Attribute, T: Type>: Algebra<A, T> + Heading<A, T> {}

pub trait Heading<A: Attribute, T: Type>: Debug + Sized + Clone + Algebra<A, T> {
    fn new(is_negated: bool) -> Self;
    fn attributes(&self) -> BTreeSet<&A>;
    fn attribute_type(&self, attr: A) -> Option<&T>;
    fn attribute_types(&self) -> &BTreeMap<A, T>;
    fn arity(&self) -> usize;
    fn is_negated(&self) -> bool;
    fn add_attribute(&mut self, attr: A, typ: T);
    fn common_attributes<'a, 'b>(&'a self, other: &'b impl Heading<A, T>) -> HashSet<A>
    where
        'b: 'a,
    {
        let mut common = HashSet::new();

        if self.arity() <= other.arity() {
            for attr in self.attributes() {
                if other.attribute_type(*attr).is_some() {
                    common.insert(*attr);
                }
            }
            common
        } else {
            other.common_attributes(self)
        }
    }
    fn disjunction(&self) -> &BTreeSet<BTreeMap<A, T>>;
}

pub type Attr = usize;
impl Attribute for Attr {}

pub type Typ = usize;
impl Type for Typ {}

#[derive(Clone, Debug, Default)]
struct SimpleHeading<A, T> {
    attributes: BTreeMap<A, T>,
    is_negated: bool,
    disjunction: BTreeSet<BTreeMap<A, T>>,
}

impl<A: Attribute, T: Type> AlgebraHeading<A, T> for SimpleHeading<A, T> {}

impl<A: Attribute, T: Type> Heading<A, T> for SimpleHeading<A, T> {
    fn new(is_negated: bool) -> Self {
        SimpleHeading {
            attributes: Default::default(),
            is_negated,
            disjunction: Default::default(),
        }
    }
    // TODO: implement iterator
    fn attributes(&self) -> BTreeSet<&A> {
        // Make this OnceOnly, after heading is frozen.
        let mut set = BTreeSet::new();

        for key in self.attributes.keys() {
            set.insert(key);
        }
        set
    }
    fn attribute_type(&self, attr: A) -> Option<&T> {
        self.attributes.get(&attr)
    }
    fn attribute_types(&self) -> &BTreeMap<A, T> {
        &self.attributes
    }

    fn arity(&self) -> usize {
        self.attributes.len()
    }
    fn is_negated(&self) -> bool {
        self.is_negated
    }
    fn disjunction(&self) -> &BTreeSet<BTreeMap<A, T>> {
        &self.disjunction
    }
    fn add_attribute(&mut self, attr: A, typ: T) {
        self.attributes.insert(attr, typ);
    }
}

impl<A: Attribute, T: Type> Algebra<A, T> for SimpleHeading<A, T> {
    fn equal(&self, other: &impl AlgebraHeading<A, T>) -> bool {
        if self.arity() != other.arity() {
            return false;
        };

        let common = self.common_attributes(other);

        if common.len() != self.arity() {
            return false;
        };

        common
            .iter()
            .all(|attr| self.attribute_type(*attr) == other.attribute_type(*attr))
            && &self.disjunction == other.disjunction()
    }
    fn not(&self) -> Self {
        Self {
            attributes: self.attributes.clone(),
            is_negated: !self.is_negated,
            disjunction: self.disjunction.clone(),
        }
    }
    fn and(&self, other: &(impl Algebra<A, T> + AlgebraHeading<A, T>)) -> Self {
        if !self.is_negated() && !other.is_negated() {
            if !self.disjunction().is_empty() || !other.disjunction().is_empty() {
                unimplemented!("conjunction of disjunctions");
            }
            let common = self.common_attributes(other);
            let mut new_heading = Self::new(self.is_negated());
            let compatible = common
                .iter()
                .all(|attr| self.attribute_type(*attr) == other.attribute_type(*attr));

            if !compatible {
                return new_heading;
            };

            for attr in self.attributes().iter() {
                new_heading.add_attribute(**attr, *self.attribute_type(**attr).unwrap());
            }
            for attr in other.attributes().iter() {
                if common.get(attr).is_none() {
                    new_heading.add_attribute(**attr, *other.attribute_type(**attr).unwrap());
                }
            }
            new_heading
        } else if self.is_negated() {
            if other.is_negated() {
                // DeMorgan's
                self.not().or(&other.not()).not()
            } else {
                todo!("negated heading and non-negated heading");
            }
        } else {
            let mut new_heading = Self::new(false);

            for attr in self.attributes().iter() {
                if other.attribute_type(**attr).is_some() {
                    continue;
                }

                let mut a = true;

                for d in other.disjunction().iter() {
                    if d.get(*attr).is_some() {
                        a = false;
                        continue;
                    }
                    if !a {
                        continue;
                    }
                }
                if a {
                    new_heading.add_attribute(**attr, *self.attribute_type(**attr).unwrap())
                }
            }

            new_heading
        }
    }
    fn or(&self, other: &impl AlgebraHeading<A, T>) -> Self {
        if self.equal(other) {
            // If we can require that constructed headings are frozen, we can avoid this duplication.
            self.clone()
        } else {
            let mut disjunction = self.disjunction.clone();

            if other.is_negated() {
                unimplemented!("disjunction with negation");
            }

            disjunction.insert(other.attribute_types().clone());

            Self {
                attributes: self.attributes.clone(),
                is_negated: self.is_negated(),
                disjunction,
            }
        }
    }
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attrs = attrs.into();
        let mut attributes = self.attributes.clone();
        if !self.is_negated() {
            attributes.retain(|k, _v| attrs.contains(k));
        }

        let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
        for d in self.disjunction.iter() {
            let mut a = d.clone();
            a.retain(|k, _v| attrs.contains(k));
            disjunction.insert(a);
        }
        Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
        }
    }
    fn remove<I: Into<HashSet<A>>>(&self, attrs: I) -> Self {
        let attrs = attrs.into();
        let mut attributes = self.attributes.clone();
        if !self.is_negated() {
            attributes.retain(|k, _v| !attrs.contains(k));
        }

        let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
        for d in self.disjunction.iter() {
            let mut a = d.clone();
            a.retain(|k, _v| !attrs.contains(k));
            disjunction.insert(a);
        }
        Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
        }
    }
    fn rename<I: Into<HashMap<A, A>>>(&self, mapping: I) -> Self {
        let mapping = mapping.into();
        let mut attributes = BTreeMap::new();
        for (k, v) in self.attributes.iter() {
            let new_k = mapping.get(k).unwrap_or(k).clone();

            attributes.insert(new_k, v.clone());
        }
        let mut disjunction: BTreeSet<BTreeMap<A, T>> = Default::default();
        for d in self.disjunction.iter() {
            let mut a = BTreeMap::new();
            for (k, v) in d.iter() {
                let new_k = mapping.get(k).unwrap_or(k).clone();

                a.insert(new_k, v.clone());
            }
            disjunction.insert(a);
        }
        Self {
            attributes,
            is_negated: self.is_negated(),
            disjunction,
        }
    }
    fn compose(&self, other: &impl AlgebraHeading<A, T>) -> Self {
        let common = self.common_attributes(other);

        self.and(other).remove(common)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heading() {
        let heading0 = SimpleHeading::<Attr, Typ>::default();
        assert_eq!(0, heading0.arity());

        let mut heading1 = SimpleHeading::<Attr, Typ>::default();
        heading1.add_attribute(1, 100);

        let mut heading2 = SimpleHeading::<Attr, Typ>::default();
        heading2.add_attribute(2, 200);

        let mut heading3 = SimpleHeading::<Attr, Typ>::default();
        heading3.add_attribute(3, 300);

        let mut heading1_2 = SimpleHeading::<Attr, Typ>::default();
        heading1_2.add_attribute(1, 100);
        heading1_2.add_attribute(2, 200);

        let mut heading1x_3 = SimpleHeading::<Attr, Typ>::default();
        heading1x_3.add_attribute(1, 101);
        heading1x_3.add_attribute(3, 300);

        let mut heading1_2_3 = SimpleHeading::<Attr, Typ>::default();
        heading1_2_3.add_attribute(1, 100);
        heading1_2_3.add_attribute(2, 200);
        heading1_2_3.add_attribute(3, 300);

        let heading1and_1_2 = heading1.and(&heading1_2);
        let heading1x_3and1_2 = heading1x_3.and(&heading1_2);
        let heading1_2and_not1 = heading1_2.and(&heading1.not());
        let heading1_2or1_2 = heading1_2.or(&heading1_2);
        let heading1or2 = heading1.or(&heading2);
        let heading1_2_3and_not1_2 = heading1_2_3.and(&heading1or2.not());

        // unimplemented
        // let heading1or2and_3 = heading1or2.and(&heading3);
        // let heading3and_1or2 = heading3.and(&heading1or2);

        // arity
        assert_eq!(1, heading1.arity());
        assert_eq!(2, heading1_2.arity());
        assert_eq!(3, heading1_2_3.arity());

        // project
        assert!(heading1.project([]).equal(&heading0));
        assert!(heading1.project([1]).equal(&heading1));
        assert!(heading1_2_3.project([1, 2]).equal(&heading1_2));
        // TODO: Should this be an error?
        assert!(heading1_2_3.project([1, 2, 12345]).equal(&heading1_2));

        // remove
        assert!(heading1.remove([1]).equal(&heading0));
        assert!(heading1_2_3.remove([1, 2]).equal(&heading3));
        assert!(heading1_2_3.remove([1, 2, 12345]).equal(&heading3));

        // rename
        let h = heading1_2_3.rename([(1, 9), (2, 10)]);
        assert_eq!(3, h.arity());
        assert!(h.project([3]).equal(&heading3));
        assert!(h.attribute_type(1).is_none());
        assert!(h.attribute_type(2).is_none());
        assert_eq!(Some(100), h.attribute_type(9).cloned());
        assert_eq!(Some(200), h.attribute_type(10).cloned());

        // compose
        assert!(heading1.compose(&heading1_2).equal(&heading2));
        assert!(heading3.compose(&heading1_2_3).equal(&heading1_2));

        // attribute_type
        assert_eq!(Some(100), heading1.attribute_type(1).cloned());
        assert_eq!(Some(100), heading1_2.attribute_type(1).cloned());
        assert_eq!(Some(200), heading1_2.attribute_type(2).cloned());

        // common_attributes
        assert_eq!(1, heading1.common_attributes(&heading1_2).len());
        assert!(!heading1.equal(&heading1_2));
        assert_eq!(2, heading1_2_3.common_attributes(&heading1_2).len());

        // and
        assert!(!heading1.equal(&heading1and_1_2));
        assert!(heading1_2.equal(&heading1and_1_2));
        assert!(heading1_2.equal(&heading1and_1_2));
        assert!(heading1_2and_not1.equal(&heading2));
        assert!(heading1_2_3and_not1_2.equal(&heading3));
        // Type mismatch on common attribute yields empty conjunction.
        assert!(heading1x_3and1_2.equal(&heading0));

        // or
        assert!(heading1_2or1_2.equal(&heading1_2));
        assert!(!heading1_2or1_2.equal(&heading1));
        assert!(!heading1or2.equal(&heading1));
        assert!(!heading1or2.equal(&heading2));
        assert!(!heading1or2.equal(&heading1_2));
    }
}
