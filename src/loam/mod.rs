use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

pub trait Attribute: Copy + Default + Eq + PartialEq + Hash + Debug + Ord {}
pub trait Type: Copy + Eq + Hash + Debug + Ord {}

pub trait Heading<A: Attribute, T: Type>: Debug + Sized + Clone {
    fn new(is_negated: bool) -> Self;
    fn attributes(&self) -> BTreeSet<&A>;
    fn attribute_type(&self, attr: A) -> Option<&T>;
    fn attribute_types(&self) -> &BTreeMap<A, T>;
    fn arity(&self) -> usize;
    fn is_negated(&self) -> bool;
    fn add_attribute(&mut self, attr: A, typ: T);
    fn remove_attribute(&mut self, attr: &A);
    fn common_attributes<'a, 'b>(&'a self, other: &'b impl Heading<A, T>) -> HashSet<&A>
    where
        'b: 'a,
    {
        let mut common = HashSet::new();

        if self.arity() <= other.arity() {
            for attr in self.attributes() {
                if other.attribute_type(*attr).is_some() {
                    common.insert(attr);
                }
            }
            common
        } else {
            other.common_attributes(self)
        }
    }
    fn and(&self, other: &impl Heading<A, T>) -> Self {
        if !self.is_negated() && !other.is_negated() {
            if !self.disjunction().is_empty() || !other.disjunction().is_empty() {
                unimplemented!("conjunction of disjunctions");
            }
            let common = self.common_attributes(other);
            let mut new_heading = Self::new(self.is_negated());
            let compatible = common
                .iter()
                .all(|attr| self.attribute_type(**attr) == other.attribute_type(**attr));

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

                let mut xxx = true;

                for d in other.disjunction().iter() {
                    if d.get(*attr).is_some() {
                        xxx = false;
                        continue;
                    }
                    if !xxx {
                        continue;
                    }
                }
                if xxx {
                    new_heading.add_attribute(**attr, *self.attribute_type(**attr).unwrap())
                }
            }

            new_heading
        }
    }
    fn or(&self, other: &impl Heading<A, T>) -> Self;
    fn equal(&self, other: &impl Heading<A, T>) -> bool;
    fn not(&self) -> Self;
    fn disjunction(&self) -> &BTreeSet<BTreeMap<A, T>>;
    fn project<I: Into<HashSet<A>>>(&self, attrs: I) -> Self;
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
    fn remove_attribute(&mut self, attr: &A) {
        unimplemented!();
        self.attributes.remove(attr);
    }
    fn equal(&self, other: &impl Heading<A, T>) -> bool {
        if self.arity() != other.arity() {
            return false;
        };

        let common = self.common_attributes(other);

        if common.len() != self.arity() {
            return false;
        };

        common
            .iter()
            .all(|attr| self.attribute_type(**attr) == other.attribute_type(**attr))
            && &self.disjunction == other.disjunction()
    }
    fn not(&self) -> Self {
        Self {
            attributes: self.attributes.clone(),
            is_negated: !self.is_negated,
            disjunction: self.disjunction.clone(),
        }
    }
    fn or(&self, other: &impl Heading<A, T>) -> Self {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heading() {
        let mut heading0 = SimpleHeading::<Attr, Typ>::default();
        assert_eq!(0, heading0.arity());

        let mut heading1 = SimpleHeading::<Attr, Typ>::default();
        heading1.add_attribute(1, 100);

        assert!(heading1.project([]).equal(&heading0));
        assert!(heading1.project([1]).equal(&heading1));

        let mut heading2 = SimpleHeading::<Attr, Typ>::default();
        heading2.add_attribute(1, 100);
        heading2.add_attribute(2, 200);

        assert_eq!(1, heading1.arity());
        assert_eq!(Some(100), heading1.attribute_type(1).copied());

        assert_eq!(2, heading2.arity());
        assert_eq!(Some(100), heading2.attribute_type(1).copied());
        assert_eq!(Some(200), heading2.attribute_type(2).copied());

        assert_eq!(1, heading1.common_attributes(&heading2).len());
        assert!(!heading1.equal(&heading2));

        let heading3 = heading1.and(&heading2);
        dbg!(&heading1, &heading2, &heading3);

        assert!(!heading1.equal(&heading3));
        assert!(heading2.equal(&heading3));
        assert!(heading2.equal(&heading3));

        let heading4 = heading2.and(&heading1.not());

        let mut heading5 = SimpleHeading::<Attr, Typ>::default();
        heading5.add_attribute(2, 200);
        dbg!(&heading4, &heading5);

        let heading2or2 = heading2.or(&heading2);

        assert!(heading2or2.equal(&heading2));
        assert!(!heading2or2.equal(&heading1));

        let heading1or5 = heading1.or(&heading5);
        dbg!(&heading1or5);
        assert!(!heading1or5.equal(&heading1));
        assert!(!heading1or5.equal(&heading5));
        assert!(!heading1or5.equal(&heading2));

        let mut heading6 = SimpleHeading::<Attr, Typ>::default();
        heading6.add_attribute(1, 100);
        heading6.add_attribute(2, 200);
        heading6.add_attribute(3, 300);

        let mut heading7 = SimpleHeading::<Attr, Typ>::default();
        heading7.add_attribute(3, 300);

        let heading8 = heading6.and(&heading1or5.not());
        dbg!(&heading7, &heading8);
        assert!(heading8.equal(&heading7));

        // These panic via unimplemented!().
        //
        // let heading9 = heading1or5.and(&heading7);
        // let heading10 = heading7.and(&heading1or5);
        // dbg!(&heading9, &heading10);

        // // This is passing but both values are wrong.
        // assert!(heading9.equal(&heading10));

        // //assert!(heading9.equal(todo!()));
    }
}
