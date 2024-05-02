use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hash};

pub mod loam;
pub mod store_core;

pub trait Heading<A, T> {
    fn attributes(&self) -> HashSet<&A>;
    fn attribute_type(&self, attr: &A) -> Option<&T>;
    fn arity(&self) -> usize;
    fn add_attribute(&mut self, attr: A, typ: T);
}

#[derive(Default)]
struct SimpleHeading<A, T>(HashMap<A, T>);

impl<A: Default + Eq + PartialEq + Hash, T: Eq + Hash> Heading<A, T> for SimpleHeading<A, T> {
    fn attributes(&self) -> HashSet<&A> {
        // Make this OnceOnly, after heading is frozen.
        let mut set = HashSet::default();

        for key in self.0.keys() {
            set.insert(key);
        }
        set
    }
    fn attribute_type(&self, attr: &A) -> Option<&T> {
        self.0.get(attr)
    }
    fn arity(&self) -> usize {
        self.0.len()
    }
    fn add_attribute(&mut self, attr: A, typ: T) {
        self.0.insert(attr, typ);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut heading = SimpleHeading::<String, String>::default();

        heading.add_attribute("attr".into(), "type".into());

        assert_eq!(1, heading.arity());
        assert_eq!(
            Some("type"),
            heading.attribute_type(&"attr".into()).map(|x| x.as_str())
        );
    }
}
