use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub mod loam;
pub mod store_core;

trait Attribute: Default + Eq + PartialEq + Hash {}
trait Type: Eq + Hash {}

impl Attribute for String {}
impl Type for String {}

pub trait Heading<A, T> {
    fn attributes(&self) -> HashSet<&A>;
    fn attribute_type(&self, attr: &A) -> Option<&T>;
    fn arity(&self) -> usize;
    fn add_attribute(&mut self, attr: A, typ: T);
    fn common_attributes<'a, 'b>(&'a self, other: &'b impl Heading<A, T>) -> HashSet<&A>
    where
        'b: 'a;
}

#[derive(Default)]
struct SimpleHeading<A, T>(HashMap<A, T>);

impl<A: Attribute, T: Type> Heading<A, T> for SimpleHeading<A, T> {
    // TODO: implement iterator
    fn attributes(&self) -> HashSet<&A> {
        // Make this OnceOnly, after heading is frozen.
        let mut set = HashSet::new();

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
    fn common_attributes<'a, 'b>(&'a self, other: &'b impl Heading<A, T>) -> HashSet<&A>
    where
        'b: 'a,
    {
        let mut common = HashSet::new();

        if self.arity() < other.arity() {
            for attr in self.attributes() {
                if other.attribute_type(attr).is_some() {
                    common.insert(attr);
                }
            }
            common
        } else {
            other.common_attributes(self)
        }
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
