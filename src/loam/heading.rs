use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::Debug;

use super::{Algebra, Attribute, Type};

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
