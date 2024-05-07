use std::fmt::Debug;
use std::hash::Hash;

use crate::loam::algebra::Algebra;
use crate::loam::heading::Heading;

mod algebra;
mod heading;
mod relation;
mod schema;
mod tuple;

pub trait Attribute: Copy + Default + Eq + PartialEq + Hash + Debug + Ord {}
pub trait Type: Copy + Eq + Hash + Debug + Ord {}
pub trait Value: Clone + Debug + PartialEq + Ord {}
pub trait AlgebraHeading<A: Attribute, T: Type, V: Value>:
    Algebra<A, T> + Heading<A, T, V>
{
}

pub type BubbaBear = u32;

pub type Attr = BubbaBear;
impl Attribute for Attr {}

pub type Typ = BubbaBear;
impl Type for Typ {}
