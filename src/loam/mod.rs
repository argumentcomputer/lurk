use std::fmt::Debug;
use std::hash::Hash;

use crate::loam::algebra::Algebra;
use crate::loam::heading::Heading;

mod algebra;
mod heading;
mod schema;
mod tuple;

pub trait Attribute: Copy + Default + Eq + PartialEq + Hash + Debug + Ord {}
pub trait Type: Copy + Eq + Hash + Debug + Ord {}
pub trait Value: Clone + Debug + PartialEq {}
pub trait AlgebraHeading<A: Attribute, T: Type>: Algebra<A, T> + Heading<A, T> {}

pub type BubbaBear = u32;

pub type Attr = BubbaBear;
impl Attribute for Attr {}

pub type Typ = BubbaBear;
impl Type for Typ {}
