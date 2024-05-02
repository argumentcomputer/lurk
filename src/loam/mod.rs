use std::fmt::Debug;
use std::hash::Hash;

use crate::loam::algebra::Algebra;
use crate::loam::heading::Heading;

mod algebra;
mod heading;
mod tuple;

pub trait Attribute: Copy + Default + Eq + PartialEq + Hash + Debug + Ord {}
pub trait Type: Copy + Eq + Hash + Debug + Ord {}
pub trait AlgebraHeading<A: Attribute, T: Type>: Algebra<A, T> + Heading<A, T> {}

pub type Attr = u32;
impl Attribute for Attr {}

pub type Typ = u32;
impl Type for Typ {}
