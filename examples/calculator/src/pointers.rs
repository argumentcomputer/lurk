use loam::pointers::IPtr;
use p3_field::AbstractField;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum Tag {
    Nil,
    Cons,
    Num,
    OpAdd,
}

impl Tag {
    pub(crate) fn field<F: AbstractField>(&self) -> F {
        match self {
            Tag::Nil => F::from_canonical_u8(0),
            Tag::Cons => F::from_canonical_u8(2),
            Tag::Num => F::from_canonical_u8(3),
            Tag::OpAdd => F::from_canonical_u8(4),
        }
    }
}

pub(crate) type Ptr = IPtr<Tag>;
