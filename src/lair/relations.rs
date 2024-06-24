use itertools::chain;
use p3_field::AbstractField;

use crate::air::builder::Relation;

const MEMORY_TAG: u32 = 0;

pub struct MemoryRelation<Ptr, ValuesIter>(pub Ptr, pub ValuesIter);

impl<T, Ptr, IntoValuesIter, Value> Relation<T> for MemoryRelation<Ptr, IntoValuesIter>
where
    T: AbstractField,
    Ptr: Into<T>,
    IntoValuesIter: IntoIterator<Item = Value>,
    Value: Into<T>,
{
    fn values(self) -> impl IntoIterator<Item = T> {
        let Self(ptr, values_iter) = self;
        chain(
            [T::from_canonical_u32(MEMORY_TAG), ptr.into()],
            values_iter.into_iter().map(Into::into),
        )
    }
}
