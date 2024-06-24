use itertools::chain;
use p3_field::AbstractField;

use crate::air::builder::Relation;

const CALL_TAG: u32 = 0;
const MEMORY_TAG: u32 = 1;

pub struct CallRelation<Idx, Inp, Out>(pub Idx, pub Inp, pub Out);
pub struct MemoryRelation<Ptr, ValuesIter>(pub Ptr, pub ValuesIter);

impl<F: AbstractField, FuncIdx: Into<F>, IntoInputIter, IntoOutputIter, Value: Into<F>> Relation<F>
    for CallRelation<FuncIdx, IntoInputIter, IntoOutputIter>
where
    IntoInputIter: IntoIterator<Item = Value>,
    IntoOutputIter: IntoIterator<Item = Value>,
{
    fn values(self) -> impl IntoIterator<Item = F> {
        let Self(func_idx, input, output) = self;
        chain(
            [F::from_canonical_u32(CALL_TAG), func_idx.into()],
            chain(
                input.into_iter().map(Into::into),
                output.into_iter().map(Into::into),
            ),
        )
    }
}

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
