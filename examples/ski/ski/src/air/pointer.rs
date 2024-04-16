use wp1_derive::AlignedBorrow;

#[derive(AlignedBorrow, Default, Debug, Clone, Copy)]
pub struct Pointer<T> {
    pub idx: T,
    pub tag: T,
}

impl<T> Pointer<T> {
    pub fn into_exprs<U>(self) -> impl IntoIterator<Item = U>
    where
        T: Into<U>,
    {
        [self.tag.into(), self.idx.into()]
    }
}
