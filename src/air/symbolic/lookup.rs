#[derive(Clone)]
pub(crate) enum InteractionKind<T> {
    Require(T),
    Provide,
}

#[derive(Clone)]
pub(crate) struct Interaction<T> {
    values: Vec<T>,
    kind: InteractionKind<T>,
}

impl<T> Interaction<T> {
    pub(crate) fn required(values: Vec<T>, is_real: T) -> Self {
        Self {
            values,
            kind: InteractionKind::Require(is_real),
        }
    }

    pub(crate) fn provided(
        values: Vec<T>,
    ) -> Self {
        Self {
            values,
            kind: InteractionKind::Provide,
        }
    }
}
