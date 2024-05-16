pub struct Pointer<T, I> {
    trace: T,
    index: I,
}

impl<T, I> Pointer<T, I> {
    pub fn new(trace: T, index: I) -> Self {
        Self { trace, index }
    }
}

pub type TracePointer<F> = Pointer<F, F>;
