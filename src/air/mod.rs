

pub(crate)  mod builder;

pub(crate) mod symbolic;



struct Pointer<T, I> {
    trace: T,
    index: I,
}

impl<T, I> Pointer<T, I> {
    fn new(trace: T, index: I) -> Self {
        Self { trace, index }
    }
}

type TracePointer<F> = Pointer<F, F>;
