mod debug_builder;
mod symbolic_builder;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field};
use p3_matrix::{
    dense::{RowMajorMatrix, RowMajorMatrixView},
    Matrix,
};
use rayon::iter::{IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use std::{
    sync::mpsc::{channel, Sender},
};
use std::collections::BTreeMap;
use crate::debug_builder::{debug_constraints, LookupSet};

struct Lookup<T> {
    data: Vec<T>,
    multiplicity: T,
}

impl<T> Lookup<T> {
    #[inline]
    fn new<D: Into<T>, I: IntoIterator<Item = D>, M: Into<T>>(data: I, multiplicity: M) -> Self {
        Self {
            data: data.into_iter().map(Into::into).collect(),
            multiplicity: multiplicity.into(),
        }
    }
}

pub trait LookupAirBuilder<T> {
    fn require<V: Into<T>, R: Into<T>>(
        &mut self,
        values: impl IntoIterator<Item = V>,
        is_real: R,
    );
    fn provide<V: Into<T>,  M: Into<T>>(
        &mut self,
        values: impl IntoIterator<Item = V>,
        multiplicity: M,
    );
}

/// Columns:
/// * byte[1]
/// * is_byte[1]
struct MainChip;

impl<F: Send + Sync> BaseAir<F> for MainChip {
    fn width(&self) -> usize {
        2
    }
}

impl<AB: AirBuilder + LookupAirBuilder<AB::Expr>> Air<AB> for MainChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);

        let (byte, is_byte) = (local[0], local[1]);

        builder.assert_bool(is_byte);

        builder.require([byte], is_byte);
    }
}

/// Columns:
/// * byte[1]
/// * bits[8]
/// * multiplicity[1]
struct BytesChip;

impl<F: Send + Sync> BaseAir<F> for BytesChip {
    fn width(&self) -> usize {
        10
    }
}

impl<AB: AirBuilder + LookupAirBuilder<AB::Expr>> Air<AB> for BytesChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let byte = local[0];
        let bits = &local[1..9];
        let multiplicity = local[9];

        for bit in bits {
            builder.assert_bool(*bit);
        }

        let bases = [1, 2, 4, 8, 16, 32, 64, 128].map(AB::Expr::from_canonical_u16);

        let mut byte_expected = AB::Expr::zero();
        for (bit, base) in bits.iter().zip(bases) {
            byte_expected += *bit * base;
        }

        builder.assert_eq(byte_expected, byte);

        builder.provide([byte], multiplicity);
    }
}

enum LookupKind {
    Required,
    Provided,
}

type Message<F> = (LookupKind, Lookup<F>);

struct LookupBuilder<'a, F> {
    view: RowMajorMatrixView<'a, F>,
    is_first_row: F,
    is_transition: F,
    is_last_row: F,
    sender: Sender<Message<F>>,
}

impl<'a, F: Field> LookupBuilder<'a, F> {
    fn mk_views(
        matrix: &'a RowMajorMatrix<F>,
        roundtrip: &'a [F],
        sender: &Sender<Message<F>>,
    ) -> Vec<Self> {
        let width = matrix.width;
        let height = matrix.height();
        (0..height)
            .into_par_iter()
            .map(|r| {
                let is_last_row = F::from_bool(r == height - 1);
                let row_values = if is_last_row.is_one() {
                    roundtrip
                } else {
                    &matrix.values[(r * width)..((r + 1) * width)]
                };
                Self {
                    view: RowMajorMatrixView::new(row_values, width),
                    is_first_row: F::from_bool(r == 0),
                    is_transition: F::one() - is_last_row,
                    is_last_row,
                    sender: sender.clone(),
                }
            })
            .collect()
    }
}

impl<'a, F> LookupAirBuilder<F> for LookupBuilder<'a, F> {
    fn require<V: Into<F>, R: Into<F>>(&mut self, values: impl IntoIterator<Item=V>, is_real: R) {
        let data = values.into_iter().map(|v| v.into()).collect();
        let lookup = Lookup{ data, multiplicity: is_real.into() };
        self.sender
            .send((LookupKind::Required, lookup))
            .expect("send error");
    }

    fn provide<V: Into<F>, M: Into<F>>(&mut self, values: impl IntoIterator<Item=V>, multiplicity: M) {
        let data = values.into_iter().map(|v| v.into()).collect();
        let lookup = Lookup{ data, multiplicity: multiplicity.into() };
        self.sender
            .send((LookupKind::Provided, lookup))
            .expect("send error");
    }

}

impl<'a, F: Field> AirBuilder for LookupBuilder<'a, F> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = RowMajorMatrixView<'a, F>;
    fn main(&self) -> Self::M {
        self.view
    }
    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }
    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            self.is_transition
        } else {
            panic!("only supports a window size of 2")
        }
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        assert_eq!(x.into(), F::zero(), "constraints must evaluate to zero");
    }
}

fn extract_roundtrip<F: Clone + Sync + Send>(matrix: &RowMajorMatrix<F>) -> Vec<F> {
    let mut roundtrip = Vec::with_capacity(2 * matrix.width);
    roundtrip.extend_from_slice(&matrix.row_slice(matrix.height() - 1));
    roundtrip.extend_from_slice(&matrix.row_slice(0));
    roundtrip
}

fn send_lookups<'a, F: Field, A: Air<LookupBuilder<'a, F>>>(
    matrix: &'a RowMajorMatrix<F>,
    roundtrip: &'a [F],
    sender: &Sender<Message<F>>,
    chip: &A,
) {
    LookupBuilder::mk_views(matrix, roundtrip, sender)
        .par_iter_mut()
        .for_each(|builder| chip.eval(builder));
}

fn main() {
    let f = BabyBear::from_canonical_u16;
    let main_vals = [
        [f(0), f(1)],
        [f(0), f(0)],
        [f(4), f(1)],
        [f(4), f(1)],
        [f(3), f(0)],
        [f(5), f(1)],
        [f(255), f(1)],
        [f(256), f(0)],
    ];
    let main_trace = RowMajorMatrix::new(main_vals.into_iter().flatten().collect(), 2);

    let bytes_vals = [
        [f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(4), f(0), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(2)],
        [f(5), f(1), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(255), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1)],
    ];
    let bytes_trace = RowMajorMatrix::new(bytes_vals.into_iter().flatten().collect(), 10);

    let mut lookups = LookupSet::default();
    debug_constraints(MainChip{}, &main_trace, &mut  lookups);
    debug_constraints(BytesChip{}, &bytes_trace, &mut  lookups);

    for m in lookups.values() {
        assert!(m.is_zero())
    }

    let (sender, receiver) = channel();

    let main_roundtrip = extract_roundtrip(&main_trace);
    send_lookups(&main_trace, &main_roundtrip, &sender, &MainChip);

    let bytes_roundtrip = extract_roundtrip(&bytes_trace);
    send_lookups(&bytes_trace, &bytes_roundtrip, &sender, &BytesChip);

    let mut required = BTreeMap::default();
    let mut provided = BTreeMap::default();

    for (kind, Lookup { data, multiplicity }) in receiver.try_iter() {
        let collected = match kind {
            LookupKind::Required => &mut required,
            LookupKind::Provided => &mut provided,
        };
        if multiplicity.is_zero() {
            continue;
        }
        if let Some(mult) = collected.get_mut(&data) {
            *mult += multiplicity;
        } else {
            collected.insert(data, multiplicity);
        }
    }

    println!("Required: {:?}", required);
    println!("Provided: {:?}", provided);
    assert_eq!(required, provided);
}
