use crate::air::builder::{LairBuilder, LookupBuilder, ProvideRecord, Relation, RequireRecord};
use hashbrown::{HashMap, HashSet};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues};
use p3_field::PrimeField32;
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use p3_matrix::Matrix;
use std::collections::BTreeMap;

type LocalRowView<'a, F> = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;

type Query<F> = Vec<F>;

#[derive(Copy, Clone, Default)]
struct Record {
    prev_nonce: u32,
    prev_count: u32,
    nonce: u32,
}

type MemoSetAccessRecords = BTreeMap<u32, Record>;

#[derive(Default)]
pub struct TraceQueries<F> {
    sends: HashSet<Query<F>>,
    receives: HashSet<Query<F>>,
    memoset: HashMap<Query<F>, MemoSetAccessRecords>,
}

impl<F: PrimeField32> TraceQueries<F> {
    fn receive(&mut self, query: Query<F>) {
        assert!(self.receives.insert(query), "query was already received");
    }

    fn send(&mut self, query: Query<F>) {
        assert!(self.sends.insert(query), "query was already sent");
    }

    fn memoset(&mut self, query: Query<F>, count: u32, record: Record) {
        let records = self.memoset.entry(query).or_default();
        assert!(
            records.insert(count, record).is_none(),
            "memoset record already accessed"
        );
    }

    pub fn merge(&mut self, other: Self) {
        let Self {
            sends,
            receives,
            memoset,
        } = other;

        for query in sends {
            self.send(query);
        }

        for query in receives {
            self.receive(query);
        }

        // Iterate over all memoset queries in other
        for (query, other_records) in memoset {
            let records = self.memoset.entry(query).or_default();
            for (count, record) in other_records {
                assert!(
                    records.insert(count, record).is_none(),
                    "memoset record already accessed"
                );
            }
        }
    }

    pub fn verify(&self) {
        assert_eq!(self.sends, self.receives);
        for (_query, records) in &self.memoset {
            let (mut prev_count, mut prev_record) = records
                .last_key_value()
                .expect("record should not be empty");

            for (i, (count, record)) in records.iter().enumerate() {
                assert_eq!(i, *count as usize, "count should be increasing");

                assert_eq!(record.prev_count, *prev_count);
                assert_eq!(record.prev_nonce, prev_record.nonce);

                (prev_count, prev_record) = (count, record);
            }
        }
    }

    pub fn verify_many(query_sets: impl IntoIterator<Item = Self>) {
        let mut merged = Self::default();
        for query_set in query_sets {
            merged.merge(query_set);
        }
        merged.verify()
    }
}

/// Check the `air` constraints over a given `main` trace.
pub fn debug_constraints_collecting_queries<
    F: PrimeField32,
    A: for<'a> Air<DebugConstraintBuilder<'a, F>>,
    M: Matrix<F>,
>(
    air: &A,
    public_values: &[F],
    main: &M,
) -> TraceQueries<F> {
    let height = main.height();

    let queries = (0..height).fold(TraceQueries::<F>::default(), |mut queries, row| {
        let row_next = (row + 1) % height;

        let main_local = &main.row_slice(row);
        let main_next = &main.row_slice(row_next);

        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(main_local),
            RowMajorMatrixView::new_row(main_next),
        );
        {
            let mut builder =
                DebugConstraintBuilder::new(public_values, main, row, height, &mut queries);

            air.eval(&mut builder);
        }
        queries
    });
    queries
}

/// A builder for debugging constraints.
pub struct DebugConstraintBuilder<'a, F> {
    public_values: &'a [F],
    main: LocalRowView<'a, F>,
    row: usize,
    height: usize,
    queries: &'a mut TraceQueries<F>,
}

impl<'a, F: PrimeField32> LookupBuilder for DebugConstraintBuilder<'a, F> {
    fn receive(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();
        if is_real.is_zero() {
            return;
        } else {
            assert!(is_real.is_one());
        }

        self.queries
            .receive(relation.values().into_iter().collect());
    }

    fn send(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>) {
        let is_real = is_real_bool.into();
        if is_real.is_zero() {
            return;
        } else {
            assert!(is_real.is_one());
        }

        self.queries.send(relation.values().into_iter().collect());
    }

    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: impl Into<Self::Expr>,
        record: ProvideRecord<impl Into<Self::Expr>>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();
        if is_real.is_zero() {
            return;
        } else {
            assert!(is_real.is_one());
        }
        let query = relation.values().into_iter().collect();
        let count = 0;
        let ProvideRecord {
            last_nonce,
            last_count,
        } = record;
        self.queries.memoset(
            query,
            count,
            Record {
                prev_nonce: last_nonce.into().as_canonical_u32(),
                prev_count: last_count.into().as_canonical_u32(),
                nonce: nonce.into().as_canonical_u32(),
            },
        )
    }

    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: impl Into<Self::Expr>,
        record: RequireRecord<impl Into<Self::Expr>>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();
        if is_real.is_zero() {
            return;
        } else {
            assert!(is_real.is_one());
        }
        let prev_nonce = record.prev_nonce.into();
        let prev_count = record.prev_count.into();
        let count = prev_count + F::one();
        assert_eq!(count * record.count_inv.into(), F::one());

        let query = relation.values().into_iter().collect();
        let count = count.as_canonical_u32();
        self.queries.memoset(
            query,
            count,
            Record {
                prev_nonce: prev_nonce.as_canonical_u32(),
                prev_count: prev_count.as_canonical_u32(),
                nonce: nonce.into().as_canonical_u32(),
            },
        )
    }
}

impl<'a, F: PrimeField32> AirBuilderWithPublicValues for DebugConstraintBuilder<'a, F> {
    type PublicVar = F;

    fn public_values(&self) -> &'a [Self::PublicVar] {
        self.public_values
    }
}

impl<'a, F: PrimeField32> LairBuilder for DebugConstraintBuilder<'a, F> {}

impl<'a, F: PrimeField32> DebugConstraintBuilder<'a, F> {
    #[inline]
    fn new(
        public_values: &'a [F],
        main: LocalRowView<'a, F>,
        row: usize,
        height: usize,
        queries: &'a mut TraceQueries<F>,
    ) -> Self {
        Self {
            public_values,
            main,
            row,
            height,
            queries,
        }
    }

    #[inline]
    fn debug_constraint(&self, x: F, y: F) {
        if x != y {
            let backtrace = std::backtrace::Backtrace::force_capture();
            eprintln!(
                "constraint failed at row {}: {:?} != {:?}\n{}",
                self.row, x, y, backtrace
            );
            panic!();
        }
    }
}

impl<'a, F: PrimeField32> AirBuilder for DebugConstraintBuilder<'a, F> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = LocalRowView<'a, F>;

    fn main(&self) -> Self::M {
        self.main
    }

    fn is_first_row(&self) -> Self::Expr {
        F::from_bool(self.row == 0)
    }

    fn is_last_row(&self) -> Self::Expr {
        F::from_bool(self.row == self.height - 1)
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            F::from_bool(self.row != self.height - 1)
        } else {
            panic!("only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.debug_constraint(x.into(), F::zero());
    }

    fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) {
        self.debug_constraint(x.into(), F::one());
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        self.debug_constraint(x.into(), y.into());
    }

    /// Assert that `x` is a boolean, i.e. either 0 or 1.
    fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) {
        let x = x.into();
        if x != F::zero() && x != F::one() {
            let backtrace = std::backtrace::Backtrace::force_capture();
            eprintln!(
                "constraint failed at row {}: {:?} is not a bool\n{}",
                self.row, x, backtrace
            );
            panic!();
        }
    }
}
