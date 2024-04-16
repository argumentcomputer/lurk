use core::mem::size_of;
use itertools::Itertools;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, MatrixRowSlices};
use std::borrow::{Borrow, BorrowMut};
use wp1_core::stark::SP1AirBuilder;
use wp1_derive::AlignedBorrow;

#[derive(AlignedBorrow, Default, Clone, Debug)]
#[repr(C)]
struct OpCols<T> {
    is_add: T,
    is_sub: T,
    is_mul: T,
    is_div: T,
}

/// The column layout for the chip.
#[derive(AlignedBorrow, Default, Clone, Debug)]
#[repr(C)]
struct CpuCols<T> {
    op: OpCols<T>,

    /// Unconstrained in the first row
    stack_top: T,
    /// Unconstrained in rows that perform operations and consume the stack
    stack_next: T,

    /// When performing a division, we need to provide the inverse
    /// of stack_next. Can be 0 whenever op.is_div = 0
    stack_next_inv: T,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Default)]
struct CpuChip<F> {
    _phantom: std::marker::PhantomData<F>,
}

const NUM_CPU_COLS: usize = size_of::<CpuCols<u8>>();

impl<F: Field> CpuChip<F> {
    /// Creates a trace matrix from a sequence of n operations and a stack with n+1 values.
    /// For example, providing the operations [+, -] and the values [1, 2, 3] will result on the
    /// trace for 3 + 2 - 1
    #[allow(dead_code)]
    fn generate_trace(ops: Vec<Operation>, mut stack: Vec<F>) -> RowMajorMatrix<F> {
        let trace_height = (ops.len() + 1).next_power_of_two();

        let trace = ops
            .into_iter()
            .map(Some)
            .pad_using(trace_height, |_| None)
            .flat_map(|op| {
                let mut row = [F::zero(); NUM_CPU_COLS];
                let cols: &mut CpuCols<F> = row.as_mut_slice().borrow_mut();

                match op {
                    None => {
                        assert_eq!(stack.len(), 1);
                        cols.stack_top = stack[0];
                    }
                    Some(op) => {
                        let stack_top = stack.pop().unwrap();
                        let stack_next = stack.pop().unwrap();

                        let result = match op {
                            Operation::Add => {
                                cols.op.is_add = F::one();
                                stack_top + stack_next
                            }
                            Operation::Sub => {
                                cols.op.is_sub = F::one();
                                stack_top - stack_next
                            }
                            Operation::Mul => {
                                cols.op.is_mul = F::one();
                                stack_top * stack_next
                            }
                            Operation::Div => {
                                cols.op.is_div = F::one();
                                let inv = stack_next.inverse();
                                cols.stack_next_inv = inv;

                                stack_top * inv
                            }
                        };
                        stack.push(result);
                        cols.stack_top = stack_top;
                        cols.stack_next = stack_next
                    }
                }
                row
            })
            .collect();

        RowMajorMatrix::new(trace, NUM_CPU_COLS)
    }
}

impl<F: Send + Sync> BaseAir<F> for CpuChip<F> {
    fn width(&self) -> usize {
        NUM_CPU_COLS
    }
}

impl<AB> Air<AB> for CpuChip<AB::F>
where
    AB: SP1AirBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &CpuCols<AB::Var> = main.row_slice(0).borrow();
        let next: &CpuCols<AB::Var> = main.row_slice(1).borrow();

        let op_is_some = local.op.is_add + local.op.is_sub + local.op.is_mul + local.op.is_div;

        // Constrain op flags
        {
            // Ensure all flags are boolean
            builder.assert_bool(local.op.is_add);
            builder.assert_bool(local.op.is_sub);
            builder.assert_bool(local.op.is_mul);
            builder.assert_bool(local.op.is_div);

            // Ensure only 1 or 0 flags are set
            builder.assert_bool(op_is_some.clone());
        }

        // op ADD
        {
            let result = local.stack_top + local.stack_next;

            // We need `when_transition` to skip the constraint in the last row, for which
            // `next` roundtrips and points to the first row.
            // Also, we should avoid degrees higher than 3 for efficiency purposes. The following
            // reaches degree 3 with two "when" followed by an "assert"
            builder
                .when(local.op.is_add)
                .when_transition()
                .assert_eq(result, next.stack_top);
        }

        // op SUB
        {
            let result = local.stack_top - local.stack_next;

            builder
                .when(local.op.is_sub)
                .when_transition()
                .assert_eq(result, next.stack_top);
        }

        // op MUL
        {
            let result = local.stack_top * local.stack_next;

            builder
                .when(local.op.is_mul)
                .when_transition()
                .assert_eq(result, next.stack_top);
        }

        // op DIV
        {
            // Check that stack_next has an inverse stack_next_inv
            builder
                .when(local.op.is_div)
                .assert_eq(local.stack_next * local.stack_next_inv, AB::F::one());

            let result = local.stack_top * local.stack_next_inv;

            builder
                .when(local.op.is_div)
                .when_transition()
                .assert_eq(result, next.stack_top);
        }

        // no op
        {
            // When there's no operation to be performed, the the stack can't change
            builder
                .when_not(op_is_some.clone())
                .when_transition()
                .assert_eq(local.stack_top, next.stack_top);

            builder
                .when_not(op_is_some)
                .when_transition()
                .assert_eq(local.stack_next, next.stack_next)
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractField, Field};
    use p3_matrix::dense::RowMajorMatrix;
    use wp1_core::{
        stark::StarkGenericConfig,
        utils::{uni_stark_prove as prove, uni_stark_verify as verify, BabyBearPoseidon2},
    };

    use super::*;

    #[test]
    fn prove_trace() {
        let config = BabyBearPoseidon2::new();
        let mut challenger = config.challenger();

        let f = BabyBear::from_canonical_u16;

        let ops = vec![
            Operation::Add,
            Operation::Sub,
            Operation::Mul,
            Operation::Div,
        ];
        let stack = vec![f(3), f(7), f(3), f(4), f(2)];

        let trace: RowMajorMatrix<BabyBear> = CpuChip::generate_trace(ops, stack);

        let trace_expected = {
            let inv = f(3).inverse();
            assert_eq!(f(21) * inv, f(7));
            let trace_expected = [
                //               stack_top─┐     ┌─stack_next
                // ┌─add ┌─sub ┌─mul ┌─div │     │     ┌─stack_next_inv
                [f(1), f(0), f(0), f(0), f(2), f(4), f(0)], // 2 + 4 => 6
                [f(0), f(1), f(0), f(0), f(6), f(3), f(0)], // 6 - 3 => 3
                [f(0), f(0), f(1), f(0), f(3), f(7), f(0)], // 3 * 7 => 21
                [f(0), f(0), f(0), f(1), f(21), f(3), inv], // 21 / 3 => 7
                [f(0), f(0), f(0), f(0), f(7), f(0), f(0)], // 7
                // fill rows until we reach the next power of two
                [f(0), f(0), f(0), f(0), f(7), f(0), f(0)], // 7
                [f(0), f(0), f(0), f(0), f(7), f(0), f(0)], // 7
                [f(0), f(0), f(0), f(0), f(7), f(0), f(0)], // 7
            ]
            .into_iter()
            .flatten()
            .collect();
            RowMajorMatrix::new(trace_expected, NUM_CPU_COLS)
        };
        assert_eq!(trace, trace_expected);

        let chip = CpuChip::default();
        let proof = prove::<BabyBearPoseidon2, _>(&config, &chip, &mut challenger, trace);

        let mut challenger = config.challenger();
        verify(&config, &chip, &mut challenger, &proof).unwrap();
    }
}
