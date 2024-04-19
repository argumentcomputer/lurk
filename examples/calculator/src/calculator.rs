use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::AbstractField;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::{marker::PhantomData, mem::size_of};

use loam::pointers::GPtr;

use crate::{
    dummy_hasher::DummyHasher,
    pointers::{Ptr, Tag},
    store::Store,
};

#[derive(Clone, Default)]
#[repr(C)]
pub(crate) struct GFrame<Ptr, Bool, Slot> {
    entry: Ptr,
    stack: Ptr,

    o_entry: Ptr,
    pub(crate) o_stack: Ptr,

    slot0: Slot,
    slot1: Slot,
    slot2: Slot,
    slot3: Slot,

    entry_tag_is_nil: Bool,
    entry_tag_is_cons: Bool,

    entry_head: Ptr,
    entry_tail: Ptr,

    entry_head_tag_is_num: Bool,

    new_stack_push: Ptr,

    entry_head_tag_is_op_add: Bool,

    first_num: Ptr,
    stack_tail_1: Ptr,
    second_num: Ptr,
    stack_tail_2: Ptr,
    sum: Ptr,
    new_stack_op_add: Ptr,
}

type VarFrame<T> = GFrame<GPtr<T, T>, T, DummyHasher<T>>;

const NUM_COLS: usize = size_of::<VarFrame<u8>>();

impl<T> VarFrame<T> {
    /// Unsafely reads `&[T]` as `&VarFrame<T>` because:
    /// * `GFrame` has `repr(C)`
    /// * Every atomic piece of data in `VarFrame<T>` is precisely of type `T`
    #[inline]
    fn from_slice(slice: &[T]) -> &Self {
        assert_eq!(slice.len(), NUM_COLS);
        let (_, shorts, _) = unsafe { slice.align_to::<VarFrame<T>>() };
        &shorts[0]
    }
}

pub(crate) type WitnessFrame = GFrame<Ptr, bool, [Ptr; 2]>;

#[derive(Default)]
pub(crate) struct Calculator<F> {
    _p: PhantomData<F>,
}

impl<F: AbstractField + PartialEq + Eq + std::hash::Hash + Clone + Copy + Send + Sync>
    Calculator<F>
{
    /// Initiates a dummy `WitnessFrame` with a given input
    #[inline]
    fn init_frame(entry: Ptr, stack: Ptr, store: &Store<F>) -> WitnessFrame {
        let nil = store.nil();
        WitnessFrame {
            entry,
            stack,
            o_entry: nil,
            o_stack: nil,
            slot0: [nil, nil],
            slot1: [nil, nil],
            slot2: [nil, nil],
            slot3: [nil, nil],
            entry_tag_is_nil: false,
            entry_tag_is_cons: false,
            entry_head: nil,
            entry_tail: nil,
            entry_head_tag_is_num: false,
            new_stack_push: nil,
            entry_head_tag_is_op_add: false,
            first_num: nil,
            stack_tail_1: nil,
            second_num: nil,
            stack_tail_2: nil,
            sum: nil,
            new_stack_op_add: nil,
        }
    }

    fn compute_frame(entry: Ptr, stack: Ptr, store: &Store<F>) -> WitnessFrame {
        let mut frame = Self::init_frame(entry, stack, store);
        match entry.tag() {
            Tag::Nil => {
                frame.entry_tag_is_nil = true;

                // return
                frame.o_entry = entry;
                frame.o_stack = stack;
            }
            Tag::Cons => {
                frame.entry_tag_is_cons = true;
                let [entry_head, entry_tail] = store.decons(&frame.entry); // slot 0
                frame.entry_head = *entry_head;
                frame.entry_tail = *entry_tail;
                frame.slot0 = [frame.entry_head, frame.entry_tail];
                match entry_head.tag() {
                    Tag::Num => {
                        frame.entry_head_tag_is_num = true;

                        frame.new_stack_push = store.cons(frame.entry_head, frame.stack); // slot 1
                        frame.slot1 = [frame.entry_head, frame.stack];

                        // return
                        frame.o_entry = frame.entry_tail;
                        frame.o_stack = frame.new_stack_push;
                    }
                    Tag::OpAdd => {
                        frame.entry_head_tag_is_op_add = true;

                        let [first_num, stack_tail_1] = store.decons(&frame.stack); // slot 1
                        frame.first_num = *first_num;
                        frame.stack_tail_1 = *stack_tail_1;
                        frame.slot1 = [frame.first_num, frame.stack_tail_1];

                        let [second_num, stack_tail_2] = store.decons(&frame.stack_tail_1); // slot 2
                        frame.second_num = *second_num;
                        frame.stack_tail_2 = *stack_tail_2;
                        frame.slot2 = [frame.second_num, frame.stack_tail_2];

                        frame.sum = store.num(
                            *store.get_num(&frame.first_num) + *store.get_num(&frame.second_num),
                        );

                        frame.new_stack_op_add = store.cons(frame.sum, frame.stack_tail_2); // slot 3
                        frame.slot3 = [frame.sum, frame.stack_tail_2];

                        // return
                        frame.o_entry = frame.entry_tail;
                        frame.o_stack = frame.new_stack_op_add;
                    }
                    _ => panic!("Malformed entry"),
                }
            }
            _ => panic!("Malformed entry"),
        }
        frame
    }

    pub(crate) fn compute_frames(
        mut entry: Ptr,
        mut stack: Ptr,
        store: &Store<F>,
    ) -> Vec<WitnessFrame> {
        let mut frames = vec![];
        loop {
            let frame = Self::compute_frame(entry, stack, store);
            entry = frame.o_entry;
            stack = frame.o_stack;
            frames.push(frame);
            if entry.tag() == &Tag::Nil {
                break;
            }
        }
        frames
    }

    /// Computes a trace row from a `WitnessFrame` by following the same order
    /// that the data should appear in `VarFrame<F>`
    fn compute_row(frame: &WitnessFrame, store: &Store<F>) -> [F; NUM_COLS] {
        let extend_with_ptr = |ptr, row: &mut Vec<F>| {
            let (tag, val) = store.core.hash_ptr(ptr).into_parts();
            row.push(tag.field());
            row.push(val);
        };

        let extend_with_slot = |slot: &[Ptr; 2], row: &mut Vec<F>| {
            let (slot_0_tag, slot_0_val) = store.core.hash_ptr(&slot[0]).into_parts();
            let (slot_1_tag, slot_1_val) = store.core.hash_ptr(&slot[1]).into_parts();
            row.extend(DummyHasher::compute_row(
                slot_0_tag.field(),
                slot_0_val,
                slot_1_tag.field(),
                slot_1_val,
            ));
        };

        let extend_with_bool = |b: bool, row: &mut Vec<F>| row.push(F::from_bool(b));

        let mut row = Vec::with_capacity(NUM_COLS);

        extend_with_ptr(&frame.entry, &mut row);
        extend_with_ptr(&frame.stack, &mut row);
        extend_with_ptr(&frame.o_entry, &mut row);
        extend_with_ptr(&frame.o_stack, &mut row);

        extend_with_slot(&frame.slot0, &mut row);
        extend_with_slot(&frame.slot1, &mut row);
        extend_with_slot(&frame.slot2, &mut row);
        extend_with_slot(&frame.slot3, &mut row);

        extend_with_bool(frame.entry_tag_is_nil, &mut row);
        extend_with_bool(frame.entry_tag_is_cons, &mut row);

        extend_with_ptr(&frame.entry_head, &mut row);
        extend_with_ptr(&frame.entry_tail, &mut row);

        extend_with_bool(frame.entry_head_tag_is_num, &mut row);

        extend_with_ptr(&frame.new_stack_push, &mut row);

        extend_with_bool(frame.entry_head_tag_is_op_add, &mut row);

        extend_with_ptr(&frame.first_num, &mut row);
        extend_with_ptr(&frame.stack_tail_1, &mut row);
        extend_with_ptr(&frame.second_num, &mut row);
        extend_with_ptr(&frame.stack_tail_2, &mut row);
        extend_with_ptr(&frame.sum, &mut row);
        extend_with_ptr(&frame.new_stack_op_add, &mut row);

        row.try_into().expect("row length mismatch")
    }

    pub(crate) fn pad_frames(frames: &mut Vec<WitnessFrame>, store: &Store<F>) {
        let n_frames = frames.len();
        let target_n_frames = n_frames.next_power_of_two();
        if n_frames != target_n_frames {
            let last_frame = frames.last().expect("empty frames");
            let padding_frame = Self::compute_frame(last_frame.o_entry, last_frame.o_stack, store);
            assert_eq!(&padding_frame.stack, &padding_frame.o_stack);
            assert_eq!(&padding_frame.entry, &padding_frame.o_entry);
            frames.resize(target_n_frames, padding_frame);
        }
    }

    pub(crate) fn compute_trace(frames: &[WitnessFrame], store: &Store<F>) -> RowMajorMatrix<F> {
        let values = frames
            .par_iter()
            .flat_map(|frame| Self::compute_row(frame, store))
            .collect();
        RowMajorMatrix::new(values, NUM_COLS)
    }
}

impl<F: Send + Sync> BaseAir<F> for Calculator<F> {
    fn width(&self) -> usize {
        NUM_COLS
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for Calculator<AB::F> {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let local = VarFrame::<AB::Var>::from_slice(&local);

        let next = main.row_slice(1);
        let next = VarFrame::<AB::Var>::from_slice(&next);

        let public_values = builder.public_values();
        assert_eq!(public_values.len(), 8);
        let (
            entry_tag,
            entry_val,
            stack_tag,
            stack_val,
            o_entry_tag,
            o_entry_val,
            o_stack_tag,
            o_stack_val,
        ) = (
            public_values[0],
            public_values[1],
            public_values[2],
            public_values[3],
            public_values[4],
            public_values[5],
            public_values[6],
            public_values[7],
        );

        {
            // enforcing equality with public values
            builder
                .when_first_row()
                .assert_eq(local.stack.tag, stack_tag);
            builder
                .when_first_row()
                .assert_eq(local.stack.val, stack_val);
            builder
                .when_first_row()
                .assert_eq(local.entry.tag, entry_tag);
            builder
                .when_first_row()
                .assert_eq(local.entry.val, entry_val);
            builder
                .when_last_row()
                .assert_eq(local.o_stack.tag, o_stack_tag);
            builder
                .when_last_row()
                .assert_eq(local.o_stack.val, o_stack_val);
            builder
                .when_last_row()
                .assert_eq(local.o_entry.tag, o_entry_tag);
            builder
                .when_last_row()
                .assert_eq(local.o_entry.val, o_entry_val);
        }

        {
            // booleans
            builder.assert_bool(local.entry_tag_is_nil);
            builder.assert_bool(local.entry_tag_is_cons);
            builder.assert_bool(local.entry_head_tag_is_num);
            builder.assert_bool(local.entry_head_tag_is_op_add);
        }

        {
            // forcing a path
            builder.assert_one(local.entry_tag_is_nil + local.entry_tag_is_cons);

            builder
                .when(local.entry_tag_is_cons)
                .assert_one(local.entry_head_tag_is_num + local.entry_head_tag_is_op_add);
        }

        {
            // matched tags
            builder
                .when(local.entry_tag_is_nil)
                .assert_eq(local.entry.tag, Tag::Nil.field::<AB::F>());
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.entry.tag, Tag::Cons.field::<AB::F>());
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.entry_head.tag, Tag::Num.field::<AB::F>());
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.entry_head.tag, Tag::OpAdd.field::<AB::F>());
        }

        {
            // slot 0 io
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.slot0.pre0, local.entry_head.tag);
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.slot0.pre1, local.entry_head.val);
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.slot0.pre2, local.entry_tail.tag);
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.slot0.pre3, local.entry_tail.val);
            builder
                .when(local.entry_tag_is_cons)
                .assert_eq(local.slot0.img, local.entry.val);
        }

        {
            // slot 1 io
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.slot1.pre0, local.entry_head.tag);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.slot1.pre1, local.entry_head.val);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.slot1.pre2, local.stack.tag);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.slot1.pre3, local.stack.val);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.slot1.img, local.new_stack_push.val);

            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot1.pre0, local.first_num.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot1.pre1, local.first_num.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot1.pre2, local.stack_tail_1.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot1.pre3, local.stack_tail_1.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot1.img, local.stack.val);
        }

        {
            // slot 2 io
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot2.pre0, local.second_num.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot2.pre1, local.second_num.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot2.pre2, local.stack_tail_2.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot2.pre3, local.stack_tail_2.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot2.img, local.stack_tail_1.val);
        }

        {
            // slot 3 io
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot3.pre0, local.sum.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot3.pre1, local.sum.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot3.pre2, local.stack_tail_2.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot3.pre3, local.stack_tail_2.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.slot3.img, local.new_stack_op_add.val);
        }

        {
            // enforcing slots
            DummyHasher::eval(
                builder,
                local.entry_tag_is_cons,
                local.slot0.pre0,
                local.slot0.pre1,
                local.slot0.pre2,
                local.slot0.pre3,
                local.slot0.img,
            );
            DummyHasher::eval(
                builder,
                local.entry_tag_is_cons,
                local.slot1.pre0,
                local.slot1.pre1,
                local.slot1.pre2,
                local.slot1.pre3,
                local.slot1.img,
            );
            DummyHasher::eval(
                builder,
                local.entry_head_tag_is_op_add,
                local.slot2.pre0,
                local.slot2.pre1,
                local.slot2.pre2,
                local.slot2.pre3,
                local.slot2.img,
            );
            DummyHasher::eval(
                builder,
                local.entry_head_tag_is_op_add,
                local.slot3.pre0,
                local.slot3.pre1,
                local.slot3.pre2,
                local.slot3.pre3,
                local.slot3.img,
            );
        }

        {
            // new vars
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.new_stack_push.tag, Tag::Cons.field::<AB::F>());
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.sum.tag, Tag::Num.field::<AB::F>());
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.sum.val, local.first_num.val + local.second_num.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.new_stack_op_add.tag, Tag::Cons.field::<AB::F>());
        }

        {
            // returns
            builder
                .when(local.entry_tag_is_nil)
                .assert_eq(local.o_stack.tag, local.stack.tag);
            builder
                .when(local.entry_tag_is_nil)
                .assert_eq(local.o_stack.val, local.stack.val);
            builder
                .when(local.entry_tag_is_nil)
                .assert_eq(local.o_entry.tag, local.entry.tag);
            builder
                .when(local.entry_tag_is_nil)
                .assert_eq(local.o_entry.val, local.entry.val);

            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.o_stack.tag, local.new_stack_push.tag);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.o_stack.val, local.new_stack_push.val);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.o_entry.tag, local.entry_tail.tag);
            builder
                .when(local.entry_head_tag_is_num)
                .assert_eq(local.o_entry.val, local.entry_tail.val);

            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.o_stack.tag, local.new_stack_op_add.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.o_stack.val, local.new_stack_op_add.val);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.o_entry.tag, local.entry_tail.tag);
            builder
                .when(local.entry_head_tag_is_op_add)
                .assert_eq(local.o_entry.val, local.entry_tail.val);
        }

        {
            // io transitions
            builder
                .when_transition()
                .assert_eq(local.o_stack.tag, next.stack.tag);
            builder
                .when_transition()
                .assert_eq(local.o_stack.val, next.stack.val);
            builder
                .when_transition()
                .assert_eq(local.o_entry.tag, next.entry.tag);
            builder
                .when_transition()
                .assert_eq(local.o_entry.val, next.entry.val);
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use wp1_core::{
        stark::StarkGenericConfig,
        utils::{
            uni_stark_prove_with_public_values as prove,
            uni_stark_verify_with_public_values as verify, BabyBearPoseidon2,
        },
    };

    use super::*;

    #[test]
    fn it_works() {
        let store = Store::<BabyBear>::default();
        let entry = store.parse("1 3 8 + +");

        let expected_stack = store.parse("12"); // a cons list with a single element: the number 12
        let nil = store.nil();

        let mut frames = Calculator::compute_frames(entry, nil, &store);
        let last_frame = frames.last().unwrap();
        assert_eq!(&last_frame.o_stack, &expected_stack);
        assert_eq!(&last_frame.o_entry, &nil);

        Calculator::pad_frames(&mut frames, &store);
        let last_frame = frames.last().unwrap();
        assert_eq!(&last_frame.o_stack, &expected_stack);
        assert_eq!(&last_frame.o_entry, &nil);

        store.core.hydrate_z_cache();
        let trace = Calculator::compute_trace(&frames, &store);

        let public_values = store.to_scalar_vector(&[entry, nil, nil, expected_stack]);

        let config = BabyBearPoseidon2::new();

        let calculator = Calculator::default();

        let challenger = &mut config.challenger();
        let proof = prove(&config, &calculator, challenger, trace, &public_values);

        let challenger = &mut config.challenger();
        verify(&config, &calculator, challenger, &proof, &public_values).unwrap();
    }
}
