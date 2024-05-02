use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::mem::size_of;

use loam::store_core::pointers::GPtr;

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

type VarFrame<T> = GFrame<GPtr<T, T>, T, ([T; 4], T)>;

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

    #[inline]
    fn into_array(self) -> [T; NUM_COLS]
    where
        T: Copy + Default + AbstractField,
    {
        let Self {
            entry,
            stack,
            o_entry,
            o_stack,
            slot0,
            slot1,
            slot2,
            slot3,
            entry_tag_is_nil,
            entry_tag_is_cons,
            entry_head,
            entry_tail,
            entry_head_tag_is_num,
            new_stack_push,
            entry_head_tag_is_op_add,
            first_num,
            stack_tail_1,
            second_num,
            stack_tail_2,
            sum,
            new_stack_op_add,
        } = self;
        let mut array = [T::default(); NUM_COLS];
        let mut idx = 0;
        let populate_with_atom = |a, array: &mut [T; NUM_COLS], idx: &mut usize| {
            array[*idx] = a;
            *idx += 1;
        };
        let populate_with_ptr = |ptr: GPtr<T, T>, array: &mut [T; NUM_COLS], idx: &mut usize| {
            let (tag, val) = ptr.into_parts();
            populate_with_atom(tag, array, idx);
            populate_with_atom(val, array, idx);
        };
        let populate_with_slot = |slot, array: &mut [T; NUM_COLS], idx: &mut usize| {
            let (preimg, img) = slot;
            for x in preimg {
                populate_with_atom(x, array, idx);
            }
            populate_with_atom(img, array, idx);
        };
        populate_with_ptr(entry, &mut array, &mut idx);
        populate_with_ptr(stack, &mut array, &mut idx);
        populate_with_ptr(o_entry, &mut array, &mut idx);
        populate_with_ptr(o_stack, &mut array, &mut idx);
        populate_with_slot(slot0, &mut array, &mut idx);
        populate_with_slot(slot1, &mut array, &mut idx);
        populate_with_slot(slot2, &mut array, &mut idx);
        populate_with_slot(slot3, &mut array, &mut idx);
        populate_with_atom(entry_tag_is_nil, &mut array, &mut idx);
        populate_with_atom(entry_tag_is_cons, &mut array, &mut idx);
        populate_with_ptr(entry_head, &mut array, &mut idx);
        populate_with_ptr(entry_tail, &mut array, &mut idx);
        populate_with_atom(entry_head_tag_is_num, &mut array, &mut idx);
        populate_with_ptr(new_stack_push, &mut array, &mut idx);
        populate_with_atom(entry_head_tag_is_op_add, &mut array, &mut idx);
        populate_with_ptr(first_num, &mut array, &mut idx);
        populate_with_ptr(stack_tail_1, &mut array, &mut idx);
        populate_with_ptr(second_num, &mut array, &mut idx);
        populate_with_ptr(stack_tail_2, &mut array, &mut idx);
        populate_with_ptr(sum, &mut array, &mut idx);
        populate_with_ptr(new_stack_op_add, &mut array, &mut idx);
        array
    }
}

type WitnessFrame = GFrame<Ptr, bool, [Ptr; 2]>;

#[derive(Default)]
pub(crate) struct Calculator<F> {
    _f: F,
}

struct IterationContext<'a, F: Field> {
    entry: Ptr,
    stack: Ptr,
    store: &'a Store<F>,
}

impl<'a, F: Field> Iterator for IterationContext<'a, F> {
    type Item = WitnessFrame;

    fn next(&mut self) -> Option<Self::Item> {
        if self.entry.tag() == &Tag::Nil {
            None
        } else {
            let frame = Calculator::compute_frame(self.entry, self.stack, self.store);
            self.entry = frame.o_entry;
            self.stack = frame.o_stack;
            Some(frame)
        }
    }
}

impl<F: Field> Calculator<F> {
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

    #[inline]
    pub(crate) fn compute_frames(entry: Ptr, stack: Ptr, store: &Store<F>) -> Vec<WitnessFrame> {
        IterationContext {
            entry,
            stack,
            store,
        }
        .collect()
    }

    fn materialize_var_frame(frame: &WitnessFrame, store: &Store<F>) -> VarFrame<F> {
        let hash_ptr = |ptr| {
            let (tag, val) = store.core.hash_ptr(ptr).into_parts();
            GPtr::new(tag.field(), val)
        };
        let hash_slot_ptrs = |slot: &[Ptr; 2]| {
            let (a_tag, a_val) = store.core.hash_ptr(&slot[0]).into_parts();
            let (b_tag, b_val) = store.core.hash_ptr(&slot[1]).into_parts();
            let preimg = [a_tag.field(), a_val, b_tag.field(), b_val];
            (preimg, DummyHasher::hash(preimg))
        };
        VarFrame {
            entry: hash_ptr(&frame.entry),
            stack: hash_ptr(&frame.stack),
            o_entry: hash_ptr(&frame.o_entry),
            o_stack: hash_ptr(&frame.o_stack),
            slot0: hash_slot_ptrs(&frame.slot0),
            slot1: hash_slot_ptrs(&frame.slot1),
            slot2: hash_slot_ptrs(&frame.slot2),
            slot3: hash_slot_ptrs(&frame.slot3),
            entry_tag_is_nil: F::from_bool(frame.entry_tag_is_nil),
            entry_tag_is_cons: F::from_bool(frame.entry_tag_is_cons),
            entry_head: hash_ptr(&frame.entry_head),
            entry_tail: hash_ptr(&frame.entry_tail),
            entry_head_tag_is_num: F::from_bool(frame.entry_head_tag_is_num),
            new_stack_push: hash_ptr(&frame.new_stack_push),
            entry_head_tag_is_op_add: F::from_bool(frame.entry_head_tag_is_op_add),
            first_num: hash_ptr(&frame.first_num),
            stack_tail_1: hash_ptr(&frame.stack_tail_1),
            second_num: hash_ptr(&frame.second_num),
            stack_tail_2: hash_ptr(&frame.stack_tail_2),
            sum: hash_ptr(&frame.sum),
            new_stack_op_add: hash_ptr(&frame.new_stack_op_add),
        }
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
            .flat_map(|frame| Self::materialize_var_frame(frame, store).into_array())
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
            // eval slots
            let mut eval_slot = |slot, is_real| {
                let (preimg, img) = slot;
                DummyHasher::eval(builder, preimg, img, is_real);
            };

            eval_slot(local.slot0, local.entry_tag_is_cons);
            eval_slot(local.slot1, local.entry_tag_is_cons);
            eval_slot(local.slot2, local.entry_head_tag_is_op_add);
            eval_slot(local.slot3, local.entry_head_tag_is_op_add);
        }

        {
            // enforce slots io
            let mut enforce_slot_io = |slot: ([_; 4], _), preimg: [GPtr<_, _>; 2], img, is_real| {
                let (slot_preimg, slot_img) = slot;
                let [a, b] = preimg;
                let builder = &mut builder.when(is_real);
                builder.assert_eq(slot_preimg[0], a.tag);
                builder.assert_eq(slot_preimg[1], a.val);
                builder.assert_eq(slot_preimg[2], b.tag);
                builder.assert_eq(slot_preimg[3], b.val);
                builder.assert_eq(slot_img, img);
            };

            enforce_slot_io(
                local.slot0,
                [local.entry_head, local.entry_tail],
                local.entry.val,
                local.entry_tag_is_cons,
            );

            enforce_slot_io(
                local.slot1,
                [local.entry_head, local.stack],
                local.new_stack_push.val,
                local.entry_head_tag_is_num,
            );
            enforce_slot_io(
                local.slot1,
                [local.first_num, local.stack_tail_1],
                local.stack.val,
                local.entry_head_tag_is_op_add,
            );

            enforce_slot_io(
                local.slot2,
                [local.second_num, local.stack_tail_2],
                local.stack_tail_1.val,
                local.entry_head_tag_is_op_add,
            );

            enforce_slot_io(
                local.slot3,
                [local.sum, local.stack_tail_2],
                local.new_stack_op_add.val,
                local.entry_head_tag_is_op_add,
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

            let mut builder_entry_tag_is_nil = builder.when(local.entry_tag_is_nil);
            builder_entry_tag_is_nil.assert_eq(local.o_stack.tag, local.stack.tag);
            builder_entry_tag_is_nil.assert_eq(local.o_stack.val, local.stack.val);
            builder_entry_tag_is_nil.assert_eq(local.o_entry.tag, local.entry.tag);
            builder_entry_tag_is_nil.assert_eq(local.o_entry.val, local.entry.val);

            let mut builder_entry_head_tag_is_num = builder.when(local.entry_head_tag_is_num);
            builder_entry_head_tag_is_num.assert_eq(local.o_stack.tag, local.new_stack_push.tag);
            builder_entry_head_tag_is_num.assert_eq(local.o_stack.val, local.new_stack_push.val);
            builder_entry_head_tag_is_num.assert_eq(local.o_entry.tag, local.entry_tail.tag);
            builder_entry_head_tag_is_num.assert_eq(local.o_entry.val, local.entry_tail.val);

            let mut builder_entry_head_tag_is_op_add = builder.when(local.entry_head_tag_is_op_add);
            builder_entry_head_tag_is_op_add
                .assert_eq(local.o_stack.tag, local.new_stack_op_add.tag);
            builder_entry_head_tag_is_op_add
                .assert_eq(local.o_stack.val, local.new_stack_op_add.val);
            builder_entry_head_tag_is_op_add.assert_eq(local.o_entry.tag, local.entry_tail.tag);
            builder_entry_head_tag_is_op_add.assert_eq(local.o_entry.val, local.entry_tail.val);
        }

        {
            // io transitions
            let mut builder_when_transition = builder.when_transition();
            builder_when_transition.assert_eq(local.o_stack.tag, next.stack.tag);
            builder_when_transition.assert_eq(local.o_stack.val, next.stack.val);
            builder_when_transition.assert_eq(local.o_entry.tag, next.entry.tag);
            builder_when_transition.assert_eq(local.o_entry.val, next.entry.val);
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
