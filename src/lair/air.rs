use p3_air::{Air, AirBuilder};
use p3_field::Field;
use p3_matrix::Matrix;
use std::fmt::Debug;

use crate::air::builder::{LookupBuilder, ProvideRecord, RequireRecord};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    func_chip::{ColumnLayout, FuncChip, LayoutSizes},
    hasher::Hasher,
    relations::{CallRelation, MemoryRelation},
    toplevel::Toplevel,
    trace::ColumnIndex,
};

impl ColumnIndex {
    #[inline]
    fn save(&mut self) -> usize {
        self.aux
    }

    #[inline]
    fn restore(&mut self, aux: usize) {
        self.aux = aux;
    }
}

#[derive(Clone)]
struct CallCtx<F, T> {
    func_idx: F,
    call_inp: Vec<T>,
}

pub type ColumnSlice<'a, T> = ColumnLayout<&'a T, &'a [T]>;

impl<'a, T> ColumnSlice<'a, T> {
    pub fn from_slice(slice: &'a [T], layout_sizes: LayoutSizes) -> Self {
        let (nonce, slice) = slice.split_at(1);
        let (input, slice) = slice.split_at(layout_sizes.input);
        let (aux, slice) = slice.split_at(layout_sizes.aux);
        let (sel, slice) = slice.split_at(layout_sizes.sel);
        assert!(slice.is_empty());
        let nonce = &nonce[0];
        Self {
            nonce,
            input,
            aux,
            sel,
        }
    }

    pub fn next_input(&self, index: &mut ColumnIndex) -> T
    where
        T: Copy,
    {
        let t = self.input[index.input];
        index.input += 1;
        t
    }

    pub fn next_aux(&self, index: &mut ColumnIndex) -> T
    where
        T: Copy,
    {
        let t = self.aux[index.aux];
        index.aux += 1;
        t
    }

    pub fn next_n_aux(&self, index: &mut ColumnIndex, n: usize) -> &[T] {
        let slice = &self.aux[index.aux..index.aux + n];
        index.aux += n;
        slice
    }
}

impl<'a, AB, H: Hasher<AB::F>> Air<AB> for FuncChip<'a, AB::F, H>
where
    AB: AirBuilder + LookupBuilder,
    <AB as AirBuilder>::Var: Debug,
{
    fn eval(&self, builder: &mut AB) {
        self.func.eval(builder, self.toplevel, self.layout_sizes)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Val<AB: AirBuilder> {
    Const(AB::F),
    Expr(AB::Expr),
}

impl<AB: AirBuilder> Val<AB> {
    fn to_expr(&self) -> AB::Expr {
        match self {
            Val::Const(f) => (*f).into(),
            Val::Expr(e) => e.clone(),
        }
    }
}

impl<F: Field> Func<F> {
    fn eval<AB, H: Hasher<F>>(
        &self,
        builder: &mut AB,
        toplevel: &Toplevel<F, H>,
        layout_sizes: LayoutSizes,
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        let main = builder.main();
        let local_slice = main.row_slice(0);
        let next_slice = main.row_slice(1);
        let local = ColumnSlice::from_slice(&local_slice, layout_sizes);
        let next = ColumnSlice::from_slice(&next_slice, layout_sizes);
        let index = &mut ColumnIndex::default();

        let nonce = *local.nonce;
        let next_nonce = *next.nonce;

        // nonce counting starts from zero
        builder.when_first_row().assert_zero(nonce);

        // nonces are unique, even for dummy rows
        builder
            .when_transition()
            .assert_eq(next_nonce, nonce + F::one());

        let map = &mut vec![];
        let mut call_inp = Vec::with_capacity(self.input_size);
        for _ in 0..self.input_size {
            let i = local.next_input(index);
            map.push(Val::Expr(i.into()));
            call_inp.push(i.into());
        }

        let func_idx = F::from_canonical_usize(
            toplevel
                .map
                .get_index_of(&self.name)
                .expect("Func not found on toplevel"),
        );
        let call_ctx = CallCtx { func_idx, call_inp };

        let toplevel_sel = self.body.return_sel::<AB>(local);
        self.body.eval(
            builder,
            local,
            &toplevel_sel,
            index,
            map,
            toplevel,
            call_ctx,
        );
        builder.assert_bool(toplevel_sel.clone());
    }
}

impl<F: Field> Block<F> {
    fn return_sel<AB>(&self, local: ColumnSlice<'_, AB::Var>) -> AB::Expr
    where
        AB: AirBuilder<F = F>,
        <AB as AirBuilder>::Var: Debug,
    {
        self.return_idents
            .iter()
            .map(|i| local.sel[*i].into())
            .sum()
    }

    #[allow(clippy::too_many_arguments)]
    fn eval<AB, H: Hasher<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        sel: &AB::Expr,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, H>,
        call_ctx: CallCtx<F, AB::Expr>,
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        self.ops
            .iter()
            .for_each(|op| op.eval(builder, local, sel, index, map, toplevel));
        self.ctrl
            .eval(builder, local, index, map, toplevel, call_ctx);
    }
}

impl<F: Field> Op<F> {
    #[allow(clippy::too_many_arguments)]
    fn eval<AB, H: Hasher<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        sel: &AB::Expr,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, H>,
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        match self {
            Op::AssertNe(a, b) => {
                let coeffs = (0..a.len()).map(|_| local.next_aux(index)).collect();
                let diffs = a
                    .iter()
                    .zip(b.iter())
                    .map(|(a, b)| {
                        let a = map[*a].to_expr();
                        let b = map[*b].to_expr();
                        a - b
                    })
                    .collect();
                constrain_inequality_witness(sel.clone(), coeffs, diffs, builder);
            }
            Op::AssertEq(a, b) => {
                for (a, b) in a.iter().zip(b.iter()) {
                    let a = &map[*a];
                    let b = &map[*b];
                    builder
                        .when(sel.clone())
                        .assert_eq(a.to_expr(), b.to_expr());
                }
            }
            Op::Contains(a, b) => {
                let b = map[*b].to_expr();
                let acc = a
                    .iter()
                    .map(|a| map[*a].to_expr() - b.clone())
                    .reduce(|acc, diff| {
                        let aux = local.next_aux(index);
                        let acc = acc * diff;
                        builder.when(sel.clone()).assert_eq(acc.clone(), aux);
                        aux.into()
                    })
                    .unwrap();
                builder.when(sel.clone()).assert_zero(acc);
            }
            Op::Const(c) => {
                map.push(Val::Const(*c));
            }
            Op::Add(a, b) => {
                let a = &map[*a];
                let b = &map[*b];
                let c = if let (Val::Const(a), Val::Const(b)) = (a, b) {
                    Val::Const(*a + *b)
                } else {
                    Val::Expr(a.to_expr() + b.to_expr())
                };
                map.push(c);
            }
            Op::Sub(a, b) => {
                let a = &map[*a];
                let b = &map[*b];
                let c = if let (Val::Const(a), Val::Const(b)) = (a, b) {
                    Val::Const(*a - *b)
                } else {
                    Val::Expr(a.to_expr() - b.to_expr())
                };
                map.push(c);
            }
            Op::Mul(a, b) => {
                let a = &map[*a];
                let b = &map[*b];
                let c = if let (Val::Const(a), Val::Const(b)) = (a, b) {
                    Val::Const(*a * *b)
                } else {
                    let c = local.next_aux(index);
                    builder
                        .when(sel.clone())
                        .assert_eq(a.to_expr() * b.to_expr(), c);
                    Val::Expr(c.into())
                };
                map.push(c);
            }
            Op::Inv(a) => {
                let a = &map[*a];
                let c = if let Val::Const(a) = a {
                    Val::Const(a.inverse())
                } else {
                    let c = local.next_aux(index);
                    builder.when(sel.clone()).assert_one(a.to_expr() * c);
                    Val::Expr(c.into())
                };
                map.push(c);
            }
            Op::Not(a) => {
                let a = &map[*a];
                let x = if let Val::Const(a) = a {
                    let x = if a.is_zero() { F::one() } else { F::zero() };
                    Val::Const(x)
                } else {
                    let d = local.next_aux(index);
                    let x = local.next_aux(index);
                    // The two constraints
                    //   a*x = 0
                    //   a*d + x = 1, for some d
                    // means that a = 0 implies x = 1 and that a != 0 implies x = 0
                    // i.e. x = not(a)
                    builder.when(sel.clone()).assert_zero(a.to_expr() * x);
                    builder.when(sel.clone()).assert_one(a.to_expr() * d + x);
                    Val::Expr(x.into())
                };
                map.push(x);
            }
            Op::Call(idx, inp, _) => {
                let func = toplevel.get_by_index(*idx);
                let mut out = Vec::with_capacity(func.output_size);
                for _ in 0..func.output_size {
                    let o = local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                    out.push(o.into());
                }
                let inp = inp.iter().map(|i| map[*i].to_expr());
                let prev_nonce = local.next_aux(index);
                let prev_count = local.next_aux(index);
                let count_inv = local.next_aux(index);
                let record = RequireRecord {
                    prev_nonce,
                    prev_count,
                    count_inv,
                };
                builder.require(
                    CallRelation(F::from_canonical_usize(*idx), inp, out),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::PreImg(idx, out, _) => {
                let func = toplevel.get_by_index(*idx);
                let mut inp = Vec::with_capacity(func.input_size);
                for _ in 0..func.input_size {
                    let i = local.next_aux(index);
                    map.push(Val::Expr(i.into()));
                    inp.push(i.into());
                }
                let out = out.iter().map(|o| map[*o].to_expr());
                let prev_nonce = local.next_aux(index);
                let prev_count = local.next_aux(index);
                let count_inv = local.next_aux(index);
                let record = RequireRecord {
                    prev_nonce,
                    prev_count,
                    count_inv,
                };
                builder.require(
                    CallRelation(F::from_canonical_usize(*idx), inp, out),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::Store(values, _) => {
                let ptr = local.next_aux(index);
                map.push(Val::Expr(ptr.into()));
                let values = values.iter().map(|&idx| map[idx].to_expr());

                let prev_nonce = local.next_aux(index);
                let prev_count = local.next_aux(index);
                let count_inv = local.next_aux(index);
                let record = RequireRecord {
                    prev_nonce,
                    prev_count,
                    count_inv,
                };

                builder.require(
                    MemoryRelation(ptr, values),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::Load(len, ptr, _) => {
                let ptr = map[*ptr].to_expr();
                // This must be collected to ensure the side effects take place
                let values = (0..*len)
                    .map(|_| {
                        let o = local.next_aux(index);
                        map.push(Val::Expr(o.into()));
                        o
                    })
                    .collect::<Vec<_>>();

                let prev_nonce = local.next_aux(index);
                let prev_count = local.next_aux(index);
                let count_inv = local.next_aux(index);
                let record = RequireRecord {
                    prev_nonce,
                    prev_count,
                    count_inv,
                };

                builder.require(
                    MemoryRelation(ptr, values),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::Hash(preimg) => {
                let preimg: Vec<_> = preimg.iter().map(|a| map[*a].to_expr()).collect();
                let hasher = &toplevel.hasher;
                let img_size = hasher.img_size();
                let img_vars = local.next_n_aux(index, img_size);
                let witness_size = hasher.witness_size(preimg.len());
                let witness = local.next_n_aux(index, witness_size);
                hasher.eval_preimg(builder, preimg, img_vars, witness, sel.clone());
                for &img_var in img_vars {
                    map.push(Val::Expr(img_var.into()))
                }
            }
            Op::Debug(..) => (),
        }
    }
}

impl<F: Field> Ctrl<F> {
    fn eval<AB, H: Hasher<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, H>,
        call_ctx: CallCtx<F, AB::Expr>,
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        match self {
            Ctrl::Choose(_, cases) => {
                let map_len = map.len();
                let init_state = index.save();

                let mut process = |block: &Block<F>| {
                    let sel = block.return_sel::<AB>(local);
                    block.eval(builder, local, &sel, index, map, toplevel, call_ctx.clone());
                    map.truncate(map_len);
                    index.restore(init_state);
                };
                cases.branches.iter().for_each(|(_, block)| process(block));
                if let Some(block) = cases.default.as_ref() {
                    process(block)
                };
            }
            Ctrl::ChooseMany(_, cases) => {
                let map_len = map.len();
                let init_state = index.save();

                let mut process = |block: &Block<F>| {
                    let sel = block.return_sel::<AB>(local);
                    block.eval(builder, local, &sel, index, map, toplevel, call_ctx.clone());
                    map.truncate(map_len);
                    index.restore(init_state);
                };
                cases.branches.iter().for_each(|(_, block)| process(block));
                if let Some(block) = cases.default.as_ref() {
                    process(block)
                };
            }
            Ctrl::Return(ident, vs) => {
                let sel = local.sel[*ident];
                let out = vs.iter().map(|v| map[*v].to_expr());
                let CallCtx { func_idx, call_inp } = call_ctx;
                let last_nonce = local.next_aux(index);
                let last_count = local.next_aux(index);
                let record = ProvideRecord {
                    last_nonce,
                    last_count,
                };
                builder.provide(CallRelation(func_idx, call_inp, out), record, sel);
            }
        }
    }
}

fn constrain_inequality_witness<AB: AirBuilder>(
    sel: AB::Expr,
    coeffs: Vec<AB::Var>,
    vals: Vec<AB::Expr>,
    builder: &mut AB,
) {
    let acc: AB::Expr = coeffs
        .into_iter()
        .zip(vals)
        .map(|(coeff, val)| coeff * val)
        .sum();
    builder.when(sel).assert_one(acc);
}

#[cfg(test)]
mod tests {
    use crate::{
        air::debug::debug_constraints_collecting_queries,
        func,
        lair::{execute::Shard, hasher::LurkHasher},
    };
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use crate::lair::{demo_toplevel, execute::QueryRecord, field_from_u32};

    use super::*;

    type F = BabyBear;

    #[test]
    fn lair_constraint_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();
        let mut queries = QueryRecord::new(&toplevel);
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        toplevel.execute_by_name("factorial", &[F::from_canonical_usize(5)], &mut queries);
        let factorial_trace = factorial_chip.generate_trace(&Shard::new(&queries));
        let factorial_width = factorial_chip.width();
        let expected_factorial_trace = RowMajorMatrix::new(
            [
                // in order: nonce, n, 1/n, fact(n-1), prev_nonce, prev_count, count_inv, n*fact(n-1), and selectors
                0, 5, 1610612737, 24, 0, 0, 1, 120, 0, 1, 1, 0, //
                1, 4, 1509949441, 6, 0, 0, 1, 24, 0, 1, 1, 0, //
                2, 3, 1342177281, 2, 0, 0, 1, 6, 1, 1, 1, 0, //
                3, 2, 1006632961, 1, 0, 0, 1, 2, 2, 1, 1, 0, //
                4, 1, 1, 1, 0, 0, 1, 1, 3, 1, 1, 0, //
                5, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 1, //
                // dummy
                6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            factorial_width,
        );
        assert_eq!(factorial_trace, expected_factorial_trace);

        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        toplevel.execute_by_name("fib", &[F::from_canonical_usize(7)], &mut queries);
        let fib_trace = fib_chip.generate_trace(&Shard::new(&queries));
        let fib_width = fib_chip.width();
        let expected_fib_trace = RowMajorMatrix::new(
            // in order: nonce, n, 1/n, 1/(n-1), fib(n-1), lookup nonces and counts, fib(n-2), lookup nonces and counts, and selectors
            [
                0, 7, 862828252, 1677721601, 13, 0, 0, 1, 8, 1, 1, 1006632961, 0, 1, 0, 0,
                1, //
                1, 6, 1677721601, 1610612737, 8, 0, 0, 1, 5, 2, 1, 1006632961, 0, 1, 0, 0,
                1, //
                2, 5, 1610612737, 1509949441, 5, 0, 0, 1, 3, 3, 1, 1006632961, 0, 2, 0, 0,
                1, //
                3, 4, 1509949441, 1342177281, 3, 0, 0, 1, 2, 4, 1, 1006632961, 1, 2, 0, 0,
                1, //
                4, 3, 1342177281, 1006632961, 2, 0, 0, 1, 1, 5, 1, 1006632961, 2, 2, 0, 0,
                1, //
                5, 2, 1006632961, 1, 1, 0, 0, 1, 1, 0, 0, 1, 3, 2, 0, 0, 1, //
                6, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, //
                7, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            fib_width,
        );
        assert_eq!(fib_trace, expected_fib_trace);

        let _ = debug_constraints_collecting_queries(&factorial_chip, &[], None, &factorial_trace);
        let _ = debug_constraints_collecting_queries(&fib_chip, &[], None, &fib_trace);
    }

    #[test]
    fn lair_long_constraint_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let args = &[field_from_u32(20000)];
        let mut queries = QueryRecord::new(&toplevel);
        toplevel.execute_by_name("fib", args, &mut queries);
        let fib_trace = fib_chip.generate_trace(&Shard::new(&queries));

        let _ = debug_constraints_collecting_queries(&fib_chip, &[], None, &fib_trace);
    }

    #[test]
    fn lair_not_eq_test() {
        let not_func = func!(
        fn not(a): [1] {
            let x = not(a);
            return x
        });
        let eq_func = func!(
        fn eq(a, b): [1] {
            let x = eq(a, b);
            return x
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[eq_func, not_func]);
        let eq_chip = FuncChip::from_name("eq", &toplevel);
        let not_chip = FuncChip::from_name("not", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[field_from_u32(4)];
        toplevel.execute_by_name("not", args, &mut queries);
        let args = &[field_from_u32(8)];
        toplevel.execute_by_name("not", args, &mut queries);
        let args = &[field_from_u32(0)];
        toplevel.execute_by_name("not", args, &mut queries);
        let args = &[field_from_u32(1)];
        toplevel.execute_by_name("not", args, &mut queries);
        let not_trace = not_chip.generate_trace(&Shard::new(&queries));

        let not_width = not_chip.width();
        let expected_not_trace = RowMajorMatrix::new(
            [
                0, 4, 1509949441, 0, 0, 1, 1, //
                1, 8, 1761607681, 0, 0, 1, 1, //
                2, 0, 0, 1, 0, 1, 1, //
                3, 1, 1, 0, 0, 1, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            not_width,
        );
        assert_eq!(not_trace, expected_not_trace);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[field_from_u32(4), field_from_u32(2)];
        toplevel.execute_by_name("eq", args, &mut queries);
        let args = &[field_from_u32(4), field_from_u32(4)];
        toplevel.execute_by_name("eq", args, &mut queries);
        let args = &[field_from_u32(0), field_from_u32(3)];
        toplevel.execute_by_name("eq", args, &mut queries);
        let args = &[field_from_u32(0), field_from_u32(0)];
        toplevel.execute_by_name("eq", args, &mut queries);
        let eq_trace = eq_chip.generate_trace(&Shard::new(&queries));

        let eq_width = eq_chip.width();
        let expected_eq_trace = RowMajorMatrix::new(
            [
                0, 4, 2, 1006632961, 0, 0, 1, 1, //
                1, 4, 4, 0, 1, 0, 1, 1, //
                2, 0, 3, 671088640, 0, 0, 1, 1, //
                3, 0, 0, 0, 1, 0, 1, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            eq_width,
        );
        assert_eq!(eq_trace, expected_eq_trace);

        let _ = debug_constraints_collecting_queries(&not_chip, &[], None, &not_trace);
        let _ = debug_constraints_collecting_queries(&eq_chip, &[], None, &eq_trace);
    }

    #[test]
    fn lair_if_many_test() {
        let if_many_func = func!(
        fn if_many(a: [4]): [1] {
            if a {
                let one = 1;
                return one
            }
            let zero = 0;
            return zero
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[if_many_func]);
        let if_many_chip = FuncChip::from_name("if_many", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0), f(0), f(0)];
        toplevel.execute_by_name("if_many", args, &mut queries);
        let args = &[f(1), f(3), f(8), f(2)];
        toplevel.execute_by_name("if_many", args, &mut queries);
        let args = &[f(0), f(0), f(4), f(1)];
        toplevel.execute_by_name("if_many", args, &mut queries);
        let args = &[f(0), f(0), f(0), f(9)];
        toplevel.execute_by_name("if_many", args, &mut queries);

        let if_many_trace = if_many_chip.generate_trace(&Shard::new(&queries));

        let if_many_width = if_many_chip.width();
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 4 inputs, 6 coeffs, 2 selectors
                0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, //
                1, 1, 3, 8, 2, 1, 0, 0, 0, 0, 1, 1, 0, //
                2, 0, 0, 4, 1, 0, 0, 1509949441, 0, 0, 1, 1, 0, //
                3, 0, 0, 0, 9, 0, 0, 0, 447392427, 0, 1, 1, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            if_many_width,
        );
        assert_eq!(if_many_trace, expected_trace);

        let _ = debug_constraints_collecting_queries(&if_many_chip, &[], None, &expected_trace);
    }

    #[test]
    fn lair_match_many_test() {
        let match_many_func = func!(
        fn match_many(a: [2]): [2] {
            match a {
                [0, 0] => {
                    let res = [1, 0];
                    return res
                }
                [0, 1] => {
                    let res = [1, 1];
                    return res
                }
                [1, 0] => {
                    let res = [1, 2];
                    return res
                }
                [1, 1] => {
                    let res = [1, 3];
                    return res
                }
            };
            let fail = [0, 0];
            return fail
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[match_many_func]);
        let match_many_chip = FuncChip::from_name("match_many", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0)];
        toplevel.execute_by_name("match_many", args, &mut queries);
        let args = &[f(0), f(1)];
        toplevel.execute_by_name("match_many", args, &mut queries);
        let args = &[f(1), f(0)];
        toplevel.execute_by_name("match_many", args, &mut queries);
        let args = &[f(1), f(1)];
        toplevel.execute_by_name("match_many", args, &mut queries);
        let args = &[f(0), f(8)];
        toplevel.execute_by_name("match_many", args, &mut queries);

        let match_many_trace = match_many_chip.generate_trace(&Shard::new(&queries));

        let match_many_width = match_many_chip.width();
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 2 inputs, 10 witness coefficients, 5 selectors
                0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, //
                1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, //
                2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, //
                3, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, //
                4, 0, 8, 0, 1761607681, 0, 862828252, 2013265920, 0, 2013265920, 0, 0, 1, 0, 0, 0,
                0, 1, //
                // dummy queries
                5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            match_many_width,
        );
        assert_eq!(match_many_trace, expected_trace);

        let _ = debug_constraints_collecting_queries(&match_many_chip, &[], None, &expected_trace);
    }

    #[test]
    fn lair_assert_test() {
        let assert_func = func!(
        fn assert(a: [4]): [4] {
            let arr1 = [2, 4, 5, 8];
            let arr2 = [2, 4, 6, 8];
            assert_ne!(a, arr1);
            let two = 2;
            let four = 4;
            contains!(a, two);
            contains!(a, four);
            assert_eq!(a, arr2);
            return a
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[assert_func]);
        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(2), f(4), f(6), f(8)];
        toplevel.execute_by_name("assert", args, &mut queries);
        let chip = FuncChip::from_name("assert", &toplevel);
        let trace = chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 4 inputs, 6 multiplications for the two `contains!`, 4 coefficients for `assert_ne!`, last nonce, last count, selector
                0, 2, 4, 6, 8, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
                // dummies
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            chip.width(),
        );
        assert_eq!(trace, expected_trace);
        let _ = debug_constraints_collecting_queries(&chip, &[], None, &trace);
    }
}
