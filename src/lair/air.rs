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

    pub fn next_input(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.input[index.input];
        index.input += 1;
        t
    }

    pub fn next_aux(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.aux[index.aux];
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

        // this prevents evil provers from starting ahead (maybe close to |F|)
        builder.when_first_row().assert_zero(nonce);

        // nonces are unique, even for dummy rows
        builder
            .when_transition()
            .assert_eq(next_nonce, nonce + F::one());

        let map = &mut vec![];
        let mut call_inp = Vec::with_capacity(self.input_size);
        for _ in 0..self.input_size {
            let i = *local.next_input(index);
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

        let mult = *local.next_aux(index);
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
        builder.when_ne(toplevel_sel, F::one()).assert_zero(mult);
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
                    let c = *local.next_aux(index);
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
                    let c = *local.next_aux(index);
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
                    let d = *local.next_aux(index);
                    let x = *local.next_aux(index);
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
                let func = toplevel.get_by_index(*idx).unwrap();
                let mut out = Vec::with_capacity(func.output_size);
                for _ in 0..func.output_size {
                    let o = *local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                    out.push(o.into());
                }
                let inp = inp.iter().map(|i| map[*i].to_expr());
                let prev_nonce = *local.next_aux(index);
                let prev_count = *local.next_aux(index);
                let count_inv = *local.next_aux(index);
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
                let func = toplevel.get_by_index(*idx).unwrap();
                let mut inp = Vec::with_capacity(func.input_size);
                for _ in 0..func.input_size {
                    let i = *local.next_aux(index);
                    map.push(Val::Expr(i.into()));
                    inp.push(i.into());
                }
                let out = out.iter().map(|o| map[*o].to_expr());
                let prev_nonce = *local.next_aux(index);
                let prev_count = *local.next_aux(index);
                let count_inv = *local.next_aux(index);
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
            Op::Store(values) => {
                let ptr = *local.next_aux(index);
                map.push(Val::Expr(ptr.into()));
                let values = values.iter().map(|&idx| map[idx].to_expr());
                builder.receive(MemoryRelation(ptr, values), sel.clone());
            }
            Op::Load(len, ptr) => {
                let ptr = map[*ptr].to_expr();
                // This must be collected to ensure the side effects take place
                let values = (0..*len)
                    .map(|_| {
                        let o = *local.next_aux(index);
                        map.push(Val::Expr(o.into()));
                        o
                    })
                    .collect::<Vec<_>>();
                builder.receive(MemoryRelation(ptr, values), sel.clone());
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
            Ctrl::Match(v, cases) => {
                let map_len = map.len();
                let init_state = index.save();
                let v = map[*v].to_expr();

                for (f, branch) in cases.branches.iter() {
                    let sel = branch.return_sel::<AB>(local);
                    branch.eval(builder, local, &sel, index, map, toplevel, call_ctx.clone());
                    builder.when(sel).assert_eq(v.clone(), *f);
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                if let Some(branch) = &cases.default {
                    let invs = (0..cases.branches.size())
                        .map(|_| *local.next_aux(index))
                        .collect::<Vec<_>>();
                    let sel = branch.return_sel::<AB>(local);
                    branch.eval(builder, local, &sel, index, map, toplevel, call_ctx);
                    for ((f, _), inv) in cases.branches.iter().zip(invs.into_iter()) {
                        builder.when(sel.clone()).assert_one(inv * (v.clone() - *f));
                    }
                    map.truncate(map_len);
                    index.restore(init_state);
                }
            }
            Ctrl::MatchMany(vars, cases) => {
                let map_len = map.len();
                let init_state = index.save();
                let vals: Vec<_> = vars.iter().map(|&var| map[var].to_expr()).collect();

                for (fs, branch) in cases.branches.iter() {
                    let sel = branch.return_sel::<AB>(local);
                    branch.eval(builder, local, &sel, index, map, toplevel, call_ctx.clone());
                    vals.iter()
                        .zip(fs.iter())
                        .for_each(|(v, f)| builder.when(sel.clone()).assert_eq(v.clone(), *f));
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                if let Some(branch) = &cases.default {
                    let wit: Vec<Vec<_>> = (0..cases.branches.size())
                        .map(|_| (0..vars.len()).map(|_| *local.next_aux(index)).collect())
                        .collect();
                    let sel = branch.return_sel::<AB>(local);
                    branch.eval(builder, local, &sel, index, map, toplevel, call_ctx);
                    for (coeffs, (fs, _)) in wit.into_iter().zip(cases.branches.iter()) {
                        let diffs = vals
                            .iter()
                            .zip(fs.iter())
                            .map(|(v, f)| v.clone() - *f)
                            .collect();
                        constrain_inequality_witness(sel.clone(), coeffs, diffs, builder);
                    }
                    map.truncate(map_len);
                    index.restore(init_state);
                }
            }
            Ctrl::If(b, t, f) => {
                let map_len = map.len();
                let init_state = index.save();
                let b = map[*b].to_expr();

                let inv = *local.next_aux(index);
                let t_sel = t.return_sel::<AB>(local);
                t.eval(
                    builder,
                    local,
                    &t_sel,
                    index,
                    map,
                    toplevel,
                    call_ctx.clone(),
                );
                builder.when(t_sel).assert_one(inv * b.clone());
                map.truncate(map_len);
                index.restore(init_state);

                let f_sel = f.return_sel::<AB>(local);
                f.eval(builder, local, &f_sel, index, map, toplevel, call_ctx);
                builder.when(f_sel).assert_zero(b);
                map.truncate(map_len);
                index.restore(init_state);
            }
            Ctrl::IfMany(vars, t, f) => {
                let map_len = map.len();
                let init_state = index.save();

                let coeffs = vars.iter().map(|_| *local.next_aux(index)).collect();
                let vals = vars.iter().map(|&v| map[v].to_expr()).collect();
                let t_sel = t.return_sel::<AB>(local);
                t.eval(
                    builder,
                    local,
                    &t_sel,
                    index,
                    map,
                    toplevel,
                    call_ctx.clone(),
                );
                constrain_inequality_witness(t_sel, coeffs, vals, builder);
                map.truncate(map_len);
                index.restore(init_state);

                let f_sel = f.return_sel::<AB>(local);
                f.eval(builder, local, &f_sel, index, map, toplevel, call_ctx);
                for var in vars.iter() {
                    let b = map[*var].to_expr();
                    builder.when(f_sel.clone()).assert_zero(b);
                }
                map.truncate(map_len);
                index.restore(init_state);
            }
            Ctrl::Return(ident, vs) => {
                let sel = local.sel[*ident];
                let out = vs.iter().map(|v| map[*v].to_expr());
                let CallCtx { func_idx, call_inp } = call_ctx;
                let last_nonce = *local.next_aux(index);
                let last_count = *local.next_aux(index);
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
    use crate::{air::debug::debug_constraints_collecting_queries, func, lair::hasher::LurkHasher};
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use crate::lair::{demo_toplevel, execute::QueryRecord, field_from_u32};

    use super::*;

    type F = BabyBear;

    #[test]
    fn lair_constraint_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let factorial_width = factorial_chip.width();
        let factorial_trace = RowMajorMatrix::new(
            [
                // in order: n, mult, 1/n, fact(n-1), n*fact(n-1), and selectors
                0, 1, 0, 0, 0, 0, 1, //
                1, 1, 1, 1, 1, 1, 0, //
                2, 1, 1006632961, 1, 2, 1, 0, //
                3, 1, 1342177281, 2, 6, 1, 0, //
                4, 1, 1509949441, 6, 24, 1, 0, //
                5, 1, 1610612737, 24, 120, 1, 0, //
                // dummy
                0, 0, 0, 0, 0, 0, 0, //
                0, 0, 0, 0, 0, 0, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            factorial_width,
        );
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let fib_width = fib_chip.width();
        let fib_trace = RowMajorMatrix::new(
            [
                // in order: n, mult, 1/n, 1/(n-1), fib(n-1), fib(n-2), and selectors
                0, 1, 0, 0, 0, 0, 1, 0, 0, //
                1, 2, 0, 0, 0, 0, 0, 1, 0, //
                2, 2, 1006632961, 1, 1, 1, 0, 0, 1, //
                3, 2, 1342177281, 1006632961, 2, 1, 0, 0, 1, //
                4, 2, 1509949441, 1342177281, 3, 2, 0, 0, 1, //
                5, 2, 1610612737, 1509949441, 5, 3, 0, 0, 1, //
                6, 1, 1677721601, 1610612737, 8, 5, 0, 0, 1, //
                7, 1, 862828252, 1677721601, 13, 8, 0, 0, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            fib_width,
        );

        let _ = debug_constraints_collecting_queries(&factorial_chip, &[], None, &factorial_trace);
        let _ = debug_constraints_collecting_queries(&fib_chip, &[], None, &fib_trace);
    }

    #[test]
    fn lair_long_constraint_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let args = &[field_from_u32(20000)];
        let queries = &mut QueryRecord::new(&toplevel);
        toplevel.execute_iter_by_name("fib", args, queries);
        let fib_trace = fib_chip.generate_trace_parallel(queries);

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

        let queries = &mut QueryRecord::new(&toplevel);
        let args = &[field_from_u32(4)];
        toplevel.execute_iter_by_name("not", args, queries);
        let args = &[field_from_u32(8)];
        toplevel.execute_iter_by_name("not", args, queries);
        let args = &[field_from_u32(0)];
        toplevel.execute_iter_by_name("not", args, queries);
        let args = &[field_from_u32(1)];
        toplevel.execute_iter_by_name("not", args, queries);

        let not_width = not_chip.width();
        let not_trace = RowMajorMatrix::new(
            [
                0, 1, 0, 1, 1, //
                1, 1, 1, 0, 1, //
                4, 1, 1509949441, 0, 1, //
                8, 1, 1761607681, 0, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            not_width,
        );

        let args = &[field_from_u32(4), field_from_u32(2)];
        toplevel.execute_iter_by_name("eq", args, queries);
        let args = &[field_from_u32(4), field_from_u32(4)];
        toplevel.execute_iter_by_name("eq", args, queries);
        let args = &[field_from_u32(0), field_from_u32(3)];
        toplevel.execute_iter_by_name("eq", args, queries);
        let args = &[field_from_u32(0), field_from_u32(0)];
        toplevel.execute_iter_by_name("eq", args, queries);

        let eq_width = eq_chip.width();
        let eq_trace = RowMajorMatrix::new(
            [
                0, 0, 1, 0, 1, 1, //
                0, 3, 1, 671088640, 0, 1, //
                4, 2, 1, 1006632961, 0, 1, //
                4, 4, 1, 0, 1, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            eq_width,
        );

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

        let queries = &mut QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0), f(0), f(0)];
        toplevel.execute_iter_by_name("if_many", args, queries);
        let args = &[f(1), f(3), f(8), f(2)];
        toplevel.execute_iter_by_name("if_many", args, queries);
        let args = &[f(0), f(0), f(4), f(1)];
        toplevel.execute_iter_by_name("if_many", args, queries);
        let args = &[f(0), f(0), f(0), f(9)];
        toplevel.execute_iter_by_name("if_many", args, queries);

        let if_many_trace = if_many_chip.generate_trace_parallel(queries);

        let if_many_width = if_many_chip.width();
        let expected_trace = RowMajorMatrix::new(
            [
                // 4 inputs, mult, 4 coeffs, 2 selectors
                0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, //
                1, 3, 8, 2, 1, 1, 0, 0, 0, 1, 0, //
                0, 0, 4, 1, 1, 0, 0, 1509949441, 0, 1, 0, //
                0, 0, 0, 9, 1, 0, 0, 0, 447392427, 1, 0, //
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

        let queries = &mut QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0)];
        toplevel.execute_iter_by_name("match_many", args, queries);
        let args = &[f(0), f(1)];
        toplevel.execute_iter_by_name("match_many", args, queries);
        let args = &[f(1), f(0)];
        toplevel.execute_iter_by_name("match_many", args, queries);
        let args = &[f(1), f(1)];
        toplevel.execute_iter_by_name("match_many", args, queries);
        let args = &[f(0), f(8)];
        toplevel.execute_iter_by_name("match_many", args, queries);

        let match_many_trace = match_many_chip.generate_trace_parallel(queries);

        let match_many_width = match_many_chip.width();
        let expected_trace = RowMajorMatrix::new(
            [
                // 2 inputs, mult, 8 witness coefficients, 5 selectors
                0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, //
                0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, //
                1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, //
                1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, //
                0, 8, 1, 0, 1761607681, 0, 862828252, 2013265920, 0, 2013265920, 0, 0, 0, 0, 0,
                1, //
                // dummy queries
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            match_many_width,
        );
        assert_eq!(match_many_trace, expected_trace);

        let _ = debug_constraints_collecting_queries(&match_many_chip, &[], None, &expected_trace);
    }
}
