use p3_air::{Air, AirBuilder};
use p3_field::Field;
use p3_matrix::Matrix;
use std::{borrow::Borrow, fmt::Debug};

use crate::{
    air::builder::{LookupBuilder, ProvideRecord, RequireRecord},
    gadgets::{
        bytes::{builder::BytesAirRecordWithContext, ByteAirRecord},
        unsigned::Word32,
    },
};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chipset::Chipset,
    func_chip::{ColumnLayout, FuncChip, LayoutSizes},
    provenance::{DepthLessThan, DEPTH_LESS_THAN_SIZE, DEPTH_W},
    relations::{CallRelation, MemoryRelation},
    toplevel::Toplevel,
    trace::ColumnIndex,
};

impl ColumnIndex {
    #[inline]
    fn save(&mut self) -> (usize, usize) {
        (self.aux, self.output)
    }

    #[inline]
    fn restore(&mut self, (aux, output): (usize, usize)) {
        self.aux = aux;
        self.output = output;
    }
}

pub type ColumnSlice<'a, T> = ColumnLayout<&'a T, &'a [T]>;

impl<'a, T> ColumnSlice<'a, T> {
    pub fn from_slice(slice: &'a [T], layout_sizes: LayoutSizes) -> Self {
        let (nonce, slice) = slice.split_at(1);
        let (input, slice) = slice.split_at(layout_sizes.input);
        let (output, slice) = slice.split_at(layout_sizes.output);
        let (aux, slice) = slice.split_at(layout_sizes.aux);
        let (sel, slice) = slice.split_at(layout_sizes.sel);
        assert!(slice.is_empty());
        let nonce = &nonce[0];
        Self {
            nonce,
            input,
            output,
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

    pub fn next_output(&self, index: &mut ColumnIndex) -> T
    where
        T: Copy,
    {
        let t = self.output[index.output];
        index.output += 1;
        t
    }

    pub fn next_n_aux(&self, index: &mut ColumnIndex, n: usize) -> &[T] {
        let slice = &self.aux[index.aux..index.aux + n];
        index.aux += n;
        slice
    }

    pub fn next_require(&self, index: &mut ColumnIndex) -> RequireRecord<T>
    where
        T: Copy,
    {
        let prev_nonce = self.next_aux(index);
        let prev_count = self.next_aux(index);
        let count_inv = self.next_aux(index);
        RequireRecord {
            prev_nonce,
            prev_count,
            count_inv,
        }
    }
}

fn eval_depth<F: Field, AB>(
    builder: &mut AB,
    local: ColumnSlice<'_, AB::Var>,
    index: &mut ColumnIndex,
    depth: &[AB::Expr],
    sel: &AB::Expr,
    out: &mut Vec<AB::Expr>,
) where
    AB: AirBuilder<F = F> + LookupBuilder,
{
    let dep_depth: &[_] = &(0..DEPTH_W)
        .map(|_| local.next_aux(index).into())
        .collect::<Vec<_>>();
    let witness: &[_] = &(0..DEPTH_LESS_THAN_SIZE)
        .map(|_| local.next_aux(index))
        .collect::<Vec<_>>();
    let less_than: &DepthLessThan<_> = witness.borrow();
    let mut air_record = BytesAirRecordWithContext::default();
    let dep_depth_word: &Word32<_> = dep_depth.borrow();
    let depth: &Word32<_> = depth.borrow();
    less_than.assert_less_than(builder, dep_depth_word, depth, &mut air_record, sel.clone());
    let requires = (0..DepthLessThan::<F>::num_requires())
        .map(|_| local.next_require(index))
        .collect::<Vec<_>>();
    air_record.require_all(builder, (*local.nonce).into(), requires);
    out.extend(dep_depth.iter().cloned());
}

impl<AB, C1: Chipset<AB::F>, C2: Chipset<AB::F>> Air<AB> for FuncChip<'_, AB::F, C1, C2>
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
    fn eval<AB, C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        builder: &mut AB,
        toplevel: &Toplevel<F, C1, C2>,
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
                .func_map
                .get_index_of(&self.name)
                .expect("Func not found on toplevel"),
        );

        let toplevel_sel = self.body.return_sel::<AB>(local);
        builder.assert_bool(toplevel_sel.clone());
        let last_nonce = local.next_aux(index);
        let last_count = local.next_aux(index);
        // provenance and range check
        let record = ProvideRecord {
            last_nonce,
            last_count,
        };
        let mut out = (0..self.output_size)
            .map(|i| local.output[i].into())
            .collect::<Vec<_>>();
        let depth = if self.partial {
            let depth = (0..DEPTH_W)
                .map(|_| local.next_aux(index))
                .collect::<Vec<_>>();
            let depth_expr = depth.iter().map(|&b| b.into()).collect::<Vec<AB::Expr>>();
            let num_requires = (DEPTH_W / 2) + (DEPTH_W % 2);
            let requires = (0..num_requires)
                .map(|_| local.next_require(index))
                .collect::<Vec<_>>();
            let mut air_record = BytesAirRecordWithContext::default();
            air_record.range_check_u8_iter(depth, toplevel_sel.clone());
            air_record.require_all(builder, (*local.nonce).into(), requires);
            out.extend_from_slice(&depth_expr);
            depth_expr
        } else {
            vec![]
        };
        builder.provide(
            CallRelation(func_idx, call_inp, out),
            record,
            toplevel_sel.clone(),
        );
        self.body
            .eval(builder, local, &toplevel_sel, index, map, toplevel, &depth);
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
    fn eval<AB, C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        sel: &AB::Expr,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, C1, C2>,
        depth: &[AB::Expr],
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        self.ops
            .iter()
            .for_each(|op| op.eval(builder, local, sel, index, map, toplevel, depth));
        self.ctrl.eval(builder, local, index, map, toplevel, depth);
    }
}

impl<F: Field> Op<F> {
    #[allow(clippy::too_many_arguments)]
    fn eval<AB, C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        sel: &AB::Expr,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, C1, C2>,
        depth: &[AB::Expr],
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
            Op::AssertEq(a, b, _) => {
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
            Op::Call(idx, inp) => {
                let func = toplevel.func_by_index(*idx);
                let mut out = Vec::with_capacity(func.output_size);
                for _ in 0..func.output_size {
                    let o = local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                    out.push(o.into());
                }
                let inp = inp.iter().map(|i| map[*i].to_expr());
                let record = local.next_require(index);
                // dependency provenance and constraints
                if func.partial {
                    eval_depth(builder, local, index, depth, sel, &mut out);
                };
                builder.require(
                    CallRelation(F::from_canonical_usize(*idx), inp, out),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::PreImg(idx, out, _) => {
                let func = toplevel.func_by_index(*idx);
                let mut inp = Vec::with_capacity(func.input_size);
                for _ in 0..func.input_size {
                    let i = local.next_aux(index);
                    map.push(Val::Expr(i.into()));
                    inp.push(i.into());
                }
                let mut out = out.iter().map(|o| map[*o].to_expr()).collect::<Vec<_>>();
                let record = local.next_require(index);
                // dependency provenance and constraints
                if func.partial {
                    eval_depth(builder, local, index, depth, sel, &mut out);
                };
                builder.require(
                    CallRelation(F::from_canonical_usize(*idx), inp, out),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::Store(values) => {
                let ptr = local.next_aux(index);
                map.push(Val::Expr(ptr.into()));
                let values = values.iter().map(|&idx| map[idx].to_expr());
                let record = local.next_require(index);
                builder.require(
                    MemoryRelation(ptr, values),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::Load(len, ptr) => {
                let ptr = map[*ptr].to_expr();
                // This must be collected to ensure the side effects take place
                let values = (0..*len)
                    .map(|_| {
                        let o = local.next_aux(index);
                        map.push(Val::Expr(o.into()));
                        o
                    })
                    .collect::<Vec<_>>();
                let record = local.next_require(index);
                builder.require(
                    MemoryRelation(ptr, values),
                    *local.nonce,
                    record,
                    sel.clone(),
                );
            }
            Op::ExternCall(chip_idx, input) => {
                let input: Vec<_> = input.iter().map(|a| map[*a].to_expr()).collect();
                let chip = toplevel.chip_by_index(*chip_idx);

                // order: witness, requires
                let witness = local.next_n_aux(index, chip.witness_size());
                let requires = (0..chip.require_size())
                    .map(|_| local.next_require(index))
                    .collect::<Vec<_>>();

                let output_vars = chip.eval(
                    builder,
                    sel.clone(),
                    input,
                    witness,
                    (*local.nonce).into(),
                    &requires,
                );
                for img_var in output_vars {
                    map.push(Val::Expr(img_var))
                }
            }
            Op::RangeU8(xs) => {
                let num_requires = (xs.len() / 2) + (xs.len() % 2);
                let requires = (0..num_requires)
                    .map(|_| local.next_require(index))
                    .collect::<Vec<_>>();
                let mut air_record = BytesAirRecordWithContext::default();
                let xs = xs.iter().map(|x| map[*x].to_expr());
                air_record.range_check_u8_iter(xs, sel.clone());
                air_record.require_all(builder, (*local.nonce).into(), requires);
            }
            Op::Emit(_) | Op::Breakpoint | Op::Debug(_) => (),
        }
    }
}

impl<F: Field> Ctrl<F> {
    fn eval<AB, C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F, C1, C2>,
        depth: &[AB::Expr],
    ) where
        AB: AirBuilder<F = F> + LookupBuilder,
        <AB as AirBuilder>::Var: Debug,
    {
        match self {
            Ctrl::Choose(_, _, branches) => {
                let map_len = map.len();
                let init_state = index.save();

                branches.iter().for_each(|block| {
                    let sel = block.return_sel::<AB>(local);
                    block.eval(builder, local, &sel, index, map, toplevel, depth);
                    map.truncate(map_len);
                    index.restore(init_state);
                });
            }
            Ctrl::ChooseMany(_, cases) => {
                let map_len = map.len();
                let init_state = index.save();

                let mut process = |block: &Block<F>| {
                    let sel = block.return_sel::<AB>(local);
                    block.eval(builder, local, &sel, index, map, toplevel, depth);
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
                out.for_each(|o| {
                    let out_var = local.next_output(index);
                    builder.when(sel).assert_eq(o, out_var);
                });
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
        lair::{chipset::NoChip, execute::Shard},
    };
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use crate::lair::{demo_toplevel, execute::QueryRecord, field_from_u32};

    use super::*;

    type F = BabyBear;

    #[test]
    fn lair_constraint_test() {
        let toplevel = demo_toplevel::<_>();

        let mut queries = QueryRecord::new(&toplevel);
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        toplevel
            .execute_by_name(
                "factorial",
                &[F::from_canonical_usize(5)],
                &mut queries,
                None,
            )
            .unwrap();
        let factorial_trace = factorial_chip.generate_trace(&Shard::new(&queries));
        let _ = debug_constraints_collecting_queries(&factorial_chip, &[], None, &factorial_trace);

        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        toplevel
            .execute_by_name("fib", &[F::from_canonical_usize(7)], &mut queries, None)
            .unwrap();
        let fib_trace = fib_chip.generate_trace(&Shard::new(&queries));
        let _ = debug_constraints_collecting_queries(&fib_chip, &[], None, &fib_trace);
    }

    #[test]
    fn lair_long_constraint_test() {
        let toplevel = demo_toplevel::<F>();
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let args = &[field_from_u32(20000)];
        let mut queries = QueryRecord::new(&toplevel);
        toplevel
            .execute_by_name("fib", args, &mut queries, None)
            .unwrap();
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[eq_func, not_func]);
        let eq_chip = FuncChip::from_name("eq", &toplevel);
        let not_chip = FuncChip::from_name("not", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[field_from_u32(4)];
        toplevel
            .execute_by_name("not", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(8)];
        toplevel
            .execute_by_name("not", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(0)];
        toplevel
            .execute_by_name("not", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(1)];
        toplevel
            .execute_by_name("not", args, &mut queries, None)
            .unwrap();
        let not_trace = not_chip.generate_trace(&Shard::new(&queries));

        let not_width = not_chip.width();
        #[rustfmt::skip]
        let expected_not_trace = RowMajorMatrix::new(
            [
                0, 4, 0, 0, 1, 1509949441, 0, 1,
                1, 8, 0, 0, 1, 1761607681, 0, 1,
                2, 0, 1, 0, 1,          0, 1, 1,
                3, 1, 0, 0, 1,          1, 0, 1,
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            not_width,
        );
        assert_eq!(not_trace, expected_not_trace);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[field_from_u32(4), field_from_u32(2)];
        toplevel
            .execute_by_name("eq", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(4), field_from_u32(4)];
        toplevel
            .execute_by_name("eq", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(0), field_from_u32(3)];
        toplevel
            .execute_by_name("eq", args, &mut queries, None)
            .unwrap();
        let args = &[field_from_u32(0), field_from_u32(0)];
        toplevel
            .execute_by_name("eq", args, &mut queries, None)
            .unwrap();
        let eq_trace = eq_chip.generate_trace(&Shard::new(&queries));

        let eq_width = eq_chip.width();
        #[rustfmt::skip]
        let expected_eq_trace = RowMajorMatrix::new(
            [
                0, 4, 2, 0, 0, 1, 1006632961, 0, 1,
                1, 4, 4, 1, 0, 1,          0, 1, 1,
                2, 0, 3, 0, 0, 1,  671088640, 0, 1,
                3, 0, 0, 1, 0, 1,          0, 1, 1,
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[if_many_func]);
        let if_many_chip = FuncChip::from_name("if_many", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0), f(0), f(0)];
        toplevel
            .execute_by_name("if_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(1), f(3), f(8), f(2)];
        toplevel
            .execute_by_name("if_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(0), f(0), f(4), f(1)];
        toplevel
            .execute_by_name("if_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(0), f(0), f(0), f(9)];
        toplevel
            .execute_by_name("if_many", args, &mut queries, None)
            .unwrap();

        let if_many_trace = if_many_chip.generate_trace(&Shard::new(&queries));

        let if_many_width = if_many_chip.width();
        #[rustfmt::skip]
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 4 inputs, 1 output, last_nonce, last_count, 6 coeffs, 2 selectors
                0, 0, 0, 0, 0, 0, 0, 1, 0, 0,          0,         0, 1, 0,
                1, 1, 3, 8, 2, 1, 0, 1, 1, 0,          0,         0, 0, 1,
                2, 0, 0, 4, 1, 1, 0, 1, 0, 0, 1509949441,         0, 0, 1,
                3, 0, 0, 0, 9, 1, 0, 1, 0, 0,          0, 447392427, 0, 1,
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[match_many_func]);
        let match_many_chip = FuncChip::from_name("match_many", &toplevel);

        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(0), f(0)];
        toplevel
            .execute_by_name("match_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(0), f(1)];
        toplevel
            .execute_by_name("match_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(1), f(0)];
        toplevel
            .execute_by_name("match_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(1), f(1)];
        toplevel
            .execute_by_name("match_many", args, &mut queries, None)
            .unwrap();
        let args = &[f(0), f(8)];
        toplevel
            .execute_by_name("match_many", args, &mut queries, None)
            .unwrap();

        let match_many_trace = match_many_chip.generate_trace(&Shard::new(&queries));

        let match_many_width = match_many_chip.width();
        #[rustfmt::skip]
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 2 inputs, 2 outputs, last_nonce, last_count, 10 witness coefficients, 5 selectors
                0, 0, 0, 1, 0, 0, 1, 0,          0, 0,          0,         0, 0,          0, 0, 1, 0, 0, 0, 0,
                1, 0, 1, 1, 1, 0, 1, 0,          0, 0,          0,         0, 0,          0, 0, 0, 1, 0, 0, 0,
                2, 1, 0, 1, 2, 0, 1, 0,          0, 0,          0,         0, 0,          0, 0, 0, 0, 1, 0, 0,
                3, 1, 1, 1, 3, 0, 1, 0,          0, 0,          0,         0, 0,          0, 0, 0, 0, 0, 1, 0,
                4, 0, 8, 0, 0, 0, 1, 0, 1761607681, 0, 862828252, 2013265920, 0, 2013265920, 0, 0, 0, 0, 0, 1,
                5, 0, 0, 0, 0, 0, 0, 0,          0, 0,          0,         0, 0,          0, 0, 0, 0, 0, 0, 0,
                // dummies
                6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[assert_func]);
        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(2), f(4), f(6), f(8)];
        toplevel
            .execute_by_name("assert", args, &mut queries, None)
            .unwrap();
        let chip = FuncChip::from_name("assert", &toplevel);
        let trace = chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = RowMajorMatrix::new(
            [
                // nonce, 4 inputs, 4 output, last nonce, last count, 6 multiplications for the two `contains!`, 4 coefficients for `assert_ne!`, selector
                0, 2, 4, 6, 8, 2, 4, 6, 8, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            chip.width(),
        );
        assert_eq!(trace, expected_trace);
        let _ = debug_constraints_collecting_queries(&chip, &[], None, &trace);
    }

    #[test]
    fn lair_equal_branch_test() {
        let func = func!(
        fn test(a): [1] {
            match a {
                2, 3, 4 => {
                    let one = 1;
                    return one
                }
            };
            return a
        });
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[func]);
        let mut queries = QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = &[f(1)];
        toplevel
            .execute_by_name("test", args, &mut queries, None)
            .unwrap();
        let args = &[f(2)];
        toplevel
            .execute_by_name("test", args, &mut queries, None)
            .unwrap();
        let args = &[f(3)];
        toplevel
            .execute_by_name("test", args, &mut queries, None)
            .unwrap();
        let args = &[f(4)];
        toplevel
            .execute_by_name("test", args, &mut queries, None)
            .unwrap();
        let chip = FuncChip::from_name("test", &toplevel);
        let trace = chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = RowMajorMatrix::new(
            [
                // default case:
                //   nonce, input, output, last nonce, last count, 1/(a-2), 1/(a-3), 1/(a-4), last nonce, last count, two selectors
                0, 1, 1, 0, 1, 2013265920, 1006632960, 671088640, 0, 1,
                // branch case:
                //   nonce, input, output, last nonce, last count, (a-2)*(a-3), (a-2)*(a-3)*(a-4), dummy, two selectors
                1, 2, 1, 0, 1, 0, 0, 0, 1, 0,
                2, 3, 1, 0, 1, 0, 0, 0, 1, 0,
                3, 4, 1, 0, 1, 2, 0, 0, 1, 0,
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            chip.width(),
        );
        assert_eq!(trace, expected_trace);
        let _ = debug_constraints_collecting_queries(&chip, &[], None, &trace);
    }

    #[test]
    fn lair_range_test() {
        let func_range = func!(
        fn range_test(x: [3]): [0] {
            range_u8!(x);
            return ()
        });
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[func_range]);
        let range_chip = FuncChip::from_name("range_test", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let f = F::from_canonical_usize;
        let args = &[f(100), f(12), f(64)];
        toplevel
            .execute_by_name("range_test", args, &mut queries, None)
            .unwrap();
        let trace = range_chip.generate_trace(&Shard::new(&queries));
        #[rustfmt::skip]
        let expected_trace = [
            0, 100, 12, 64, 0, 1, 0, 0, 1, 0, 0, 1, 1,
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
        let queries = debug_constraints_collecting_queries(&range_chip, &[], None, &trace);
        // function return provide
        assert!(queries
            .memoset
            .contains_key(&vec![f(0), f(0), f(100), f(12), f(64)]));
        // byte range checks for 100, 12, 64
        assert!(queries
            .memoset
            .contains_key(&vec![f(3), f(1), f(100), f(12)]));
        assert!(queries.memoset.contains_key(&vec![f(3), f(1), f(64), f(0)]));
    }
}
