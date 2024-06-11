use std::fmt::Debug;

use p3_air::{Air, AirBuilder};
use p3_field::{AbstractField, Field};
use p3_matrix::Matrix;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chip::{ColumnLayout, FuncChip, LayoutSizes},
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

pub type ColumnSlice<'a, T> = ColumnLayout<&'a [T]>;
impl<'a, T> ColumnSlice<'a, T> {
    pub fn from_slice(slice: &'a [T], layout_sizes: LayoutSizes) -> Self {
        let (input, slice) = slice.split_at(layout_sizes.input);
        let (output, slice) = slice.split_at(layout_sizes.output);
        let (aux, slice) = slice.split_at(layout_sizes.aux);
        let (sel, slice) = slice.split_at(layout_sizes.sel);
        assert!(slice.is_empty());
        Self {
            input,
            output,
            aux,
            sel,
        }
    }

    pub fn next_input(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.input[index.input];
        index.input += 1;
        t
    }

    pub fn next_output(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.output[index.output];
        index.output += 1;
        t
    }

    pub fn next_aux(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.aux[index.aux];
        index.aux += 1;
        t
    }
}

impl<'a, AB> Air<AB> for FuncChip<'a, AB::F>
where
    AB: AirBuilder,
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
    fn eval<AB>(&self, builder: &mut AB, toplevel: &Toplevel<F>, layout_sizes: LayoutSizes)
    where
        AB: AirBuilder<F = F>,
        <AB as AirBuilder>::Var: Debug,
    {
        let main = builder.main();
        let slice = main.row_slice(0);
        let local = ColumnSlice::from_slice(&slice, layout_sizes);

        let index = &mut ColumnIndex::default();
        let map = &mut vec![];
        for _ in 0..self.input_size {
            let i = *local.next_input(index);
            map.push(Val::Expr(i.into()));
        }

        let mult = *local.next_aux(index);
        let toplevel_sel = self.body.eval(builder, local, index, map, toplevel);
        builder.assert_bool(toplevel_sel.clone());
        builder.when_ne(toplevel_sel, F::one()).assert_zero(mult);
    }
}

impl<F: Field> Block<F> {
    fn eval<AB>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) -> AB::Expr
    where
        AB: AirBuilder<F = F>,
        <AB as AirBuilder>::Var: Debug,
    {
        let mut constraints = vec![];
        self.ops
            .iter()
            .for_each(|op| op.eval(local, &mut constraints, index, map, toplevel));
        let sel = self.ctrl.eval(builder, local, index, map, toplevel);
        for expr in constraints {
            builder.when(sel.clone()).assert_zero(expr);
        }
        sel
    }
}

impl<F: Field> Op<F> {
    fn eval<AB>(
        &self,
        local: ColumnSlice<'_, AB::Var>,
        constraints: &mut Vec<AB::Expr>,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) where
        AB: AirBuilder<F = F>,
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
                    constraints.push(a.to_expr() * b.to_expr() - c);
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
                    constraints.push(a.to_expr() * c - F::one());
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
                    constraints.push(a.to_expr() * x);
                    constraints.push(a.to_expr() * d + x - F::one());
                    Val::Expr(x.into())
                };
                map.push(x);
            }
            // Call, PreImg, Store, Load TODO: lookup argument
            Op::Call(idx, _) => {
                let func = toplevel.get_by_index(*idx).unwrap();
                for _ in 0..func.output_size {
                    let o = *local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                }
            }
            Op::PreImg(idx, _) => {
                let func = toplevel.get_by_index(*idx).unwrap();
                for _ in 0..func.input_size {
                    let o = *local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                }
            }
            Op::Store(_) => {
                let ptr = *local.next_aux(index);
                map.push(Val::Expr(ptr.into()));
            }
            Op::Load(len, _) => {
                for _ in 0..*len {
                    let o = *local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                }
            }
            Op::Debug(..) => (),
        }
    }
}

impl<F: Field> Ctrl<F> {
    fn eval<AB>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) -> AB::Expr
    where
        AB: AirBuilder<F = F>,
        <AB as AirBuilder>::Var: Debug,
    {
        match self {
            Ctrl::Match(v, cases) => {
                let map_len = map.len();
                let init_state = index.save();
                let v = map[*v].to_expr();
                let mut sels = Vec::with_capacity(cases.size());

                for (f, branch) in cases.branches.iter() {
                    let sel = branch.eval(builder, local, index, map, toplevel);
                    builder.when(sel.clone()).assert_eq(v.clone(), *f);
                    sels.push(sel);
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                if let Some(branch) = &cases.default {
                    let invs = (0..cases.branches.size())
                        .map(|_| *local.next_aux(index))
                        .collect::<Vec<_>>();
                    let sel = branch.eval(builder, local, index, map, toplevel);
                    for ((f, _), inv) in cases.branches.iter().zip(invs.into_iter()) {
                        builder.when(sel.clone()).assert_one(inv * (v.clone() - *f));
                    }
                    sels.push(sel);
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                sels.into_iter()
                    .fold(F::zero().into(), |acc, sel| acc + sel)
            }
            Ctrl::MatchMany(vars, cases) => {
                let map_len = map.len();
                let init_state = index.save();
                let vals: Vec<_> = vars.iter().map(|&var| map[var].to_expr()).collect();
                let mut sels = Vec::with_capacity(cases.size());

                for (fs, branch) in cases.branches.iter() {
                    let sel = branch.eval(builder, local, index, map, toplevel);
                    for (v, f) in vals.iter().zip(fs.iter()) {
                        builder.when(sel.clone()).assert_eq(v.clone(), *f)
                    }
                    sels.push(sel);
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                if let Some(branch) = &cases.default {
                    let wit: Vec<Vec<_>> = (0..cases.branches.size())
                        .map(|_| (0..vars.len()).map(|_| *local.next_aux(index)).collect())
                        .collect();
                    let sel = branch.eval(builder, local, index, map, toplevel);
                    for (coeffs, (fs, _)) in wit.into_iter().zip(cases.branches.iter()) {
                        let diffs = vals
                            .iter()
                            .zip(fs.iter())
                            .map(|(v, f)| v.clone() - *f)
                            .collect();
                        constrain_inequality_witness(sel.clone(), coeffs, diffs, builder);
                    }
                    sels.push(sel);
                    map.truncate(map_len);
                    index.restore(init_state);
                }

                sels.into_iter()
                    .fold(F::zero().into(), |acc, sel| acc + sel)
            }
            Ctrl::If(b, t, f) => {
                let map_len = map.len();
                let init_state = index.save();
                let b = map[*b].to_expr();

                let inv = *local.next_aux(index);
                let t_sel = t.eval(builder, local, index, map, toplevel);
                builder.when(t_sel.clone()).assert_one(inv * b.clone());
                map.truncate(map_len);
                index.restore(init_state);

                let f_sel = f.eval(builder, local, index, map, toplevel);
                builder.when(f_sel.clone()).assert_zero(b);
                map.truncate(map_len);
                index.restore(init_state);

                t_sel + f_sel
            }
            Ctrl::IfMany(vars, t, f) => {
                let map_len = map.len();
                let init_state = index.save();

                let coeffs = vars.iter().map(|_| *local.next_aux(index)).collect();
                let vals = vars.iter().map(|&v| map[v].to_expr()).collect();
                let t_sel = t.eval(builder, local, index, map, toplevel);
                constrain_inequality_witness(t_sel.clone(), coeffs, vals, builder);
                map.truncate(map_len);
                index.restore(init_state);

                let f_sel = f.eval(builder, local, index, map, toplevel);
                for var in vars.iter() {
                    let b = map[*var].to_expr();
                    builder.when(f_sel.clone()).assert_zero(b);
                }
                map.truncate(map_len);
                index.restore(init_state);

                t_sel + f_sel
            }
            Ctrl::Return(ident, vs) => {
                let sel = local.sel[*ident];
                for v in vs.iter() {
                    let v = map[*v].to_expr();
                    let o = *local.next_output(index);
                    builder.when(sel).assert_eq(v, o);
                }
                sel.into()
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
    let one: AB::Expr = AB::F::one().into();
    let acc = coeffs
        .into_iter()
        .zip(vals)
        .map(|(coeff, val)| coeff * val)
        .fold(one, |acc, expr| acc - expr);
    builder.when(sel).assert_zero(acc);
}

#[cfg(test)]
mod tests {
    use crate::{air::debug::debug_constraints_collecting_queries, func};
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use crate::lair::{demo_toplevel, execute::QueryRecord, field_from_u32};

    use super::*;

    type F = BabyBear;

    #[test]
    fn lair_constraint_test() {
        let toplevel = demo_toplevel();
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let factorial_width = factorial_chip.width();
        let factorial_trace = RowMajorMatrix::new(
            [
                // in order: n, output, mult, 1/n, fact(n-1), n*fact(n-1), and selectors
                0, 1, 1, 0, 0, 0, 0, 1, //
                1, 1, 1, 1, 1, 1, 1, 0, //
                2, 2, 1, 1006632961, 1, 2, 1, 0, //
                3, 6, 1, 1342177281, 2, 6, 1, 0, //
                4, 24, 1, 1509949441, 6, 24, 1, 0, //
                5, 120, 1, 1610612737, 24, 120, 1, 0, //
                // dummy
                0, 0, 0, 0, 0, 0, 0, 0, //
                0, 0, 0, 0, 0, 0, 0, 0, //
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
                // in order: n, output, mult, 1/n, 1/(n-1), fib(n-1), fib(n-2), and selectors
                0, 1, 1, 0, 0, 0, 0, 1, 0, 0, //
                1, 1, 2, 0, 0, 0, 0, 0, 1, 0, //
                2, 2, 2, 1006632961, 1, 1, 1, 0, 0, 1, //
                3, 3, 2, 1342177281, 1006632961, 2, 1, 0, 0, 1, //
                4, 5, 2, 1509949441, 1342177281, 3, 2, 0, 0, 1, //
                5, 8, 2, 1610612737, 1509949441, 5, 3, 0, 0, 1, //
                6, 13, 1, 1677721601, 1610612737, 8, 5, 0, 0, 1, //
                7, 21, 1, 862828252, 1677721601, 13, 8, 0, 0, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            fib_width,
        );

        let _ = debug_constraints_collecting_queries(&factorial_chip, &[], &factorial_trace);
        let _ = debug_constraints_collecting_queries(&fib_chip, &[], &fib_trace);
    }

    #[test]
    fn lair_long_constraint_test() {
        let toplevel = demo_toplevel::<F>();
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let args = [field_from_u32(20000)].into();
        let queries = &mut QueryRecord::new(&toplevel);
        fib_chip.execute_iter(args, queries);
        let fib_trace = fib_chip.generate_trace_parallel(queries);

        let _ = debug_constraints_collecting_queries(&fib_chip, &[], &fib_trace);
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
        let toplevel = Toplevel::<F>::new(&[eq_func, not_func]);
        let eq_chip = FuncChip::from_name("eq", &toplevel);
        let not_chip = FuncChip::from_name("not", &toplevel);

        let queries = &mut QueryRecord::new(&toplevel);
        let args = [field_from_u32(4)].into();
        not_chip.execute_iter(args, queries);
        let args = [field_from_u32(8)].into();
        not_chip.execute_iter(args, queries);
        let args = [field_from_u32(0)].into();
        not_chip.execute_iter(args, queries);
        let args = [field_from_u32(1)].into();
        not_chip.execute_iter(args, queries);

        let not_width = not_chip.width();
        let not_trace = RowMajorMatrix::new(
            [
                0, 1, 1, 0, 1, 1, //
                1, 0, 1, 1, 0, 1, //
                4, 0, 1, 1509949441, 0, 1, //
                8, 0, 1, 1761607681, 0, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            not_width,
        );

        let args = [field_from_u32(4), field_from_u32(2)].into();
        eq_chip.execute_iter(args, queries);
        let args = [field_from_u32(4), field_from_u32(4)].into();
        eq_chip.execute_iter(args, queries);
        let args = [field_from_u32(0), field_from_u32(3)].into();
        eq_chip.execute_iter(args, queries);
        let args = [field_from_u32(0), field_from_u32(0)].into();
        eq_chip.execute_iter(args, queries);

        let eq_width = eq_chip.width();
        let eq_trace = RowMajorMatrix::new(
            [
                0, 0, 1, 1, 0, 1, 1, //
                0, 3, 0, 1, 671088640, 0, 1, //
                4, 2, 0, 1, 1006632961, 0, 1, //
                4, 4, 1, 1, 0, 1, 1, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            eq_width,
        );

        let _ = debug_constraints_collecting_queries(&not_chip, &[], &not_trace);
        let _ = debug_constraints_collecting_queries(&eq_chip, &[], &eq_trace);
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
        let toplevel = Toplevel::<F>::new(&[if_many_func]);
        let if_many_chip = FuncChip::from_name("if_many", &toplevel);

        let queries = &mut QueryRecord::new(&toplevel);
        let f = field_from_u32;
        let args = [f(0), f(0), f(0), f(0)].into();
        if_many_chip.execute_iter(args, queries);
        let args = [f(1), f(3), f(8), f(2)].into();
        if_many_chip.execute_iter(args, queries);
        let args = [f(0), f(0), f(4), f(1)].into();
        if_many_chip.execute_iter(args, queries);
        let args = [f(0), f(0), f(0), f(9)].into();
        if_many_chip.execute_iter(args, queries);

        let if_many_trace = if_many_chip.generate_trace_parallel(queries);

        let if_many_width = if_many_chip.width();
        let expected_trace = RowMajorMatrix::new(
            [
                // 4 inputs, 1 output, mult, 4 coeffs, 2 selectors
                0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, //
                1, 3, 8, 2, 1, 1, 1, 0, 0, 0, 1, 0, //
                0, 0, 4, 1, 1, 1, 0, 0, 1509949441, 0, 1, 0, //
                0, 0, 0, 9, 1, 1, 0, 0, 0, 447392427, 1, 0, //
            ]
            .into_iter()
            .map(F::from_canonical_u32)
            .collect::<Vec<_>>(),
            if_many_width,
        );
        assert_eq!(if_many_trace, expected_trace);

        let _ = debug_constraints_collecting_queries(&if_many_chip, &[], &expected_trace);
    }
}
