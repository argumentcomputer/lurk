use p3_air::{Air, AirBuilder};
use p3_field::{AbstractField, Field};
use p3_matrix::Matrix;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
    trace::{ColumnLayout, FuncChip, Width},
};

pub type ColumnSlice<'a, T> = ColumnLayout<&'a [T]>;
pub type ColumnIndex = ColumnLayout<usize>;

impl<'a, T> ColumnSlice<'a, T> {
    pub fn from_slice(slice: &'a [T], width: Width) -> Self {
        assert_eq!(
            slice.len(),
            width.input + width.output + width.aux + width.sel
        );
        let mut from = 0;
        let mut to = width.input;
        let input = &slice[from..to];
        from += width.input;
        to += width.output;
        let output = &slice[from..to];
        from += width.output;
        to += width.aux;
        let aux = &slice[from..to];
        from += width.aux;
        to += width.sel;
        let sel = &slice[from..to];
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

    pub fn next_sel(&self, index: &mut ColumnIndex) -> &T {
        let t = &self.sel[index.sel];
        index.sel += 1;
        t
    }
}

impl<'a, AB: AirBuilder> Air<AB> for FuncChip<'a, AB::F> {
    fn eval(&self, builder: &mut AB) {
        self.func.eval(builder, self.toplevel, self.width)
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

impl<F: AbstractField + Field> Func<F> {
    fn eval<AB>(&self, builder: &mut AB, toplevel: &Toplevel<F>, width: Width)
    where
        AB: AirBuilder<F = F>,
    {
        let main = builder.main();
        let slice = main.row_slice(0);
        let local = ColumnSlice::from_slice(&slice, width);

        let index = &mut ColumnIndex::default();
        let map = &mut vec![];
        for _ in 0..self.input_size {
            let i = *local.next_input(index);
            map.push(Val::Expr(i.into()));
        }

        let mult = *local.next_aux(index);
        let not_dummy = *local.next_sel(index);
        builder.assert_bool(not_dummy);
        builder.when_ne(not_dummy, AB::F::one()).assert_zero(mult);

        self.body
            .eval(builder, local, not_dummy, index, map, toplevel)
    }
}

impl<F: AbstractField + Field> Block<F> {
    fn eval<AB>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        not_dummy: AB::Var,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) where
        AB: AirBuilder<F = F>,
    {
        self.ops
            .iter()
            .for_each(|op| op.eval(builder, local, not_dummy, index, map, toplevel));

        self.ctrl
            .eval(builder, local, not_dummy, index, map, toplevel);
    }
}

impl<F: AbstractField + Field> Op<F> {
    fn eval<AB>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        not_dummy: AB::Var,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) where
        AB: AirBuilder<F = F>,
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
                    let c = local.next_aux(index);
                    builder
                        .when(not_dummy)
                        .assert_eq(a.to_expr() * b.to_expr(), *c);
                    Val::Expr((*c).into())
                };
                map.push(c);
            }
            Op::Inv(a) => {
                let a = &map[*a];
                let c = if let Val::Const(a) = a {
                    Val::Const(a.inverse())
                } else {
                    let c = local.next_aux(index);
                    builder.when(not_dummy).assert_one(a.to_expr() * *c);
                    Val::Expr((*c).into())
                };
                map.push(c);
            }
            Op::Pol(..) => {
                todo!()
            }
            Op::Call(idx, _) => {
                let func = toplevel.get_by_index(*idx as usize).unwrap();
                for _ in 0..func.output_size {
                    let o = *local.next_aux(index);
                    map.push(Val::Expr(o.into()));
                }
                // TODO: lookup argument
            }
        }
    }
}

impl<F: AbstractField + Field> Ctrl<F> {
    fn eval<AB>(
        &self,
        builder: &mut AB,
        local: ColumnSlice<'_, AB::Var>,
        not_dummy: AB::Var,
        index: &mut ColumnIndex,
        map: &mut Vec<Val<AB>>,
        toplevel: &Toplevel<F>,
    ) where
        AB: AirBuilder<F = F>,
    {
        match self {
            Ctrl::Match(v, cases) => {
                let map_len = map.len();
                let v = map[*v].to_expr();

                let mut sels = vec![];
                for _ in 0..cases.size() {
                    let not_dummy = *local.next_sel(index);
                    sels.push(not_dummy);
                }

                for ((f, branch), sel) in cases.branches.iter().zip(sels.iter()) {
                    let sel = *sel;
                    let index = &mut index.clone();
                    builder.assert_bool(sel);
                    builder.when(sel).assert_eq(v.clone(), *f);
                    branch.eval(builder, local, sel, index, map, toplevel);
                    map.truncate(map_len);
                }

                if let Some(branch) = &cases.default {
                    let index = &mut index.clone();
                    let sel = *sels.last().unwrap();
                    builder.assert_bool(sel);
                    for (f, _) in cases.branches.iter() {
                        let inv = *local.next_aux(index);
                        builder.when(sel).assert_one(inv * (v.clone() - *f));
                    }
                    branch.eval(builder, local, not_dummy, index, map, toplevel);
                    map.truncate(map_len);
                }

                let dummy: AB::Expr = -not_dummy.into() + AB::F::one();
                let sum = sels.into_iter().fold(dummy, |acc, sel| acc + sel);
                builder.assert_one(sum);
            }
            Ctrl::If(b, t, f) => {
                let map_len = map.len();
                let b = map[*b].to_expr();

                let t_index = &mut index.clone();
                let t_not_dummy = *local.next_sel(t_index);
                builder.assert_bool(t_not_dummy);
                builder.when(t_not_dummy).assert_zero(b.clone());
                t.eval(builder, local, t_not_dummy, t_index, map, toplevel);
                map.truncate(map_len);

                let f_index = &mut index.clone();
                let f_not_dummy = *local.next_sel(f_index);
                builder.assert_bool(t_not_dummy);
                let inv = *local.next_aux(f_index);
                builder.when(f_not_dummy).assert_one(inv * b);
                f.eval(builder, local, f_not_dummy, f_index, map, toplevel);
                map.truncate(map_len);

                builder.assert_one(t_not_dummy + f_not_dummy + AB::F::one() - not_dummy);
            }
            Ctrl::Return(vs) => {
                for v in vs.iter() {
                    let v = map[*v].to_expr();
                    let o = *local.next_output(index);
                    builder.when(not_dummy).assert_eq(v, o);
                }
            }
        }
    }
}
