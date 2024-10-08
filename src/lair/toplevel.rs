use either::Either;
use p3_field::Field;
use rustc_hash::FxHashMap;

use super::{bytecode::*, chipset::Chipset, expr::*, map::Map, FxIndexMap, List, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Toplevel<F, C1: Chipset<F>, C2: Chipset<F>> {
    /// Lair functions reachable by the `Call` operator
    pub(crate) func_map: FxIndexMap<Name, Func<F>>,
    /// Extern chips reachable by the `ExternCall` operator. The two different
    /// chipset types can be used to encode native and custom chips.
    pub(crate) chip_map: FxIndexMap<Name, Either<C1, C2>>,
}

pub(crate) struct FuncInfo {
    input_size: usize,
    output_size: usize,
    partial: bool,
}

impl<F: Field + Ord, C1: Chipset<F>, C2: Chipset<F>> Toplevel<F, C1, C2> {
    pub fn new(funcs_exprs: &[FuncE<F>], chip_map: FxIndexMap<Name, Either<C1, C2>>) -> Self {
        let info_map = funcs_exprs
            .iter()
            .map(|func| {
                let func_info = FuncInfo {
                    input_size: func.input_params.total_size(),
                    output_size: func.output_size,
                    partial: func.partial,
                };
                (func.name, func_info)
            })
            .collect();
        let func_map = funcs_exprs
            .iter()
            .enumerate()
            .map(|(i, func)| (func.name, func.check_and_link(i, &info_map, &chip_map)))
            .collect();
        Toplevel { func_map, chip_map }
    }

    #[inline]
    pub fn new_pure(funcs_exprs: &[FuncE<F>]) -> Self {
        Toplevel::new(funcs_exprs, FxIndexMap::default())
    }
}

impl<F, C1: Chipset<F>, C2: Chipset<F>> Toplevel<F, C1, C2> {
    #[inline]
    pub fn func_by_index(&self, i: usize) -> &Func<F> {
        self.func_map.get_index(i).expect("Index out of bounds").1
    }

    #[inline]
    pub fn func_by_name(&self, name: &'static str) -> &Func<F> {
        self.func_map.get(&Name(name)).expect("Func not found")
    }

    #[inline]
    pub fn num_funcs(&self) -> usize {
        self.func_map.len()
    }

    #[inline]
    pub fn chip_by_index(&self, i: usize) -> &Either<C1, C2> {
        self.chip_map.get_index(i).expect("Index out of bounds").1
    }
}

/// A map from `Var` to its compiled indices and block identifier
type BindMap = FxHashMap<Var, (List<usize>, usize)>;

/// A map that tells whether a `Var`, from a certain block, has been used or not
type UsedMap = FxHashMap<(Var, usize), bool>;

#[inline]
fn bind_new<C1, C2>(var: &Var, ctx: &mut CheckCtx<'_, C1, C2>) {
    let idxs = (0..var.size).map(|_| ctx.new_var()).collect();
    bind(var, idxs, ctx);
}

#[inline]
fn bind<C1, C2>(var: &Var, idxs: List<usize>, ctx: &mut CheckCtx<'_, C1, C2>) {
    ctx.bind_map.insert(*var, (idxs, ctx.block_ident));
    if let Some(used) = ctx.used_map.insert((*var, ctx.block_ident), false) {
        let ch = var.name.chars().next().expect("Empty var name");
        assert!(
            used || ch == '_',
            "Variable {var} not used. If intended, please prefix it with \"_\""
        );
    }
}

#[inline]
fn use_var<'a, C1, C2>(var: &Var, ctx: &'a mut CheckCtx<'_, C1, C2>) -> &'a [usize] {
    let (idxs, block_idx) = ctx
        .bind_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    let used = ctx
        .used_map
        .get_mut(&(*var, *block_idx))
        .expect("Data should have been inserted when binding");
    *used = true;
    idxs
}

struct CheckCtx<'a, C1, C2> {
    var_index: usize,
    block_ident: usize,
    return_ident: usize,
    return_idents: Vec<usize>,
    return_size: usize,
    partial: bool,
    bind_map: BindMap,
    used_map: UsedMap,
    info_map: &'a FxIndexMap<Name, FuncInfo>,
    chip_map: &'a FxIndexMap<Name, Either<C1, C2>>,
}

impl<'a, C1, C2> CheckCtx<'a, C1, C2> {
    fn save_bind_state(&mut self) -> (usize, BindMap) {
        (self.var_index, self.bind_map.clone())
    }

    fn restore_bind_state(&mut self, (index, bind_map): (usize, BindMap)) {
        self.var_index = index;
        self.bind_map = bind_map;
    }

    fn new_var(&mut self) -> usize {
        let var = self.var_index;
        self.var_index += 1;
        var
    }
}

impl<F: Field + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func`
    /// by replacing names with indices
    fn check_and_link<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        func_index: usize,
        info_map: &FxIndexMap<Name, FuncInfo>,
        chip_map: &FxIndexMap<Name, Either<C1, C2>>,
    ) -> Func<F> {
        let ctx = &mut CheckCtx {
            var_index: 0,
            block_ident: 0,
            return_ident: 0,
            return_idents: vec![],
            return_size: self.output_size,
            partial: self.partial,
            bind_map: FxHashMap::default(),
            used_map: FxHashMap::default(),
            info_map,
            chip_map,
        };
        self.input_params.iter().for_each(|var| {
            bind_new(var, ctx);
        });
        let body = self.body.check_and_link(ctx);
        for ((var, _), used) in ctx.used_map.iter() {
            let ch = var.name.chars().next().expect("Empty var name");
            assert!(
                *used || ch == '_',
                "Variable {var} not used. If intended, please prefix it with \"_\""
            );
        }
        Func {
            name: self.name,
            invertible: self.invertible,
            partial: self.partial,
            index: func_index,
            body,
            input_size: self.input_params.total_size(),
            output_size: self.output_size,
        }
    }
}

impl<F: Field + Ord> BlockE<F> {
    fn check_and_link_with_ops<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        mut ops: Vec<Op<F>>,
        ctx: &mut CheckCtx<'_, C1, C2>,
    ) -> Block<F> {
        self.ops
            .iter()
            .for_each(|op| op.check_and_link(&mut ops, ctx));
        let ops = ops.into();
        let saved_return_idents = std::mem::take(&mut ctx.return_idents);
        let ctrl = self.ctrl.check_and_link(ctx);
        let block_return_idents = std::mem::take(&mut ctx.return_idents);
        assert!(
            !block_return_idents.is_empty(),
            "A block must have at least one return ident"
        );
        ctx.return_idents = saved_return_idents;
        ctx.return_idents.extend(&block_return_idents);
        Block {
            ops,
            ctrl,
            return_idents: block_return_idents.into(),
        }
    }

    fn check_and_link<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ctx: &mut CheckCtx<'_, C1, C2>,
    ) -> Block<F> {
        self.check_and_link_with_ops(Vec::new(), ctx)
    }
}

impl<F: Field + Ord> CtrlE<F> {
    fn check_and_link<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ctx: &mut CheckCtx<'_, C1, C2>,
    ) -> Ctrl<F> {
        match &self {
            CtrlE::Return(return_vars) => {
                let total_size = return_vars.total_size();
                assert_eq!(
                    total_size, ctx.return_size,
                    "Return size {} different from expected size of return {}",
                    total_size, ctx.return_size
                );
                let return_vec = return_vars
                    .iter()
                    .flat_map(|arg| use_var(arg, ctx).to_vec())
                    .collect();
                let ctrl = Ctrl::Return(ctx.return_ident, return_vec);
                ctx.return_idents.push(ctx.return_ident);
                ctx.return_ident += 1;
                ctrl
            }
            CtrlE::Match(t, cases) => {
                assert_eq!(t.size, 1);
                let var = use_var(t, ctx)[0];
                let mut vec = Vec::with_capacity(cases.branches.len());
                let mut unique_branches = Vec::new();
                for (fs, block) in cases.branches.iter() {
                    ctx.block_ident += 1;
                    let state = ctx.save_bind_state();
                    let mut ops = Vec::new();
                    // Collect all constants as vars
                    let fs_vars = push_const_array(fs, &mut ops, ctx);
                    // Assert that var is contained in the constants
                    ops.push(Op::Contains(fs_vars, var));
                    let block = block.check_and_link_with_ops(ops, ctx);
                    ctx.restore_bind_state(state);
                    fs.iter().for_each(|f| vec.push((*f, block.clone())));
                    unique_branches.push(block);
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    ctx.block_ident += 1;
                    let mut ops = Vec::new();
                    for (fs, _) in cases.branches.iter() {
                        for f in fs.iter() {
                            // Collect constant as var
                            ops.push(Op::Const(*f));
                            let f_var = ctx.new_var();
                            // Assert inequality of matched var
                            ops.push(Op::AssertNe([var].into(), [f_var].into()));
                        }
                    }
                    def.check_and_link_with_ops(ops, ctx).into()
                });
                let cases = Cases { branches, default };
                Ctrl::Choose(var, cases, unique_branches.into())
            }
            CtrlE::MatchMany(t, cases) => {
                let size = t.size;
                let vars: List<_> = use_var(t, ctx).into();
                let mut vec = Vec::with_capacity(cases.branches.len());
                for (fs, block) in cases.branches.iter() {
                    assert_eq!(fs.len(), size, "Pattern must have size {size}");
                    ctx.block_ident += 1;
                    let state = ctx.save_bind_state();
                    let mut ops = Vec::new();
                    // Collect all constants as vars
                    let fs_vars = push_const_array(fs, &mut ops, ctx);
                    // Assert equality of matched vars
                    ops.push(Op::AssertEq(vars.clone(), fs_vars, None));
                    let block = block.check_and_link_with_ops(ops, ctx);
                    ctx.restore_bind_state(state);
                    vec.push((fs.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    ctx.block_ident += 1;
                    let mut ops = Vec::new();
                    for (fs, _) in cases.branches.iter() {
                        // Collect all constants as vars
                        let fs_vars = push_const_array(fs, &mut ops, ctx);
                        // Assert inequality of matched vars
                        ops.push(Op::AssertNe(vars.clone(), fs_vars));
                    }
                    def.check_and_link_with_ops(ops, ctx).into()
                });
                let cases = Cases { branches, default };
                Ctrl::ChooseMany(vars, cases)
            }
            CtrlE::If(b, true_block, false_block) => {
                let size = b.size;
                let vars: List<_> = use_var(b, ctx).into();

                let state = ctx.save_bind_state();
                ctx.block_ident += 1;
                let mut ops = Vec::new();
                ops.push(Op::Const(F::zero()));
                let zero = ctx.new_var();
                let zeros = (0..size).map(|_| zero).collect();
                ops.push(Op::AssertNe(vars.clone(), zeros));
                let true_block = true_block.check_and_link_with_ops(ops, ctx);
                ctx.restore_bind_state(state);

                ctx.block_ident += 1;
                let mut ops = Vec::new();
                ops.push(Op::Const(F::zero()));
                let zero = ctx.new_var();
                let zeros = (0..size).map(|_| zero).collect();
                ops.push(Op::AssertEq(vars.clone(), zeros, None));
                let false_block = false_block.check_and_link_with_ops(ops, ctx);

                if size == 1 {
                    let branches = Map::from_vec(vec![(F::zero(), false_block.clone())]);
                    let cases = Cases {
                        branches,
                        default: Some(true_block.into()),
                    };
                    Ctrl::Choose(vars[0], cases, [false_block].into())
                } else {
                    let arr = vec![F::zero(); b.size];
                    let branches = Map::from_vec(vec![(arr.into(), false_block)]);
                    let cases = Cases {
                        branches,
                        default: Some(true_block.into()),
                    };
                    Ctrl::ChooseMany(vars, cases)
                }
            }
        }
    }
}

impl<F: Field + Ord> OpE<F> {
    fn check_and_link<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ops: &mut Vec<Op<F>>,
        ctx: &mut CheckCtx<'_, C1, C2>,
    ) {
        match self {
            OpE::AssertNe(a, b) => {
                assert_eq!(a.size, b.size);
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx).into();
                ops.push(Op::AssertNe(a, b));
            }
            OpE::AssertEq(a, b, fmt) => {
                assert_eq!(a.size, b.size);
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx).into();
                ops.push(Op::AssertEq(a, b, *fmt));
            }
            OpE::Contains(a, b) => {
                assert_eq!(b.size, 1);
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx)[0];
                ops.push(Op::Contains(a, b));
            }
            OpE::Const(tgt, f) => {
                assert_eq!(tgt.size, 1);
                ops.push(Op::Const(*f));
                bind_new(tgt, ctx);
            }
            OpE::Array(tgt, fs) => {
                assert_eq!(tgt.size, fs.len());
                for f in fs.iter() {
                    ops.push(Op::Const(*f));
                }
                bind_new(tgt, ctx);
            }
            OpE::Add(tgt, a, b) => {
                assert_eq!(a.size, b.size);
                assert_eq!(a.size, tgt.size);
                let a = use_var(a, ctx).to_vec();
                let b = use_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Add(*a, *b));
                }
                bind_new(tgt, ctx);
            }
            OpE::Mul(tgt, a, b) => {
                assert_eq!(a.size, b.size);
                assert_eq!(a.size, tgt.size);
                let a = use_var(a, ctx).to_vec();
                let b = use_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Mul(*a, *b));
                }
                bind_new(tgt, ctx);
            }
            OpE::Sub(tgt, a, b) => {
                assert_eq!(a.size, b.size);
                assert_eq!(a.size, tgt.size);
                let a = use_var(a, ctx).to_vec();
                let b = use_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Sub(*a, *b));
                }
                bind_new(tgt, ctx);
            }
            OpE::Div(tgt, a, b) => {
                assert_eq!(a.size, b.size);
                assert_eq!(a.size, tgt.size);
                let b = use_var(b, ctx);
                for b in b.iter() {
                    ops.push(Op::Inv(*b));
                }
                let a = use_var(a, ctx).to_vec();
                for a in a.iter() {
                    ops.push(Op::Mul(*a, ctx.new_var()));
                }
                bind_new(tgt, ctx);
            }
            OpE::Inv(tgt, a) => {
                assert_eq!(a.size, tgt.size);
                let a = use_var(a, ctx);
                for a in a.iter() {
                    ops.push(Op::Inv(*a));
                }
                bind_new(tgt, ctx);
            }
            OpE::Not(tgt, a) => {
                assert_eq!(tgt.size, 1);
                assert_eq!(a.size, 1);
                let a = use_var(a, ctx)[0];
                ops.push(Op::Not(a));
                bind_new(tgt, ctx);
            }
            OpE::Eq(tgt, a, b) => {
                assert_eq!(tgt.size, 1);
                assert_eq!(a.size, 1);
                assert_eq!(b.size, 1);
                let a = use_var(a, ctx)[0];
                let b = use_var(b, ctx)[0];
                ops.push(Op::Sub(a, b));
                ops.push(Op::Not(ctx.new_var()));
                bind_new(tgt, ctx);
            }
            OpE::Call(out, name, inp) => {
                let name_idx = ctx
                    .info_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let FuncInfo {
                    input_size,
                    output_size,
                    partial,
                } = *ctx.info_map.get_index(name_idx).unwrap().1;
                if partial {
                    assert!(ctx.partial);
                }
                assert_eq!(inp.total_size(), input_size);
                assert_eq!(out.total_size(), output_size);
                let inp = inp.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::Call(name_idx, inp));
                out.iter().for_each(|t| bind_new(t, ctx));
            }
            OpE::PreImg(out, name, inp, fmt) => {
                let name_idx = ctx
                    .info_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let FuncInfo {
                    input_size,
                    output_size,
                    partial,
                } = *ctx.info_map.get_index(name_idx).unwrap().1;
                if partial {
                    assert!(ctx.partial);
                }
                assert_eq!(out.total_size(), input_size);
                assert_eq!(inp.total_size(), output_size);
                let inp = inp.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::PreImg(name_idx, inp, *fmt));
                out.iter().for_each(|t| bind_new(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                assert_eq!(ptr.size, 1);
                let vals = vals.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::Store(vals));
                bind_new(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                assert_eq!(ptr.size, 1);
                let ptr = use_var(ptr, ctx)[0];
                ops.push(Op::Load(vals.total_size(), ptr));
                vals.iter().for_each(|val| bind_new(val, ctx));
            }
            OpE::Slice(pats, args) => {
                assert_eq!(pats.total_size(), args.total_size());
                let args: List<_> = args.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                let mut i = 0;
                for pat in pats.as_slice() {
                    let idxs = args[i..i + pat.size].into();
                    bind(pat, idxs, ctx);
                    i += pat.size;
                }
            }
            OpE::ExternCall(out, name, inp) => {
                let name_idx = ctx
                    .chip_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown extern chip {name}"));
                let (_, chip) = ctx.chip_map.get_index(name_idx).unwrap();
                assert_eq!(inp.total_size(), chip.input_size());
                assert_eq!(out.total_size(), chip.output_size());
                let inp = inp.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::ExternCall(name_idx, inp));
                out.iter().for_each(|t| bind_new(t, ctx));
            }
            OpE::Emit(vars) => {
                let vars = vars.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::Emit(vars));
            }
            OpE::RangeU8(xs) => {
                let xs = xs.iter().flat_map(|x| use_var(x, ctx).to_vec()).collect();
                ops.push(Op::RangeU8(xs));
            }
            OpE::Breakpoint => ops.push(Op::Breakpoint),
            OpE::Debug(s) => ops.push(Op::Debug(s)),
        }
    }
}

fn push_const_array<F: Field + Ord, C1, C2>(
    fs: &[F],
    ops: &mut Vec<Op<F>>,
    ctx: &mut CheckCtx<'_, C1, C2>,
) -> List<usize> {
    fs.iter()
        .map(|f| {
            ops.push(Op::Const(*f));
            ctx.new_var()
        })
        .collect()
}
