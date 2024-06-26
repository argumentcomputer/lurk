use rustc_hash::FxHashMap;

use super::{bytecode::*, expr::*, hasher::Hasher, map::Map, List, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Toplevel<F, H: Hasher<F>> {
    pub(crate) map: Map<Name, Func<F>>,
    pub(crate) hasher: H,
}

pub(crate) struct FuncInfo {
    input_size: usize,
    output_size: usize,
}

impl<F: Clone + Ord, H: Hasher<F>> Toplevel<F, H> {
    pub fn new(funcs: &[FuncE<F>]) -> Self {
        let ordered_funcs = Map::from_vec(funcs.iter().map(|func| (func.name, func)).collect());
        let info_vec = ordered_funcs
            .iter()
            .map(|(name, func)| {
                let func_info = FuncInfo {
                    input_size: func.input_params.total_size(),
                    output_size: func.output_size,
                };
                (*name, func_info)
            })
            .collect();
        let hasher = H::default();
        let info_map = Map::from_vec_unsafe(info_vec);
        let map = Map::from_vec_unsafe(
            ordered_funcs
                .iter()
                .enumerate()
                .map(|(i, (name, func))| (*name, func.check_and_link(i, &info_map, &hasher)))
                .collect(),
        );
        Toplevel { map, hasher }
    }
}

impl<F, H: Hasher<F>> Toplevel<F, H> {
    #[inline]
    pub fn get_by_index(&self, i: usize) -> &Func<F> {
        self.map
            .get_index(i)
            .map(|(_, func)| func)
            .expect("Index out of bounds")
    }

    #[inline]
    pub fn get_by_name(&self, name: &'static str) -> &Func<F> {
        self.map.get(&Name(name)).expect("Func not found")
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.map.size()
    }
}

/// A map from `Var` to its compiled indices and block identifier
type BindMap = FxHashMap<Var, (List<usize>, usize)>;

/// A map that tells whether a `Var`, from a certain block, has been used or not
type UsedMap = FxHashMap<(Var, usize), bool>;

#[inline]
fn bind_new(var: &Var, ctx: &mut CheckCtx<'_>) {
    let idxs = (0..var.size).map(|_| ctx.new_var()).collect();
    bind(var, idxs, ctx);
}

#[inline]
fn bind(var: &Var, idxs: List<usize>, ctx: &mut CheckCtx<'_>) {
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
fn use_var<'a>(var: &Var, ctx: &'a mut CheckCtx<'_>) -> &'a [usize] {
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

struct CheckCtx<'a> {
    var_index: usize,
    block_ident: usize,
    call_ident: usize,
    return_ident: usize,
    return_idents: Vec<usize>,
    return_size: usize,
    bind_map: BindMap,
    used_map: UsedMap,
    info_map: &'a Map<Name, FuncInfo>,
}

impl<'a> CheckCtx<'a> {
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

impl<F: Clone + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func`
    /// by replacing names with indices
    fn check_and_link<H: Hasher<F>>(
        &self,
        func_index: usize,
        info_map: &Map<Name, FuncInfo>,
        hasher: &H,
    ) -> Func<F> {
        let ctx = &mut CheckCtx {
            var_index: 0,
            block_ident: 0,
            call_ident: 0,
            return_ident: 0,
            return_idents: vec![],
            return_size: self.output_size,
            bind_map: FxHashMap::default(),
            used_map: FxHashMap::default(),
            info_map,
        };
        self.input_params.iter().for_each(|var| {
            bind_new(var, ctx);
        });
        let body = self.body.check_and_link(ctx, hasher);
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
            index: func_index,
            body,
            input_size: self.input_params.total_size(),
            output_size: self.output_size,
        }
    }
}

impl<F: Clone + Ord> BlockE<F> {
    fn check_and_link<H: Hasher<F>>(&self, ctx: &mut CheckCtx<'_>, hasher: &H) -> Block<F> {
        let mut ops = Vec::new();
        self.ops
            .iter()
            .for_each(|op| op.check_and_link(&mut ops, ctx, hasher));
        let ops = ops.into();
        let saved_return_idents = std::mem::take(&mut ctx.return_idents);
        let ctrl = self.ctrl.check_and_link(ctx, hasher);
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
}

impl<F: Clone + Ord> CtrlE<F> {
    fn check_and_link<H: Hasher<F>>(&self, ctx: &mut CheckCtx<'_>, hasher: &H) -> Ctrl<F> {
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
            CtrlE::Match(var, cases) => {
                assert_eq!(var.size, 1);
                let t = use_var(var, ctx)[0];
                let mut vec = Vec::with_capacity(cases.branches.size());
                for (f, block) in cases.branches.iter() {
                    ctx.block_ident += 1;
                    let state = ctx.save_bind_state();
                    let block = block.check_and_link(ctx, hasher);
                    ctx.restore_bind_state(state);
                    vec.push((f.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    ctx.block_ident += 1;
                    def.check_and_link(ctx, hasher).into()
                });
                let cases = Cases { branches, default };
                Ctrl::Match(t, cases)
            }
            CtrlE::MatchMany(t, cases) => {
                let size = t.size;
                let vars = use_var(t, ctx).into();
                let mut vec = Vec::with_capacity(cases.branches.size());
                for (fs, block) in cases.branches.iter() {
                    assert_eq!(fs.len(), size, "Pattern must have size {size}");
                    ctx.block_ident += 1;
                    let state = ctx.save_bind_state();
                    let block = block.check_and_link(ctx, hasher);
                    ctx.restore_bind_state(state);
                    vec.push((fs.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    ctx.block_ident += 1;
                    def.check_and_link(ctx, hasher).into()
                });
                let cases = Cases { branches, default };
                Ctrl::MatchMany(vars, cases)
            }
            CtrlE::If(b, true_block, false_block) => {
                let vars = use_var(b, ctx).into();

                ctx.block_ident += 1;
                let state = ctx.save_bind_state();
                let true_block = true_block.check_and_link(ctx, hasher);
                ctx.restore_bind_state(state);

                ctx.block_ident += 1;
                let false_block = false_block.check_and_link(ctx, hasher);

                if b.size != 1 {
                    Ctrl::IfMany(vars, true_block.into(), false_block.into())
                } else {
                    Ctrl::If(vars[0], true_block.into(), false_block.into())
                }
            }
        }
    }
}

impl<F: Clone + Ord> OpE<F> {
    fn check_and_link<H: Hasher<F>>(
        &self,
        ops: &mut Vec<Op<F>>,
        ctx: &mut CheckCtx<'_>,
        hasher: &H,
    ) {
        match self {
            OpE::AssertNe(a, b) => {
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx).into();
                ops.push(Op::AssertNe(a, b));
            }
            OpE::AssertEq(a, b) => {
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx).into();
                ops.push(Op::AssertEq(a, b));
            }
            OpE::Contains(a, b) => {
                assert_eq!(b.size, 1);
                let a = use_var(a, ctx).into();
                let b = use_var(b, ctx)[0];
                ops.push(Op::Contains(a, b));
            }
            OpE::Const(tgt, f) => {
                assert_eq!(tgt.size, 1);
                ops.push(Op::Const(f.clone()));
                bind_new(tgt, ctx);
            }
            OpE::Array(tgt, fs) => {
                assert_eq!(tgt.size, fs.len());
                for f in fs.iter() {
                    ops.push(Op::Const(f.clone()));
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
                } = ctx.info_map.get_index(name_idx).unwrap().1;
                assert_eq!(inp.total_size(), input_size);
                assert_eq!(out.total_size(), output_size);
                let inp = inp.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::Call(name_idx, inp, ctx.call_ident));
                ctx.call_ident += 1;
                out.iter().for_each(|t| bind_new(t, ctx));
            }
            OpE::PreImg(out, name, inp) => {
                let name_idx = ctx
                    .info_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let FuncInfo {
                    input_size,
                    output_size,
                } = ctx.info_map.get_index(name_idx).unwrap().1;
                assert_eq!(out.total_size(), input_size);
                assert_eq!(inp.total_size(), output_size);
                let inp = inp.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::PreImg(name_idx, inp, ctx.call_ident));
                ctx.call_ident += 1;
                out.iter().for_each(|t| bind_new(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                assert_eq!(ptr.size, 1);
                let vals = vals.iter().flat_map(|a| use_var(a, ctx).to_vec()).collect();
                ops.push(Op::Store(vals, ctx.call_ident));
                ctx.call_ident += 1;
                bind_new(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                assert_eq!(ptr.size, 1);
                let ptr = use_var(ptr, ctx)[0];
                ops.push(Op::Load(vals.total_size(), ptr, ctx.call_ident));
                ctx.call_ident += 1;
                vals.iter().for_each(|val| bind_new(val, ctx));
            }
            OpE::Debug(s) => ops.push(Op::Debug(s)),
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
            OpE::Hash(img, preimg) => {
                assert_eq!(img.total_size(), hasher.img_size());
                let preimg: List<_> = preimg
                    .iter()
                    .flat_map(|a| use_var(a, ctx).to_vec())
                    .collect();
                img.iter().for_each(|val| bind_new(val, ctx));
                ops.push(Op::Hash(preimg));
            }
        }
    }
}
