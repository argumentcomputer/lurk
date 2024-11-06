//! The toplevel is the collection of all compiled Lair functions and external chips
//! of a Lair program. It is the core structure behind Lair.

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
    /// Given a list of Lair functions and a chip map, create a new toplevel by checking and
    /// compiling all functions and collecting them in a name->definition map
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
            .map(|(i, func)| {
                func.check(&info_map, &chip_map);
                let cfunc = func.expand().compile(i, &info_map, &chip_map);
                (func.name, cfunc)
            })
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
        self.func_map
            .get_index(i)
            .unwrap_or_else(|| panic!("Func index {i} out of bounds"))
            .1
    }

    #[inline]
    pub fn func_by_name(&self, name: &'static str) -> &Func<F> {
        self.func_map
            .get(&Name(name))
            .unwrap_or_else(|| panic!("Func {name} not found"))
    }

    #[inline]
    pub fn num_funcs(&self) -> usize {
        self.func_map.len()
    }

    #[inline]
    pub fn chip_by_index(&self, i: usize) -> &Either<C1, C2> {
        self.chip_map
            .get_index(i)
            .unwrap_or_else(|| panic!("Chip index {i} out of bounds"))
            .1
    }
}

/// A map from `Var` its block identifier. Variables in this map are always bound
type BindMap = FxHashMap<Var, usize>;

/// A map that tells whether a `Var`, from a certain block, has been used or not
type UsedMap = FxHashMap<(Var, usize), bool>;

/// A map from `Var` to its compiled indices
type LinkMap = FxHashMap<Var, List<usize>>;

impl Var {
    fn check_unused_var(&self, used: bool) {
        let Ident::User(name) = self.name else {
            unreachable!()
        };
        let ch = name.chars().next().expect("Empty var name");
        assert!(
            used || ch == '_',
            "Variable {self} not used. If intended, please prefix it with \"_\""
        );
    }
}

#[inline]
/// Binds a new variable. If a variable of the same name, in the same block, is shadowed,
/// then it ensures the variable has been used at least once or starts with '_'
fn bind_var<C1, C2>(var: &Var, ctx: &mut CheckCtx<'_, C1, C2>) {
    ctx.bind_map.insert(*var, ctx.block_ident);
    if let Some(used) = ctx.used_map.insert((*var, ctx.block_ident), false) {
        var.check_unused_var(used)
    }
}

#[inline]
/// Marks a variable as used
fn use_var<C1, C2>(var: &Var, ctx: &mut CheckCtx<'_, C1, C2>) {
    let block_idx = ctx
        .bind_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    let used = ctx
        .used_map
        .get_mut(&(*var, *block_idx))
        .expect("Data should have been inserted when binding");
    *used = true;
}

#[inline]
/// Links a variable name to a list of fresh indices
fn link_new<C1, C2>(var: &Var, ctx: &mut LinkCtx<'_, C1, C2>) {
    let idxs = (0..var.size).map(|_| ctx.new_var()).collect();
    link(var, idxs, ctx);
}

#[inline]
/// Links a variable name to a given list of indices
fn link<C1, C2>(var: &Var, idxs: List<usize>, ctx: &mut LinkCtx<'_, C1, C2>) {
    ctx.link_map.insert(*var, idxs);
}

#[inline]
/// Retrieves the indices of a given variable
fn get_var<'a, C1, C2>(var: &Var, ctx: &'a mut LinkCtx<'_, C1, C2>) -> &'a [usize] {
    ctx.link_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."))
}

/// Context struct of `check`
struct CheckCtx<'a, C1, C2> {
    block_ident: usize,
    return_size: usize,
    partial: bool,
    bind_map: BindMap,
    used_map: UsedMap,
    info_map: &'a FxIndexMap<Name, FuncInfo>,
    chip_map: &'a FxIndexMap<Name, Either<C1, C2>>,
}

/// Context struct of `expand`
struct ExpandCtx {
    uniq_ident: usize,
}

/// Context struct of `compile`
struct LinkCtx<'a, C1, C2> {
    var_index: usize,
    return_ident: usize,
    return_idents: Vec<usize>,
    link_map: LinkMap,
    info_map: &'a FxIndexMap<Name, FuncInfo>,
    chip_map: &'a FxIndexMap<Name, Either<C1, C2>>,
}

impl<C1, C2> CheckCtx<'_, C1, C2> {
    fn save_state(&mut self) -> BindMap {
        self.bind_map.clone()
    }

    fn restore_state(&mut self, bind_map: BindMap) {
        self.bind_map = bind_map;
    }
}

impl ExpandCtx {
    fn new_var(&mut self, size: usize) -> Var {
        let name = Ident::Internal(self.uniq_ident);
        self.uniq_ident += 1;
        Var { name, size }
    }
}

impl<C1, C2> LinkCtx<'_, C1, C2> {
    fn save_state(&mut self) -> (usize, LinkMap) {
        (self.var_index, self.link_map.clone())
    }

    fn restore_state(&mut self, (index, link_map): (usize, LinkMap)) {
        self.var_index = index;
        self.link_map = link_map;
    }

    fn new_var(&mut self) -> usize {
        let var = self.var_index;
        self.var_index += 1;
        var
    }
}

impl<F: Field + Ord> FuncE<F> {
    /// Checks that a Lair function is well formed
    fn check<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        info_map: &FxIndexMap<Name, FuncInfo>,
        chip_map: &FxIndexMap<Name, Either<C1, C2>>,
    ) {
        let ctx = &mut CheckCtx {
            block_ident: 0,
            return_size: self.output_size,
            partial: self.partial,
            bind_map: FxHashMap::default(),
            used_map: FxHashMap::default(),
            info_map,
            chip_map,
        };
        self.input_params.iter().for_each(|var| {
            bind_var(var, ctx);
        });
        self.body.check(ctx);
        for ((var, _), used) in ctx.used_map.iter() {
            var.check_unused_var(*used)
        }
    }

    /// Expands complex operations into simpler ones
    fn expand(&self) -> FuncE<F> {
        let ctx = &mut ExpandCtx { uniq_ident: 0 };
        let body = self.body.expand(ctx);
        FuncE {
            name: self.name,
            invertible: self.invertible,
            partial: self.partial,
            body,
            input_params: self.input_params.clone(),
            output_size: self.output_size,
        }
    }

    /// Compile a Lair function into bytecode
    fn compile<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        func_index: usize,
        info_map: &FxIndexMap<Name, FuncInfo>,
        chip_map: &FxIndexMap<Name, Either<C1, C2>>,
    ) -> Func<F> {
        let ctx = &mut LinkCtx {
            var_index: 0,
            return_ident: 0,
            return_idents: vec![],
            link_map: FxHashMap::default(),
            info_map,
            chip_map,
        };
        self.input_params.iter().for_each(|var| {
            link_new(var, ctx);
        });
        let body = self.body.compile(ctx);
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
    fn check<C1: Chipset<F>, C2: Chipset<F>>(&self, ctx: &mut CheckCtx<'_, C1, C2>) {
        self.ops.iter().for_each(|op| op.check(ctx));
        self.ctrl.check(ctx);
    }

    fn expand(&self, ctx: &mut ExpandCtx) -> BlockE<F> {
        self.expand_with_ops(vec![], ctx)
    }

    fn expand_with_ops(&self, mut ops: Vec<OpE<F>>, ctx: &mut ExpandCtx) -> BlockE<F> {
        self.ops.iter().for_each(|op| op.expand(&mut ops, ctx));
        let ops = ops.into();
        let ctrl = self.ctrl.expand(ctx);
        BlockE { ops, ctrl }
    }

    fn compile<C1: Chipset<F>, C2: Chipset<F>>(&self, ctx: &mut LinkCtx<'_, C1, C2>) -> Block<F> {
        let mut ops = vec![];
        self.ops.iter().for_each(|op| op.compile(&mut ops, ctx));
        let ops = ops.into();
        let saved_return_idents = std::mem::take(&mut ctx.return_idents);
        let ctrl = self.ctrl.compile(ctx);
        let block_return_idents = std::mem::take(&mut ctx.return_idents);
        // sanity check
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

impl<F: Field + Ord> CtrlE<F> {
    fn check<C1: Chipset<F>, C2: Chipset<F>>(&self, ctx: &mut CheckCtx<'_, C1, C2>) {
        match &self {
            CtrlE::Return(return_vars) => {
                let total_size = return_vars.total_size();
                assert_eq!(
                    total_size, ctx.return_size,
                    "Return size {} different from expected size of return {}",
                    total_size, ctx.return_size
                );
                return_vars.iter().for_each(|arg| use_var(arg, ctx));
            }
            CtrlE::If(b, true_block, false_block) => {
                use_var(b, ctx);

                let state = ctx.save_state();
                ctx.block_ident += 1;
                true_block.check(ctx);
                ctx.restore_state(state);

                let state = ctx.save_state();
                ctx.block_ident += 1;
                false_block.check(ctx);
                ctx.restore_state(state);
            }
            CtrlE::Match(t, cases) => {
                assert_eq!(t.size, 1);
                use_var(t, ctx);
                // TODO check for repetitive branches
                for (_, (block, _)) in cases.branches.iter() {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    block.check(ctx);
                    ctx.restore_state(state);
                }
                if let Some(def) = cases.default.as_ref() {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    def.0.check(ctx);
                    ctx.restore_state(state);
                }
            }
            CtrlE::MatchMany(t, cases) => {
                let size = t.size;
                use_var(t, ctx);
                // TODO check for repetitive branches
                for (fs, (block, _)) in cases.branches.iter() {
                    assert_eq!(fs.len(), size, "Pattern must have size {size}");
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    block.check(ctx);
                    ctx.restore_state(state);
                }
                if let Some(def) = &cases.default {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    def.0.check(ctx);
                    ctx.restore_state(state);
                }
            }
            CtrlE::Choose(t, cases) => {
                assert_eq!(t.size, 1);
                use_var(t, ctx);
                // TODO check for repetitive branches
                for (_, block) in cases.branches.iter() {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    block.check(ctx);
                    ctx.restore_state(state);
                }
                if let Some(def) = cases.default.as_ref() {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    def.check(ctx);
                    ctx.restore_state(state);
                }
            }
            CtrlE::ChooseMany(t, cases) => {
                let size = t.size;
                use_var(t, ctx);
                // TODO check for repetitive branches
                for (fs, block) in cases.branches.iter() {
                    assert_eq!(fs.len(), size, "Pattern must have size {size}");
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    block.check(ctx);
                    ctx.restore_state(state);
                }
                if let Some(def) = &cases.default {
                    let state = ctx.save_state();
                    ctx.block_ident += 1;
                    def.check(ctx);
                    ctx.restore_state(state);
                }
            }
        }
    }

    fn expand(&self, ctx: &mut ExpandCtx) -> CtrlE<F> {
        match self {
            CtrlE::Return(..) => self.clone(),
            CtrlE::If(x, t, f) => {
                let zero = ctx.new_var(x.size);
                let arr: List<_> = vec![F::zero(); x.size].into();
                let ops = vec![OpE::Array(zero, arr.clone()), OpE::AssertNe(*x, zero)];
                let t = t.expand_with_ops(ops, ctx).into();
                let ops = vec![OpE::Array(zero, arr.clone()), OpE::AssertEq(*x, zero, None)];
                let f = f.expand_with_ops(ops, ctx);
                let branches = vec![(arr, f)];
                let default = Some(t);
                let cases = CasesE { branches, default };
                if x.size == 1 {
                    CtrlE::Choose(*x, cases)
                } else {
                    CtrlE::ChooseMany(*x, cases)
                }
            }
            CtrlE::Match(v, cases) => {
                let branches = cases
                    .branches
                    .iter()
                    .map(|(fs, (block, constrained))| {
                        let mut ops = Vec::new();
                        if let CaseType::Constrained = constrained {
                            let arr = ctx.new_var(fs.len());
                            ops.push(OpE::Array(arr, fs.clone()));
                            ops.push(OpE::Contains(arr, *v));
                        }
                        (fs.clone(), block.expand_with_ops(ops, ctx))
                    })
                    .collect();
                let default = cases.default.as_ref().map(|b| {
                    let (block, constrained) = &**b;
                    let mut ops = Vec::new();
                    if let CaseType::Constrained = constrained {
                        for (fs, (_, _)) in cases.branches.iter() {
                            for f in fs.iter() {
                                // Collect constant as var
                                let f_var = ctx.new_var(1);
                                ops.push(OpE::Const(f_var, *f));
                                // Assert inequality of matched var
                                ops.push(OpE::AssertNe(*v, f_var));
                            }
                        }
                    }
                    block.expand_with_ops(ops, ctx).into()
                });
                let cases = CasesE { branches, default };
                CtrlE::Choose(*v, cases)
            }
            CtrlE::MatchMany(vs, cases) => {
                let branches = cases
                    .branches
                    .iter()
                    .map(|(fs, (block, constrained))| {
                        let mut ops = Vec::new();
                        if let CaseType::Constrained = constrained {
                            let arr = ctx.new_var(fs.len());
                            ops.push(OpE::Array(arr, fs.clone()));
                            ops.push(OpE::AssertEq(*vs, arr, None));
                        }
                        (fs.clone(), block.expand_with_ops(ops, ctx))
                    })
                    .collect();
                let default = cases.default.as_ref().map(|b| {
                    let (block, constrained) = &**b;
                    let mut ops = Vec::new();
                    if let CaseType::Constrained = constrained {
                        for (fs, (_, _)) in cases.branches.iter() {
                            // Collect all constants as vars
                            let arr = ctx.new_var(fs.len());
                            ops.push(OpE::Array(arr, fs.clone()));
                            // Assert inequality of matched vars
                            ops.push(OpE::AssertNe(*vs, arr));
                        }
                    }
                    block.expand_with_ops(ops, ctx).into()
                });
                let cases = CasesE { branches, default };
                CtrlE::ChooseMany(*vs, cases)
            }
            CtrlE::Choose(v, cases) => {
                let branches = cases
                    .branches
                    .iter()
                    .map(|(fs, block)| (fs.clone(), block.expand(ctx)))
                    .collect();
                let default = cases.default.as_ref().map(|block| block.expand(ctx).into());
                let cases = CasesE { branches, default };
                CtrlE::Choose(*v, cases)
            }
            CtrlE::ChooseMany(vs, cases) => {
                let branches = cases
                    .branches
                    .iter()
                    .map(|(fs, block)| (fs.clone(), block.expand(ctx)))
                    .collect();
                let default = cases.default.as_ref().map(|block| block.expand(ctx).into());
                let cases = CasesE { branches, default };
                CtrlE::ChooseMany(*vs, cases)
            }
        }
    }

    fn compile<C1: Chipset<F>, C2: Chipset<F>>(&self, ctx: &mut LinkCtx<'_, C1, C2>) -> Ctrl<F> {
        match &self {
            CtrlE::Return(return_vars) => {
                let return_vec = return_vars
                    .iter()
                    .flat_map(|arg| get_var(arg, ctx).to_vec())
                    .collect();
                let ctrl = Ctrl::Return(ctx.return_ident, return_vec);
                ctx.return_idents.push(ctx.return_ident);
                ctx.return_ident += 1;
                ctrl
            }
            CtrlE::Choose(v, cases) => {
                let var = get_var(v, ctx)[0];
                let mut vec = Vec::with_capacity(cases.branches.len());
                let mut unique_branches = Vec::new();
                for (fs, block) in cases.branches.iter() {
                    let state = ctx.save_state();
                    let block = block.compile(ctx);
                    ctx.restore_state(state);
                    fs.iter().for_each(|f| vec.push((*f, block.clone())));
                    unique_branches.push(block);
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| def.compile(ctx).into());
                let cases = Cases { branches, default };
                Ctrl::Choose(var, cases, unique_branches.into())
            }
            CtrlE::ChooseMany(vs, cases) => {
                let vars: List<_> = get_var(vs, ctx).into();
                let mut vec = Vec::with_capacity(cases.branches.len());
                for (fs, block) in cases.branches.iter() {
                    let state = ctx.save_state();
                    let block = block.compile(ctx);
                    ctx.restore_state(state);
                    vec.push((fs.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| def.compile(ctx).into());
                let cases = Cases { branches, default };
                Ctrl::ChooseMany(vars, cases)
            }
            CtrlE::If(..) | CtrlE::Match(..) | CtrlE::MatchMany(..) => panic!("Expand first"),
        }
    }
}

impl<F: Field + Ord> OpE<F> {
    fn check<C1: Chipset<F>, C2: Chipset<F>>(&self, ctx: &mut CheckCtx<'_, C1, C2>) {
        match self {
            OpE::AssertNe(a, b) | OpE::AssertEq(a, b, _) => {
                assert_eq!(a.size, b.size, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                use_var(b, ctx);
            }
            OpE::Contains(a, b) => {
                assert_eq!(b.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                use_var(b, ctx);
            }
            OpE::Const(tgt, _) => {
                assert_eq!(tgt.size, 1, "Var mismatch on `{}`", self.pretty());
                bind_var(tgt, ctx);
            }
            OpE::Array(tgt, fs) => {
                assert_eq!(tgt.size, fs.len(), "Var mismatch on `{}`", self.pretty());
                bind_var(tgt, ctx);
            }
            OpE::Add(tgt, a, b) | OpE::Mul(tgt, a, b) | OpE::Sub(tgt, a, b) => {
                assert_eq!(a.size, b.size, "Var mismatch on `{}`", self.pretty());
                assert_eq!(a.size, tgt.size, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                use_var(b, ctx);
                bind_var(tgt, ctx);
            }
            OpE::Div(tgt, a, b) => {
                assert_eq!(a.size, b.size, "Var mismatch on `{}`", self.pretty());
                assert_eq!(a.size, tgt.size, "Var mismatch on `{}`", self.pretty());
                use_var(b, ctx);
                use_var(a, ctx);
                bind_var(tgt, ctx);
            }
            OpE::Inv(tgt, a) => {
                assert_eq!(a.size, tgt.size, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                bind_var(tgt, ctx);
            }
            OpE::Not(tgt, a) => {
                assert_eq!(tgt.size, 1, "Var mismatch on `{}`", self.pretty());
                assert_eq!(a.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                bind_var(tgt, ctx);
            }
            OpE::Eq(tgt, a, b) => {
                assert_eq!(tgt.size, 1, "Var mismatch on `{}`", self.pretty());
                assert_eq!(a.size, 1, "Var mismatch on `{}`", self.pretty());
                assert_eq!(b.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                use_var(b, ctx);
                bind_var(tgt, ctx);
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
                assert_eq!(
                    inp.total_size(),
                    input_size,
                    "Input mismatch on `{}`",
                    self.pretty()
                );
                assert_eq!(
                    out.total_size(),
                    output_size,
                    "Output mismatch on `{}`",
                    self.pretty()
                );
                inp.iter().for_each(|a| use_var(a, ctx));
                out.iter().for_each(|t| bind_var(t, ctx));
            }
            OpE::PreImg(out, name, inp, _) => {
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
                assert_eq!(
                    out.total_size(),
                    input_size,
                    "Input mismatch on `{}`",
                    self.pretty()
                );
                assert_eq!(
                    inp.total_size(),
                    output_size,
                    "Output mismatch on `{}`",
                    self.pretty()
                );
                inp.iter().for_each(|a| use_var(a, ctx));
                out.iter().for_each(|t| bind_var(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                assert_eq!(ptr.size, 1, "Var mismatch on `{}`", self.pretty());
                vals.iter().for_each(|a| use_var(a, ctx));
                bind_var(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                assert_eq!(ptr.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(ptr, ctx);
                vals.iter().for_each(|val| bind_var(val, ctx));
            }
            OpE::Slice(pats, args) => {
                assert_eq!(
                    pats.total_size(),
                    args.total_size(),
                    "Var mismatch on `{}`",
                    self.pretty()
                );
                args.iter().for_each(|a| use_var(a, ctx));
                for pat in pats.as_slice() {
                    bind_var(pat, ctx);
                }
            }
            OpE::ExternCall(out, name, inp) => {
                let name_idx = ctx
                    .chip_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown extern chip {name}"));
                let (_, chip) = ctx.chip_map.get_index(name_idx).unwrap();
                assert_eq!(
                    inp.total_size(),
                    chip.input_size(),
                    "Input mismatch on `{}`",
                    self.pretty()
                );
                assert_eq!(
                    out.total_size(),
                    chip.output_size(),
                    "Output mismatch on `{}`",
                    self.pretty()
                );
                inp.iter().for_each(|a| use_var(a, ctx));
                out.iter().for_each(|t| bind_var(t, ctx));
            }
            OpE::Emit(vars) => {
                vars.iter().for_each(|a| use_var(a, ctx));
            }
            OpE::RangeU8(xs) => {
                xs.iter().for_each(|x| use_var(x, ctx));
            }
            OpE::Breakpoint | OpE::Debug(..) => (),
        }
    }

    fn expand(&self, ops: &mut Vec<Self>, ctx: &mut ExpandCtx) {
        match self {
            OpE::Div(tgt, a, b) => {
                let inv = ctx.new_var(b.size);
                ops.push(OpE::Inv(inv, *b));
                ops.push(OpE::Mul(*tgt, *a, inv));
            }
            OpE::Eq(tgt, a, b) => {
                let not_eq = ctx.new_var(a.size);
                ops.push(OpE::Sub(not_eq, *a, *b));
                ops.push(OpE::Not(*tgt, not_eq));
            }
            _ => ops.push(self.clone()),
        }
    }

    fn compile<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ops: &mut Vec<Op<F>>,
        ctx: &mut LinkCtx<'_, C1, C2>,
    ) {
        match self {
            OpE::AssertNe(a, b) => {
                let a = get_var(a, ctx).into();
                let b = get_var(b, ctx).into();
                ops.push(Op::AssertNe(a, b));
            }
            OpE::AssertEq(a, b, fmt) => {
                let a = get_var(a, ctx).into();
                let b = get_var(b, ctx).into();
                ops.push(Op::AssertEq(a, b, *fmt));
            }
            OpE::Contains(a, b) => {
                let a = get_var(a, ctx).into();
                let b = get_var(b, ctx)[0];
                ops.push(Op::Contains(a, b));
            }
            OpE::Const(tgt, f) => {
                ops.push(Op::Const(*f));
                link_new(tgt, ctx);
            }
            OpE::Array(tgt, fs) => {
                for f in fs.iter() {
                    ops.push(Op::Const(*f));
                }
                link_new(tgt, ctx);
            }
            OpE::Add(tgt, a, b) => {
                let a = get_var(a, ctx).to_vec();
                let b = get_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Add(*a, *b));
                }
                link_new(tgt, ctx);
            }
            OpE::Mul(tgt, a, b) => {
                let a = get_var(a, ctx).to_vec();
                let b = get_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Mul(*a, *b));
                }
                link_new(tgt, ctx);
            }
            OpE::Sub(tgt, a, b) => {
                let a = get_var(a, ctx).to_vec();
                let b = get_var(b, ctx);
                for (a, b) in a.iter().zip(b.iter()) {
                    ops.push(Op::Sub(*a, *b));
                }
                link_new(tgt, ctx);
            }
            OpE::Inv(tgt, a) => {
                let a = get_var(a, ctx);
                for a in a.iter() {
                    ops.push(Op::Inv(*a));
                }
                link_new(tgt, ctx);
            }
            OpE::Not(tgt, a) => {
                let a = get_var(a, ctx)[0];
                ops.push(Op::Not(a));
                link_new(tgt, ctx);
            }
            OpE::Call(out, name, inp) => {
                let name_idx = ctx
                    .info_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let inp = inp.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::Call(name_idx, inp));
                out.iter().for_each(|t| link_new(t, ctx));
            }
            OpE::PreImg(out, name, inp, fmt) => {
                let name_idx = ctx
                    .info_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let inp = inp.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::PreImg(name_idx, inp, *fmt));
                out.iter().for_each(|t| link_new(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                let vals = vals.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::Store(vals));
                link_new(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                let ptr = get_var(ptr, ctx)[0];
                ops.push(Op::Load(vals.total_size(), ptr));
                vals.iter().for_each(|val| link_new(val, ctx));
            }
            OpE::Slice(pats, args) => {
                let args: List<_> = args.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                let mut i = 0;
                for pat in pats.as_slice() {
                    let idxs = args[i..i + pat.size].into();
                    link(pat, idxs, ctx);
                    i += pat.size;
                }
            }
            OpE::ExternCall(out, name, inp) => {
                let name_idx = ctx
                    .chip_map
                    .get_index_of(name)
                    .unwrap_or_else(|| panic!("Unknown extern chip {name}"));
                let inp = inp.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::ExternCall(name_idx, inp));
                out.iter().for_each(|t| link_new(t, ctx));
            }
            OpE::Emit(vars) => {
                let vars = vars.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::Emit(vars));
            }
            OpE::RangeU8(xs) => {
                let xs = xs.iter().flat_map(|x| get_var(x, ctx).to_vec()).collect();
                ops.push(Op::RangeU8(xs));
            }
            OpE::Breakpoint => ops.push(Op::Breakpoint),
            OpE::Debug(s) => ops.push(Op::Debug(s)),
            OpE::Eq(..) | OpE::Div(..) => panic!("Expand first"),
        }
    }
}
