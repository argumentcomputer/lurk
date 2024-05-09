use std::collections::BTreeMap;

use super::{bytecode::*, expr::*, map::Map, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Toplevel<F>(Map<Name, Func<F>>);

pub(crate) struct FuncInfo {
    input_size: usize,
    output_size: usize,
}

impl<F: Clone + Ord> Toplevel<F> {
    pub fn new(funcs: &[FuncE<F>]) -> Self {
        let ordered_funcs = Map::from_vec(funcs.iter().map(|func| (func.name, func)).collect());
        let info_vec = ordered_funcs
            .iter()
            .map(|(name, func)| {
                let func_info = FuncInfo {
                    input_size: func.input_params.len(),
                    output_size: func.output_size,
                };
                (*name, func_info)
            })
            .collect();
        let info_map = Map::from_vec_unsafe(info_vec);
        let map = ordered_funcs
            .iter()
            .enumerate()
            .map(|(i, (name, func))| (*name, func.check_and_link(i, &info_map)))
            .collect();
        Toplevel(Map::from_vec_unsafe(map))
    }
}

impl<F> Toplevel<F> {
    #[inline]
    pub fn get_by_index(&self, i: usize) -> Option<&Func<F>> {
        self.0.get_index(i).map(|(_, func)| func)
    }

    #[inline]
    pub fn get_by_name(&self, name: &'static str) -> Option<&Func<F>> {
        self.0.get(&Name(name))
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.0.size()
    }
}

type BindMap = BTreeMap<Var, (usize, usize)>;
type UsedMap = BTreeMap<(Var, usize), bool>;

#[inline]
fn bind(var: &Var, ctx: &mut CheckCtx<'_>) {
    ctx.bind_map.insert(*var, (ctx.var_index, ctx.block_ident));
    if let Some(used) = ctx.used_map.insert((*var, ctx.block_ident), false) {
        let ch = var.0.chars().next().unwrap();
        assert!(
            used || ch == '_',
            "Variable {var} not used. If intended, please prefix it with \"_\""
        );
    }
    ctx.var_index += 1;
}

#[inline]
fn use_var(var: &Var, ctx: &mut CheckCtx<'_>) -> usize {
    let (idx, block_idx) = ctx
        .bind_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    let used = ctx
        .used_map
        .get_mut(&(*var, *block_idx))
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    *used = true;
    *idx
}

struct CheckCtx<'a> {
    var_index: usize,
    block_ident: usize,
    return_ident: usize,
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
}

impl<F: Clone + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func`
    /// by replacing names with indices
    fn check_and_link(&self, func_index: usize, info_map: &Map<Name, FuncInfo>) -> Func<F> {
        let ctx = &mut CheckCtx {
            var_index: 0,
            block_ident: 0,
            return_ident: 0,
            return_size: self.output_size,
            bind_map: BTreeMap::new(),
            used_map: BTreeMap::new(),
            info_map,
        };
        self.input_params.iter().for_each(|var| {
            bind(var, ctx);
        });
        let body = self.body.check_and_link(ctx);
        for ((var, _), used) in ctx.used_map.iter() {
            let ch = var.0.chars().next().unwrap();
            assert!(
                *used || ch == '_',
                "Variable {var} not used. If intended, please prefix it with \"_\""
            );
        }
        Func {
            name: self.name,
            index: func_index,
            body,
            input_size: self.input_params.len(),
            output_size: self.output_size,
        }
    }
}

impl<F: Clone + Ord> BlockE<F> {
    fn check_and_link(&self, ctx: &mut CheckCtx<'_>) -> Block<F> {
        let mut ops = Vec::new();
        for op in self.ops.iter() {
            match op {
                OpE::Const(tgt, f) => {
                    ops.push(Op::Const(f.clone()));
                    bind(tgt, ctx);
                }
                OpE::Add(tgt, a, b) => {
                    let a = use_var(a, ctx);
                    let b = use_var(b, ctx);
                    ops.push(Op::Add(a, b));
                    bind(tgt, ctx);
                }
                OpE::Mul(tgt, a, b) => {
                    let a = use_var(a, ctx);
                    let b = use_var(b, ctx);
                    ops.push(Op::Mul(a, b));
                    bind(tgt, ctx);
                }
                OpE::Sub(tgt, a, b) => {
                    let a = use_var(a, ctx);
                    let b = use_var(b, ctx);
                    ops.push(Op::Sub(a, b));
                    bind(tgt, ctx);
                }
                OpE::Div(tgt, a, b) => {
                    let a = use_var(a, ctx);
                    let b = use_var(b, ctx);
                    ops.push(Op::Inv(b));
                    ops.push(Op::Mul(a, ctx.var_index));
                    ctx.var_index += 1;
                    bind(tgt, ctx);
                }
                OpE::Inv(tgt, a) => {
                    let a = use_var(a, ctx);
                    ops.push(Op::Inv(a));
                    bind(tgt, ctx);
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
                    assert_eq!(inp.len(), input_size);
                    assert_eq!(out.len(), output_size);
                    let inp = inp.iter().map(|a| use_var(a, ctx)).collect();
                    ops.push(Op::Call(name_idx, inp));
                    out.iter().for_each(|t| bind(t, ctx));
                }
                OpE::Store(..) => {
                    todo!()
                }
                OpE::Load(..) => {
                    todo!()
                }
            }
        }
        let ops = ops.into();
        let ctrl = self.ctrl.check_and_link(ctx);
        Block { ctrl, ops }
    }
}

impl<F: Clone + Ord> CtrlE<F> {
    fn check_and_link(&self, ctx: &mut CheckCtx<'_>) -> Ctrl<F> {
        match &self {
            CtrlE::Return(return_vars) => {
                assert_eq!(
                    return_vars.len(),
                    ctx.return_size,
                    "Return size {} different from expected size of return {}",
                    return_vars.len(),
                    ctx.return_size
                );
                let return_vec = return_vars.iter().map(|arg| use_var(arg, ctx)).collect();
                let ctrl = Ctrl::Return(ctx.return_ident, return_vec);
                ctx.return_ident += 1;
                ctrl
            }
            CtrlE::Match(var, cases) => {
                let t = use_var(var, ctx);
                let mut vec = Vec::with_capacity(cases.branches.size());
                for (f, block) in cases.branches.iter() {
                    ctx.block_ident += 1;
                    let state = ctx.save_bind_state();
                    let block = block.check_and_link(ctx);
                    ctx.restore_bind_state(state);
                    vec.push((f.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    ctx.block_ident += 1;
                    def.check_and_link(ctx).into()
                });
                let cases = Cases { branches, default };
                Ctrl::Match(t, cases)
            }
            CtrlE::If(b, true_block, false_block) => {
                let b = use_var(b, ctx);

                ctx.block_ident += 1;
                let state = ctx.save_bind_state();
                let true_block = true_block.check_and_link(ctx);
                ctx.restore_bind_state(state);

                ctx.block_ident += 1;
                let false_block = false_block.check_and_link(ctx);
                Ctrl::If(b, true_block.into(), false_block.into())
            }
        }
    }
}
