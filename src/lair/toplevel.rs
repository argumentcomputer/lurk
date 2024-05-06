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
fn bind(
    var: &Var,
    idx: &mut usize,
    block_ident: &usize,
    bind_map: &mut BindMap,
    used_map: &mut UsedMap,
) {
    bind_map.insert(*var, (*idx, *block_ident));
    if let Some(used) = used_map.insert((*var, *block_ident), false) {
        let ch = var.0.chars().next().unwrap();
        assert!(
            used || ch == '_',
            "Variable {var} not used. If intended, please prefix it with \"_\""
        );
    }
    *idx += 1;
}

#[inline]
fn use_var(var: &Var, bind_map: &mut BindMap, used_map: &mut UsedMap) -> usize {
    let (idx, block_idx) = bind_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    let used = used_map
        .get_mut(&(*var, *block_idx))
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    *used = true;
    *idx
}

impl<F: Ord> Func<F> {
    #[inline]
    pub fn name(&self) -> Name {
        self.name
    }

    #[inline]
    pub fn body(&self) -> &Block<F> {
        &self.body
    }

    #[inline]
    pub fn input_size(&self) -> usize {
        self.input_size
    }

    #[inline]
    pub fn output_size(&self) -> usize {
        self.output_size
    }
}

impl<F: Clone + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func`
    /// by replacing names with indices
    fn check_and_link(&self, func_index: usize, info_map: &Map<Name, FuncInfo>) -> Func<F> {
        let bind_map = &mut BTreeMap::new();
        let used_map = &mut BTreeMap::new();
        let mut idx = 0;
        let ident = &mut 0;
        self.input_params.iter().for_each(|var| {
            bind(var, &mut idx, ident, bind_map, used_map);
        });
        let body =
            self.body
                .check_and_link(self.output_size, idx, ident, bind_map, used_map, info_map);
        for ((var, _), used) in used_map.iter() {
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
    fn check_and_link(
        &self,
        return_size: usize,
        mut idx: usize,
        running_ident: &mut usize,
        bind_map: &mut BindMap,
        used_map: &mut UsedMap,
        info_map: &Map<Name, FuncInfo>,
    ) -> Block<F> {
        let ident = *running_ident;
        let mut ops = Vec::new();
        for op in self.ops.iter() {
            match op {
                OpE::Const(tgt, f) => {
                    ops.push(Op::Const(f.clone()));
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Add(tgt, a, b) => {
                    let a = use_var(a, bind_map, used_map);
                    let b = use_var(b, bind_map, used_map);
                    ops.push(Op::Add(a, b));
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Mul(tgt, a, b) => {
                    let a = use_var(a, bind_map, used_map);
                    let b = use_var(b, bind_map, used_map);
                    ops.push(Op::Mul(a, b));
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Sub(tgt, a, b) => {
                    let a = use_var(a, bind_map, used_map);
                    let b = use_var(b, bind_map, used_map);
                    ops.push(Op::Sub(a, b));
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Div(tgt, a, b) => {
                    let a = use_var(a, bind_map, used_map);
                    let b = use_var(b, bind_map, used_map);
                    ops.push(Op::Inv(b));
                    ops.push(Op::Mul(a, idx));
                    idx += 1;
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Inv(tgt, a) => {
                    let a = use_var(a, bind_map, used_map);
                    ops.push(Op::Inv(a));
                    bind(tgt, &mut idx, running_ident, bind_map, used_map);
                }
                OpE::Call(out, name, inp) => {
                    let name_idx = info_map
                        .get_index_of(name)
                        .unwrap_or_else(|| panic!("Unknown function {name}"));
                    assert!(u32::try_from(name_idx).is_ok());
                    let FuncInfo {
                        input_size,
                        output_size,
                    } = info_map.get_index(name_idx).unwrap().1;
                    assert_eq!(inp.len(), input_size);
                    assert_eq!(out.len(), output_size);
                    let inp = inp.iter().map(|a| use_var(a, bind_map, used_map)).collect();
                    ops.push(Op::Call(name_idx as u32, inp));
                    out.iter()
                        .for_each(|t| bind(t, &mut idx, running_ident, bind_map, used_map));
                }
            }
        }
        let ops = ops.into();
        let ctrl = self.ctrl.check_and_link(
            return_size,
            idx,
            running_ident,
            bind_map,
            used_map,
            info_map,
        );
        Block { ctrl, ops, ident }
    }
}

impl<F: Clone + Ord> CtrlE<F> {
    fn check_and_link(
        &self,
        return_size: usize,
        idx: usize,
        running_ident: &mut usize,
        bind_map: &mut BindMap,
        used_map: &mut UsedMap,
        info_map: &Map<Name, FuncInfo>,
    ) -> Ctrl<F> {
        match &self {
            CtrlE::Return(return_vars) => {
                assert_eq!(
                    return_vars.len(),
                    return_size,
                    "Return size {} different from expected size of return {}",
                    return_vars.len(),
                    return_size
                );
                let return_vec = return_vars
                    .iter()
                    .map(|arg| use_var(arg, bind_map, used_map))
                    .collect();
                Ctrl::Return(return_vec)
            }
            CtrlE::Match(var, cases) => {
                let t = use_var(var, bind_map, used_map);
                let mut vec = Vec::with_capacity(cases.branches.size());
                for (f, block) in cases.branches.iter() {
                    let bind_map_clone = &mut bind_map.clone();
                    *running_ident += 1;
                    let block = block.check_and_link(
                        return_size,
                        idx,
                        running_ident,
                        bind_map_clone,
                        used_map,
                        info_map,
                    );
                    vec.push((f.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases.default.as_ref().map(|def| {
                    *running_ident += 1;
                    def.check_and_link(
                        return_size,
                        idx,
                        running_ident,
                        bind_map,
                        used_map,
                        info_map,
                    )
                    .into()
                });
                let cases = Cases { branches, default };
                Ctrl::Match(t, cases)
            }
            CtrlE::If(b, true_block, false_block) => {
                let b = use_var(b, bind_map, used_map);
                let bind_map_clone = &mut bind_map.clone();
                *running_ident += 1;
                let true_block = true_block.check_and_link(
                    return_size,
                    idx,
                    running_ident,
                    bind_map_clone,
                    used_map,
                    info_map,
                );
                *running_ident += 1;
                let false_block = false_block.check_and_link(
                    return_size,
                    idx,
                    running_ident,
                    bind_map,
                    used_map,
                    info_map,
                );
                Ctrl::If(b, true_block.into(), false_block.into())
            }
        }
    }
}
