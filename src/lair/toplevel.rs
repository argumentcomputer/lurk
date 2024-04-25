use std::collections::BTreeMap;

use super::{bytecode::*, expr::*, map::Map, Name};

pub struct Toplevel<F>(Map<Name, Func<F>>);

pub(crate) struct FuncInfo {
    input_size: usize,
    output_size: usize,
}

impl<F: Clone + Ord> Toplevel<F> {
    pub fn new(funcs: &[FuncE<F>]) -> Self {
        let info_vec = funcs
            .iter()
            .map(|func| {
                let func_info = FuncInfo {
                    input_size: func.input_params.len(),
                    output_size: func.output_size,
                };
                (func.name, func_info)
            })
            .collect();
        let info_map = Map::from_vec(info_vec);
        let map = funcs
            .iter()
            .map(|func| (func.name, func.check_and_link(&info_map)))
            .collect();
        Toplevel(Map::from_vec(map))
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
/// Binds a variable and sets it as "unused"
#[inline]
fn bind(var: &Var, idx: &mut usize, map: &mut BTreeMap<Var, (bool, usize)>) {
    map.insert(*var, (false, *idx));
    *idx += 1;
}

/// Check if variable is bound and sets it as "used"
#[inline]
fn use_var(var: &Var, map: &mut BTreeMap<Var, (bool, usize)>) -> usize {
    let (flag, idx) = map
        .get_mut(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    *flag = true;
    *idx
}

impl<F: Clone + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func` by replacing names with indexes
    pub(crate) fn check_and_link(&self, info_map: &Map<Name, FuncInfo>) -> Func<F> {
        let map = &mut BTreeMap::new();
        let mut idx = 0;
        self.input_params.iter().for_each(|var| {
            bind(var, &mut idx, map);
        });
        let body = self
            .body
            .check_and_link(self.output_size, map, idx, info_map);
        for (var, (u, _)) in map.iter() {
            let ch = var.0.chars().next().unwrap();
            assert!(
                *u || ch == '_',
                "Variable {var} not used. If intended, please prefix it with \"_\""
            );
        }
        Func {
            name: self.name,
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
        map: &mut BTreeMap<Var, (bool, usize)>,
        mut idx: usize,
        info_map: &Map<Name, FuncInfo>,
    ) -> Block<F> {
        let mut ops = Vec::new();
        for op in self.ops.iter() {
            match op {
                OpE::Const(tgt, f) => {
                    bind(tgt, &mut idx, map);
                    ops.push(Op::Const(f.clone()));
                }
                OpE::Add(tgt, a, b) => {
                    let a = use_var(a, map);
                    let b = use_var(b, map);
                    bind(tgt, &mut idx, map);
                    ops.push(Op::Add(a, b));
                }
                OpE::Mul(tgt, a, b) => {
                    let a = use_var(a, map);
                    let b = use_var(b, map);
                    bind(tgt, &mut idx, map);
                    ops.push(Op::Mul(a, b));
                }
                OpE::Sub(tgt, a, b) => {
                    let a = use_var(a, map);
                    let b = use_var(b, map);
                    bind(tgt, &mut idx, map);
                    ops.push(Op::Sub(a, b));
                }
                OpE::Div(tgt, a, b) => {
                    let a = use_var(a, map);
                    let b = use_var(b, map);
                    bind(tgt, &mut idx, map);
                    ops.push(Op::Div(a, b));
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
                    let inp = inp.iter().map(|a| use_var(a, map)).collect();
                    out.iter().for_each(|t| bind(t, &mut idx, map));
                    ops.push(Op::Call(name_idx as u32, inp));
                }
            }
        }
        let ctrl = match &self.ctrl {
            CtrlE::Return(return_vars) => {
                assert!(
                    return_vars.len() == return_size,
                    "Return size {} different from expected size of return {}",
                    return_vars.len(),
                    return_size
                );
                let return_vec = return_vars.iter().map(|arg| use_var(arg, map)).collect();
                Ctrl::Return(return_vec)
            }
            CtrlE::Match(var, cases) => {
                let t = use_var(var, map);
                let mut vec = Vec::with_capacity(cases.branches.size());
                for (f, block) in cases.branches.iter() {
                    let cloned_map = &mut map.clone();
                    let block = block.check_and_link(return_size, cloned_map, idx, info_map);
                    vec.push((f.clone(), block))
                }
                let branches = Map::from_vec(vec);
                let default = cases
                    .default
                    .as_ref()
                    .map(|def| def.check_and_link(return_size, map, idx, info_map).into());
                let cases = Cases { branches, default };
                Ctrl::Match(t, cases)
            }
            CtrlE::If(b, true_block, false_block) => {
                let b = use_var(b, map);
                let cloned_map = &mut map.clone();
                let true_block = true_block.check_and_link(return_size, cloned_map, idx, info_map);
                let false_block = false_block.check_and_link(return_size, map, idx, info_map);
                Ctrl::If(b, true_block.into(), false_block.into())
            }
        };
        let ops = ops.into();
        Block { ctrl, ops }
    }
}

impl<F: Ord> Func<F> {
    pub fn name(&self) -> Name {
        self.name
    }

    pub fn body(&self) -> &Block<F> {
        &self.body
    }

    pub fn input_size(&self) -> usize {
        self.input_size
    }

    pub fn output_size(&self) -> usize {
        self.output_size
    }
}
