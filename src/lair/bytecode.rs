use super::{expr::*, map::Map, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Div(usize, usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block<F> {
    pub ops: Vec<Op<F>>,
    pub ctrl: Ctrl<F>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ctrl<F> {
    Match(usize, Cases<F>),
    If(usize, Box<Block<F>>, Box<Block<F>>),
    Return(Vec<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<F> {
    pub branches: Map<F, Block<F>>,
    pub default: Option<Box<Block<F>>>,
}

impl<F: Ord> Cases<F> {
    pub fn match_case(&self, f: &F) -> Option<&Block<F>> {
        self.branches.get(f).or(self.default.as_deref())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Func<F> {
    name: Name,
    input_size: usize,
    output_size: usize,
    body: Block<F>,
}

impl<F: Clone + Ord> FuncE<F> {
    /// Checks if a named `Func` is correct, and produces an index-based `Func` by replacing names with indexes
    pub fn check_and_link(&self) -> Func<F> {
        use std::collections::BTreeMap;
        /// Binds a variable and sets it as "unused"
        #[inline]
        fn bind(var: &Var, idx: &mut usize, map: &mut BTreeMap<Var, (bool, usize)>) {
            map.insert(*var, (false, *idx));
            *idx += 1;
        }

        /// Check if variable is bound and sets it as "used"
        #[inline]
        fn is_bound(var: &Var, map: &mut BTreeMap<Var, (bool, usize)>) -> usize {
            let (flag, idx) = map
                .get_mut(var)
                .unwrap_or_else(|| panic!("Variable {var} is unbound."));
            *flag = true;
            *idx
        }

        fn recurse<F: Clone + Ord>(
            block: &BlockE<F>,
            return_size: usize,
            map: &mut BTreeMap<Var, (bool, usize)>,
            mut idx: usize,
        ) -> Block<F> {
            let mut ops = Vec::new();
            for op in &block.ops {
                match op {
                    OpE::Const(tgt, f) => {
                        bind(tgt, &mut idx, map);
                        ops.push(Op::Const(f.clone()));
                    }
                    OpE::Add(tgt, a, b) => {
                        let a = is_bound(a, map);
                        let b = is_bound(b, map);
                        bind(tgt, &mut idx, map);
                        ops.push(Op::Add(a, b));
                    }
                    OpE::Mul(tgt, a, b) => {
                        let a = is_bound(a, map);
                        let b = is_bound(b, map);
                        bind(tgt, &mut idx, map);
                        ops.push(Op::Mul(a, b));
                    }
                    OpE::Sub(tgt, a, b) => {
                        let a = is_bound(a, map);
                        let b = is_bound(b, map);
                        bind(tgt, &mut idx, map);
                        ops.push(Op::Sub(a, b));
                    }
                    OpE::Div(tgt, a, b) => {
                        let a = is_bound(a, map);
                        let b = is_bound(b, map);
                        bind(tgt, &mut idx, map);
                        ops.push(Op::Div(a, b));
                    }
                }
            }
            let ctrl = match &block.ctrl {
                CtrlE::Return(return_vars) => {
                    assert!(
                        return_vars.len() == return_size,
                        "Return size {} different from expected size of return {}",
                        return_vars.len(),
                        return_size
                    );
                    let return_vec = return_vars.iter().map(|arg| is_bound(arg, map)).collect();
                    Ctrl::Return(return_vec)
                }
                CtrlE::Match(var, cases) => {
                    let t = is_bound(var, map);
                    let mut vec = Vec::with_capacity(cases.branches.size());
                    for (f, block) in cases.branches.iter() {
                        let cloned_map = &mut map.clone();
                        let block = recurse(block, return_size, cloned_map, idx);
                        vec.push((f.clone(), block))
                    }
                    let branches = Map::from_vec(vec);
                    let default = cases
                        .default
                        .as_ref()
                        .map(|def| recurse(def, return_size, map, idx).into());
                    let cases = Cases { branches, default };
                    Ctrl::Match(t, cases)
                }
                CtrlE::If(b, true_block, false_block) => {
                    let b = is_bound(b, map);
                    let cloned_map = &mut map.clone();
                    let true_block = recurse(true_block, return_size, cloned_map, idx);
                    let false_block = recurse(false_block, return_size, map, idx);
                    Ctrl::If(b, true_block.into(), false_block.into())
                }
            };
            Block { ctrl, ops }
        }

        let map = &mut BTreeMap::new();
        let mut idx = 0;
        self.input_params.iter().for_each(|var| {
            bind(var, &mut idx, map);
        });
        let body = recurse(&self.body, self.output_size, map, idx);
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
