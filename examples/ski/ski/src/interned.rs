#![allow(non_snake_case)]

use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::io;

use crate::{ParseTermError, SKI};

type Addr = usize;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ITerm {
    S(Addr, Option<Addr>, Option<Addr>, Option<Addr>),
    K(Addr, Option<Addr>, Option<Addr>),
    I(Addr, Option<Addr>),
    Seq(Addr, Addr, Addr),
    Nil,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Eval1(ITerm),
    Apply(ITerm, ITerm),
    Eval(ITerm),
}

#[derive(Debug)]
pub struct Step {
    op: Op,
    out: ITerm,
    depth: usize,
}

impl Step {
    pub fn fmt_to_string(&self, mem: &Mem) -> String {
        let mut out = Vec::new();
        self.fmt(mem, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    pub fn fmt<W: io::Write>(&self, mem: &Mem, w: &mut W) -> Result<(), io::Error> {
        write!(w, "[{}]", self.depth)?;
        for _ in 0..self.depth {
            write!(w, " ")?;
        }

        match &self.op {
            Op::Eval1(term) => {
                write!(w, "Eval1 ")?;
                term.fmt(mem, w)?;
            }
            Op::Eval(term) => {
                write!(w, "Eval ")?;
                term.fmt(mem, w)?;
            }
            Op::Apply(left, right) => {
                write!(w, "Apply ")?;
                left.fmt(mem, w)?;
                write!(w, "<-[")?;
                right.fmt(mem, w)?;
                write!(w, "] ")?;
            }
        }
        write!(w, " => ")?;
        self.out.fmt(mem, w)
    }

    fn fmt_steps<I: IntoIterator<Item = impl Borrow<Step>>, W: io::Write>(
        steps: I,
        mem: &Mem,
        w: &mut W,
    ) -> Result<(), io::Error> {
        for step in steps {
            step.borrow().fmt(mem, w)?;
            write!(w, "\n")?;
        }
        Ok(())
    }

    pub fn fmt_steps_to_string<I: IntoIterator<Item = impl Borrow<Step>>>(
        steps: I,
        mem: &Mem,
    ) -> String {
        let mut out = Vec::new();
        Self::fmt_steps(steps, mem, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }
}
const NIL_ADDR: usize = 3;

impl ITerm {
    pub fn is_s(&self) -> bool {
        matches!(self, Self::S(_, None, None, None))
    }
    pub fn is_s1(&self) -> bool {
        matches!(self, Self::S(_, Some(_), None, None))
    }
    pub fn is_s2(&self) -> bool {
        matches!(self, Self::S(_, Some(_), Some(_), None))
    }
    pub fn is_s3(&self) -> bool {
        matches!(self, Self::S(_, Some(_), Some(_), Some(_)))
    }
    pub fn is_k(&self) -> bool {
        matches!(self, Self::K(_, None, None))
    }
    pub fn is_k1(&self) -> bool {
        matches!(self, Self::K(_, Some(_), None))
    }
    pub fn is_k2(&self) -> bool {
        matches!(self, Self::K(_, Some(_), Some(_)))
    }
    pub fn is_i(&self) -> bool {
        matches!(self, Self::I(_, None))
    }
    pub fn is_i1(&self) -> bool {
        matches!(self, Self::I(_, Some(_),))
    }

    pub fn try_from_ski(mem: &mut Mem, ski: &SKI) -> Result<Self, ParseTermError> {
        Self::from_str(mem, &ski.src)
    }

    pub fn to_ski(&self, mem: &Mem) -> SKI {
        SKI {
            src: self.fmt_to_string(mem),
        }
    }

    pub fn addr(&self) -> Addr {
        match self {
            Self::S(addr, _, _, _) => *addr,
            Self::K(addr, _, _) => *addr,
            Self::I(addr, _) => *addr,
            Self::Seq(addr, _, _) => *addr,
            Self::Nil => 3,
        }
    }

    fn first(&self, mem: &mut Mem) -> (Self, Option<Self>) {
        match self {
            Self::Seq(_, first, rest) => {
                let rest_term = mem.get_term(*rest);
                let tail = match rest_term {
                    Self::Nil => None,
                    _ => Some(rest_term),
                };
                let first_term = mem.get_term(*first);
                assert!(first_term != ITerm::Nil);
                (first_term, tail)
            }
            _ => {
                panic!("xxxx")
            }
        }
    }

    pub fn from_str(mem: &mut Mem, s: &str) -> Result<Self, ParseTermError> {
        if s.is_empty() {
            Err(ParseTermError)
        } else {
            let mut stack = Vec::new();
            let mut inner = Vec::new();

            for c in s.chars() {
                match c {
                    'S' | 's' => inner.push(mem.S().addr()),
                    'K' | 'k' => inner.push(mem.K().addr()),
                    'I' | 'i' => inner.push(mem.I().addr()),
                    '(' => {
                        stack.push(inner);
                        inner = Vec::new();
                    }
                    ')' => {
                        let term = mem.seq(&inner);
                        inner = stack.pop().ok_or(ParseTermError)?;
                        inner.push(term.addr());
                    }
                    _ => Err(ParseTermError)?,
                };
            }
            if inner.len() == 1 {
                Ok(mem.get_term(inner[0]))
            } else {
                Ok(mem.seq(&inner))
            }
        }
    }
    pub fn fmt_to_string(&self, mem: &Mem) -> String {
        let mut out = Vec::new();
        self.fmt(mem, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    pub fn fmt<W: io::Write>(&self, mem: &Mem, w: &mut W) -> Result<(), io::Error> {
        match self {
            Self::S(_, None, None, None) => {
                write!(w, "S")
            }
            Self::S(_, Some(x), None, None) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, Some(x), Some(y), None) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, Some(x), Some(y), Some(z)) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                mem.borrow_term(*z).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::K(_, None, None) => {
                write!(w, "K")
            }
            Self::K(_, Some(x), None) => {
                write!(w, "(K")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::K(_, Some(x), Some(y)) => {
                write!(w, "(K")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::I(_, None) => {
                write!(w, "I")
            }
            Self::I(_, Some(x)) => {
                write!(w, "(I")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, _, _, _) => write!(w, "<malformed S>"),
            Self::K(_, _, _) => write!(w, "<malformed S>"),
            Self::Seq(_, first, rest) => {
                write!(w, "(")?;
                mem.borrow_term(*first).fmt(mem, w)?;

                let mut tail = rest.clone();
                loop {
                    match mem.borrow_term(tail) {
                        ITerm::Seq(_, first, rest) => {
                            mem.borrow_term(*first).fmt(mem, w)?;
                            tail = *rest;
                        }
                        last => {
                            last.fmt(mem, w)?;
                            write!(w, ")")?;
                            break;
                        }
                    }
                }
                Ok(())
            }
            Self::Nil => Ok(()),
        }
    }
    pub fn fmt3<W: io::Write>(&self, mem: &Mem, w: &mut W) -> Result<(), io::Error> {
        match self {
            Self::S(_, None, None, None) => {
                write!(w, "S")
            }
            Self::S(_, Some(x), None, None) => {
                write!(w, "S")?;
                mem.borrow_term(*x).fmt(mem, w)
            }
            Self::S(_, Some(x), Some(y), None) => {
                write!(w, "S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)
            }
            Self::S(_, Some(x), Some(y), Some(z)) => {
                write!(w, "S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                mem.borrow_term(*z).fmt(mem, w)
            }
            Self::K(_, None, None) => {
                write!(w, "K")
            }
            Self::K(_, Some(x), None) => {
                write!(w, "K")?;
                mem.borrow_term(*x).fmt(mem, w)
            }
            Self::K(_, Some(x), Some(y)) => {
                write!(w, "K")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)
            }
            Self::I(_, None) => {
                write!(w, "I")
            }
            Self::I(_, Some(x)) => {
                write!(w, "I")?;
                mem.borrow_term(*x).fmt(mem, w)
            }
            Self::S(_, _, _, _) => write!(w, "<malformed S>"),
            Self::K(_, _, _) => write!(w, "<malformed S>"),
            Self::Seq(_, first, rest) => {
                write!(w, "(")?;
                mem.borrow_term(*first).fmt(mem, w)?;

                let mut tail = rest.clone();
                loop {
                    match mem.borrow_term(tail) {
                        ITerm::Seq(_, first, rest) => {
                            mem.borrow_term(*first).fmt(mem, w)?;
                            tail = *rest;
                        }
                        last => {
                            last.fmt(mem, w)?;
                            write!(w, ")")?;
                            break;
                        }
                    }
                }
                Ok(())
            }
            Self::Nil => Ok(()),
        }
    }

    pub fn fmt2_to_string(&self, mem: &Mem) -> String {
        let mut out = Vec::new();
        self.fmt(mem, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    pub fn fmt2<W: io::Write>(&self, mem: &Mem, w: &mut W) -> Result<(), io::Error> {
        match self {
            Self::S(_, None, None, None) => {
                write!(w, "S")
            }
            Self::S(_, Some(x), None, None) => {
                write!(w, "(S1")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, Some(x), Some(y), None) => {
                write!(w, "(S2")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                mem.borrow_term(*y).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, Some(x), Some(y), Some(z)) => {
                write!(w, "(S3")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                mem.borrow_term(*y).fmt2(mem, w)?;
                mem.borrow_term(*z).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::K(_, None, None) => {
                write!(w, "K~")
            }
            Self::K(_, Some(x), None) => {
                write!(w, "(K1")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::K(_, Some(x), Some(y)) => {
                write!(w, "(K2")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                mem.borrow_term(*y).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::I(_, None) => {
                write!(w, "I")
            }
            Self::I(_, Some(x)) => {
                write!(w, "(I")?;
                mem.borrow_term(*x).fmt2(mem, w)?;
                write!(w, ")")
            }
            Self::S(_, _, _, _) => write!(w, "<malformed S>"),
            Self::K(_, _, _) => write!(w, "<malformed S>"),
            Self::Seq(_, first, rest) => {
                write!(w, "(")?;
                mem.borrow_term(*first).fmt2(mem, w)?;

                let mut tail = rest.clone();
                loop {
                    match mem.borrow_term(tail) {
                        ITerm::Seq(_, first, rest) => {
                            mem.borrow_term(*first).fmt2(mem, w)?;
                            tail = *rest;
                        }
                        last => {
                            last.fmt2(mem, w)?;
                            write!(w, ")")?;
                            break;
                        }
                    }
                }
                Ok(())
            }
            Self::Nil => Ok(()),
        }
    }

    fn eval1(self, mem: &mut Mem, depth: usize) -> Self {
        let op = Op::Eval1(self.clone());

        if let Some(found) = mem.memo.get(&op) {
            return found.clone();
        }

        let step = Step {
            op: op.clone(),
            // Placeholder: this will be updated when output is known.
            out: self.clone(),
            depth: depth,
        };
        mem.steps.push(step);
        let step_index = mem.steps.len() - 1;

        let result = match self {
            Self::S(_, Some(x), Some(y), Some(z)) => {
                let ix = mem.get_term(x);
                let iy = mem.get_term(y);
                let iz = mem.get_term(z);
                let xz = ix
                    .apply(mem, iz.clone(), 1 + depth)
                    .eval1(mem, 1 + depth)
                    .clone();
                let yz = iy.apply(mem, iz, depth + 1).eval1(mem, depth + 1).clone();
                xz.apply(mem, yz, depth + 1)
            }
            Self::S(_, _, _, _) => self,
            Self::K(_, Some(x), Some(_)) => mem.get_term(x),
            Self::K(_, _, _) => self,
            Self::I(_, Some(x)) => mem.get_term(x),
            Self::I(_, None) => self,
            Self::Seq(_, first, rest) => {
                let first = mem.get_term(first);
                let first_evaled = first.clone().eval(mem, depth + 1);
                if mem.get_term(rest) == ITerm::Nil {
                    if first_evaled == first {
                        first_evaled
                    } else {
                        mem.cons(first_evaled, Self::Nil)
                    }
                } else {
                    let rest = mem.get_term(rest);
                    let (second, tail) = rest.first(mem);
                    let second_evaled = second.clone().eval(mem, depth + 1);
                    let applied = first_evaled.clone().apply(mem, second_evaled, depth + 1);

                    if let Some(tail) = tail {
                        mem.cons(applied, tail)
                    } else {
                        mem.cons(applied, Self::Nil)
                    }
                }
            }
            Self::Nil => unreachable!(),
        };

        mem.steps[step_index].out = result.clone();
        mem.memo.insert(op, result.clone());
        result
    }

    pub fn eval(self, mem: &mut Mem, depth: usize) -> Self {
        let op = Op::Eval(self.clone());
        let step = Step {
            op: op.clone(),
            out: self.clone(),
            depth,
        };
        mem.steps.push(step);
        let step_index = mem.steps.len() - 1;

        if let Some(found) = mem.memo.get(&op) {
            return found.clone();
        }

        let mut prev_addr;
        let mut term = self.clone();

        loop {
            prev_addr = term.addr();
            term = term.eval1(mem, depth + 1);

            if term.addr() == prev_addr {
                break;
            };
        }
        mem.steps[step_index].out = term.clone();
        mem.memo.insert(op, term.clone());

        term
    }

    fn apply(self, mem: &mut Mem, a: Self, depth: usize) -> Self {
        let op = Op::Apply(self.clone(), a.clone());
        let step = Step {
            op: op.clone(),
            out: self.clone(),
            depth,
        };
        mem.steps.push(step);
        let step_index = mem.steps.len() - 1;

        if let Some(found) = mem.memo.get(&op) {
            return found.clone();
        }

        let result = match self {
            Self::S(_, None, None, None) => mem.S1(a.addr()),
            Self::S(_, Some(x), None, None) => mem.S2(x, a.addr()),
            Self::S(_, Some(x), Some(y), None) => mem.S3(x, y, a.addr()),
            Self::K(_, None, None) => mem.K1(a.addr()),
            Self::K(_, Some(x), None) => mem.K2(x, a.addr()),
            Self::I(_, None) => mem.I1(a.addr()),
            Self::I(_, Some(x)) => mem.get_term(x).apply(mem, a, depth + 1),
            Self::Seq(_, _, _) => {
                let applied = self.clone().eval(mem, depth + 1).apply(mem, a, depth + 1);
                applied //mem.cons(applied, Self::Nil)
            }
            Self::S(_, _, _, _) => panic!("malformed S"),
            Self::K(_, _, _) => panic!("malformed K"),
            Self::Nil => unreachable!(),
        };
        if let Some(found) = mem.memo.get(&op) {
            assert_eq!(found, &result);
        }

        mem.steps[step_index].out = result.clone();
        mem.memo.insert(op, result.clone());
        result
    }
}

#[derive(Debug, Default)]
pub struct Mem {
    terms: Vec<ITerm>,
    steps: Vec<Step>,
    memo: HashMap<Op, ITerm>,
    s1: HashMap<Addr, Addr>,
    s2: HashMap<(Addr, Addr), Addr>,
    s3: HashMap<(Addr, Addr, Addr), Addr>,
    k1: HashMap<Addr, Addr>,
    k2: HashMap<(Addr, Addr), Addr>,
    i1: HashMap<Addr, Addr>,
    seqs: HashMap<(Addr, Addr), Addr>,
}

impl Mem {
    pub fn new() -> Self {
        let mut mem = Mem::default();
        mem.terms = vec![
            ITerm::S(0, None, None, None),
            ITerm::K(1, None, None),
            ITerm::I(2, None),
            ITerm::Nil,
        ];

        mem
    }

    pub fn input(&self) -> ITerm {
        match &self.steps[0].op {
            Op::Eval(input) => input.clone(),
            _ => panic!("Mem does not describe a toplevel evaluation."),
        }
    }

    pub fn output(&self) -> ITerm {
        self.steps[0].out.clone()
    }

    pub fn borrow_term(&self, addr: Addr) -> &ITerm {
        &self.terms[addr]
    }

    pub fn get_term(&self, addr: Addr) -> ITerm {
        self.terms[addr].clone()
    }

    // NOTE: The clones are shallow.
    pub fn S(&mut self) -> ITerm {
        self.terms[0].clone()
    }
    pub fn K(&mut self) -> ITerm {
        self.terms[1].clone()
    }
    pub fn I(&mut self) -> ITerm {
        self.terms[2].clone()
    }

    pub fn S1(&mut self, x_addr: Addr) -> ITerm {
        if let Some(found) = self.s1.get(&x_addr) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::S(addr, Some(x_addr), None, None);
            self.s1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn S2(&mut self, x_addr: Addr, y_addr: Addr) -> ITerm {
        if let Some(found) = self.s2.get(&(x_addr, y_addr)) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::S(addr, Some(x_addr), Some(y_addr), None);
            self.s2.insert((x_addr, y_addr), addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn S3(&mut self, x_addr: Addr, y_addr: Addr, z_addr: Addr) -> ITerm {
        if let Some(found) = self.s3.get(&(x_addr, y_addr, z_addr)) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::S(addr, Some(x_addr), Some(y_addr), Some(z_addr));
            self.s3.insert((x_addr, y_addr, z_addr), addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn K1(&mut self, x_addr: Addr) -> ITerm {
        if let Some(found) = self.k1.get(&x_addr) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::K(addr, Some(x_addr), None);
            self.k1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn K2(&mut self, x_addr: Addr, y_addr: Addr) -> ITerm {
        if let Some(found) = self.k2.get(&(x_addr, y_addr)) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::K(addr, Some(x_addr), Some(y_addr));
            self.k2.insert((x_addr, y_addr), addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn I1(&mut self, x_addr: Addr) -> ITerm {
        if let Some(found) = self.i1.get(&x_addr) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::I(addr, Some(x_addr));
            self.i1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new
        }
    }
    pub fn seq(&mut self, addrs: &[Addr]) -> ITerm {
        if addrs.is_empty() {
            return ITerm::Nil;
        }
        let first_addr = addrs[0];
        let rest_seqs = self.seq(&addrs[1..]);

        if let Some(found) = self.seqs.get(&(first_addr, rest_seqs.addr())) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            if addrs.len() > 1 {
                self.seqs.insert((first_addr, rest_seqs.addr()), addr);
                let new = ITerm::Seq(addr, addrs[0], rest_seqs.addr());
                self.terms.push(new.clone());
                new
            } else {
                let new = ITerm::Seq(addr, addrs[0], NIL_ADDR);
                self.terms.push(new.clone());
                new
            }
        }
    }

    pub fn cons(&mut self, first: ITerm, rest: ITerm) -> ITerm {
        if let Some(found) = self.seqs.get(&(first.addr(), rest.addr())) {
            self.terms[*found].clone()
        } else {
            let addr = self.terms.len();
            let new = ITerm::Seq(addr, first.addr(), rest.addr());
            self.terms.push(new.clone());
            new
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn eval_test(input: &str, expected: &str) {
        let mem = &mut Mem::new();
        let term = ITerm::from_str(mem, input).unwrap();
        let evaled = term.clone().eval(mem, 0);

        if expected != evaled.fmt2_to_string(mem) {
            let _ = dbg!(&input);
            let _ = dbg!(Step::fmt_steps(&mem.steps, mem, &mut io::stdout()));
            // dbg!(&mem);
        }
        assert_eq!(expected, evaled.fmt_to_string(mem));
        assert_eq!(term, mem.input());
        assert_eq!(evaled, mem.output());
    }

    #[test]
    // cargo test debug -- --nocapture
    fn test_debug_reduction() {
        eval_test("(S(K(SI)))", "(S(K(SI)))");
        eval_test("(K(SI))", "(K(SI))");
        eval_test("(S(K(SI))K)", "(S(K(SI))K)");
        eval_test("((K(SI))K)KKI", "(KK)");
        eval_test("((K(SI))K)KK", "(K(KK))");
        eval_test("((((K(SI))K)K)K)", "(K(KK))");
        eval_test(&"K((SII)(SII))", "(K(SII(SII)))");
        eval_test("SIKKI", "(KK)");
    }

    #[test]
    fn test_iterm() {
        let test = |input: &str, expected: &str| {
            let mem = &mut Mem::new();
            let term = ITerm::from_str(mem, input).unwrap();
            assert_eq!(expected, term.fmt_to_string(mem));
        };

        test("K", "K");
        test("(S)", "(S)");
        test("(SI)", "(SI)");
        test("KIS(S)", "(KIS(S))");
        test("S(K(IS)S)KI", "(S(K(IS)S)KI)");

        eval_test("SK(KS)", "(SK(KS))");

        eval_test("SII(SII)", "(SII(SII))");
        eval_test("((SII)(SII))", "(SII(SII))");
        eval_test(&"K((SII)(SII))", "(K(SII(SII)))");

        eval_test("K", "K");
        eval_test("KK", "(KK)");
        eval_test("SKSK", "K");

        eval_test("SII(I)", "I");

        eval_test("SIKKI", "(KK)");
        eval_test("((K(SI))K)", "(SI)");

        eval_test("(K(SI))", "(K(SI))");
        eval_test("(S(K(SI)))", "(S(K(SI)))");
        eval_test("(S(K(SI))K)", "(S(K(SI))K)");

        eval_test("(S(K(SI))K)KI", "K");
        eval_test("((K(SI))K)KKI", "(KK)");

        eval_test("((K(SI))K)KK", "(K(KK))");

        eval_test("(((K(SI))K)K)", "(SIK)");
        eval_test("((((K(SI))K)K)K)", "(K(KK))");

        eval_test("((SII)(SII))", "(SII(SII))");

        // these pass
        eval_test("SIK(K)", "(K(KK))");
        eval_test("K(K)K", "K");
        eval_test("((K(SI))K)K", "(SIK)");
        eval_test("SIKK", "(K(KK))");
        eval_test("SIKKK", "(KK)");
        eval_test("(K(SI))K", "(SI)");
        eval_test("(SI)KKI", "(KK)");
        eval_test("(KK)KKI", "K");

        // boolean
        let t = &"K";
        let f = &"(SK)";
        let not = format!("({f})({t})");
        let not_t = format!("({t}){not}");
        let not_f = format!("({f}){not}");
        let or = format!("{t}");
        let and = format!("{f}");

        eval_test(&not_t, &format!("{f}"));
        eval_test(&not_f, &format!("{t}"));

        let t_and_t = format!("({t})({t})({and})");
        let t_and_f = format!("({t})({f})({and})");
        let f_and_f = format!("({f})({f})({and})");
        let f_and_t = format!("({f})({t})({and})");
        eval_test(&t_and_t, t);
        eval_test(&t_and_f, f);
        eval_test(&f_and_f, f);
        eval_test(&f_and_t, f);

        let t_or_t = format!("({t})({or})({t})");
        let t_or_f = format!("({t})({or})({f})");
        let f_or_f = format!("({f})({or})({f})");
        let f_or_t = format!("({f})({or})({t})");
        eval_test(&t_or_t, t);
        eval_test(&t_or_f, t);
        eval_test(&f_or_f, f);
        eval_test(&f_or_t, t);
    }
}
