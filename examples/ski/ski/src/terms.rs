#![allow(non_snake_case)]
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt::Formatter;
use std::hash::Hash;
use std::io;
use std::str::FromStr;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct SKI {
    pub src: String,
}

#[derive(Debug)]
pub struct ParseTermError;

#[derive(Clone, Debug)]
pub struct WithMultiplicity<T: Clone>(T, usize);

impl<T: Clone> WithMultiplicity<T> {
    // When preallocating, there is no corresponding access, so multiplicity starts from 0.
    pub fn preallocate(thing: T) -> Self {
        Self(thing, 0)
    }

    // When creating upon first access, that access counts, so multiplicity starts from 1.
    pub fn first_access(thing: T) -> Self {
        Self(thing, 1)
    }

    pub fn query_value(&mut self) -> T {
        self.1 += 1;
        self.0.clone()
    }
    pub fn multiplicity(&self) -> usize {
        self.1
    }
}

impl FromStr for SKI {
    type Err = ParseTermError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self { src: s.into() })
    }
}

impl std::fmt::Display for SKI {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.src)
    }
}

type Addr = usize;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    S(Addr),
    S1(Addr, Addr),
    S2(Addr, Addr, Addr),
    S3(Addr, Addr, Addr, Addr),

    K(Addr),
    K1(Addr, Addr),
    K2(Addr, Addr, Addr),

    I(Addr),
    I1(Addr, Addr),

    Cons(Addr, Addr, Addr),
    Nil,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Reduce(Term),
    Apply(Term, Term),
    Eval(Term),
}

impl Op {
    fn is_reduce(&self) -> bool {
        matches!(self, Self::Reduce(_))
    }
    fn is_apply(&self) -> bool {
        matches!(self, Self::Apply(_, _))
    }
    fn is_eval(&self) -> bool {
        matches!(self, Self::Eval(_))
    }
}

#[derive(Clone, Debug)]
pub struct Step {
    op: Op,
    out: Term,
    depth: usize,
}

impl Op {
    pub fn fmt_to_string(&self, mem: &Mem) -> String {
        let mut out = Vec::new();
        self.fmt(mem, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    pub fn fmt<W: io::Write>(&self, mem: &Mem, w: &mut W) -> Result<(), io::Error> {
        match self {
            Op::Reduce(term) => {
                write!(w, "Reduce ")?;
                term.fmt(mem, w)
            }
            Op::Eval(term) => {
                write!(w, "Eval ")?;
                term.fmt(mem, w)
            }
            Op::Apply(left, right) => {
                write!(w, "Apply ")?;
                left.fmt(mem, w)?;
                write!(w, "<-[")?;
                right.fmt(mem, w)?;
                write!(w, "] ")
            }
        }
    }
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

        self.op.fmt(mem, w)?;
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

const S_ADDR: usize = 0;
const K_ADDR: usize = 1;
const I_ADDR: usize = 2;
const NIL_ADDR: usize = 3;

fn setup(op: Op, mem: &mut Mem, depth: usize) -> (usize, Option<Term>) {
    let mut found = None;
    mem.memo.entry(op.clone()).and_modify(|e| {
        e.1 += 1;
        found = Some(e.0.clone());
    });

    let step = Step {
        op,
        // Placeholder: this will be updated when output is known.
        out: found.clone().unwrap_or_else(|| mem.I()),
        depth,
    };
    mem.steps.push(step);

    (mem.steps.len() - 1, found)
}

fn finalize(op: Op, step_index: usize, mem: &mut Mem, result: Term) {
    mem.steps[step_index].out = result.clone();

    mem.memo
        .entry(op)
        // Just in case it was inserted in the body, after setup.
        .and_modify(|e| {
            // `query_value` increments multiplicity.
            assert_eq!(result, e.query_value());

            unreachable!("This should never happen.");
        })
        .or_insert_with(|| WithMultiplicity::first_access(result));
}

macro_rules! with_memo {
    ($op:expr,
     ($mem:ident, $depth:ident, $result:ident),
     $body:expr) => {{
        let op = $op;
        let (step_index, found) = setup(op.clone(), $mem, $depth);
        if let Some(found) = found {
            found
        } else {
            let $result = $body;
            finalize(op, step_index, $mem, $result.clone());
            $result
        }
    }};
}

impl Term {
    pub fn is_s(&self) -> bool {
        matches!(
            self,
            Self::S(_) | Self::S1(_, _) | Self::S2(_, _, _) | Self::S3(_, _, _, _)
        )
    }
    pub fn is_k(&self) -> bool {
        matches!(self, Self::K(_) | Self::K1(_, _) | Self::K2(_, _, _))
    }
    pub fn is_i(&self) -> bool {
        matches!(self, Self::I(_) | Self::I1(_, _))
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
            Self::S(addr) => *addr,
            Self::S1(addr, _) => *addr,
            Self::S2(addr, _, _) => *addr,
            Self::S3(addr, _, _, _) => *addr,
            Self::K(addr) => *addr,
            Self::K1(addr, _) => *addr,
            Self::K2(addr, _, _) => *addr,
            Self::I(addr) => *addr,
            Self::I1(addr, _) => *addr,
            Self::Cons(addr, _, _) => *addr,
            Self::Nil => NIL_ADDR,
        }
    }

    fn first(&self, mem: &Mem) -> (Self, Option<Self>) {
        match self {
            Self::Cons(_, first, rest) => {
                let rest_term = mem.get_term(*rest);
                let tail = match rest_term {
                    Self::Nil => None,
                    _ => Some(rest_term),
                };
                let first_term = mem.get_term(*first);
                assert!(first_term != Term::Nil);
                (first_term, tail)
            }
            _ => {
                panic!("first called on non-cons")
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
                        let term = mem.list(&inner);
                        inner = stack.pop().ok_or(ParseTermError)?;
                        inner.push(term.addr());
                    }
                    _ => Err(ParseTermError)?,
                };
            }
            if inner.len() == 1 {
                Ok(mem.get_term(inner[0]))
            } else {
                Ok(mem.list(&inner))
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
            Self::S(_) => {
                write!(w, "S")
            }
            Self::S1(_, x) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::S2(_, x, y) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::S3(_, x, y, z) => {
                write!(w, "(S")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                mem.borrow_term(*z).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::K(_) => {
                write!(w, "K")
            }
            Self::K1(_, x) => {
                write!(w, "(K")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::K2(_, x, y) => {
                write!(w, "(K")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                mem.borrow_term(*y).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::I(_) => {
                write!(w, "I")
            }
            Self::I1(_, x) => {
                write!(w, "(I")?;
                mem.borrow_term(*x).fmt(mem, w)?;
                write!(w, ")")
            }
            Self::Cons(_, first, rest) => {
                write!(w, "(")?;
                mem.borrow_term(*first).fmt(mem, w)?;

                let mut tail = rest.clone();
                loop {
                    match mem.borrow_term(tail) {
                        Term::Cons(_, first, rest) => {
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

    fn reduce(self, mem: &mut Mem, depth: usize) -> Self {
        with_memo!(Op::Reduce(self.clone()), (mem, depth, result), {
            match self {
                Self::S3(_, x, y, z) => {
                    // Q: Do we need to eval x too?
                    //
                    // Some of these `eval`s could probably be just `reduce`s, and that would
                    // reduce the amount of work performed. However, if we get it wrong that might
                    // result in some terms not being fully reduced. So for now, we will just conservatively
                    // fully evaluate all sub-terms before performing the reduction.
                    let ix = mem.get_term(x);
                    let evaled_y = mem.get_term(y).eval(mem, depth + 1);
                    let evaled_z = mem.get_term(z).eval(mem, depth + 1);
                    let xz = ix
                        .apply(mem, evaled_z.clone(), depth + 1)
                        .eval(mem, 1 + depth)
                        .clone();
                    let yz = evaled_y
                        .apply(mem, evaled_z, depth + 1)
                        .eval(mem, depth + 1)
                        .clone();
                    xz.apply(mem, yz, depth + 1)
                }
                Self::K2(_, x, _) => mem.get_term(x),
                Self::I1(_, x) => mem.get_term(x),
                Self::Cons(_, first, rest) => {
                    let first = mem.get_term(first);
                    let first_evaled = first.clone().eval(mem, depth + 1);
                    let rest = mem.get_term(rest);

                    if rest == Term::Nil {
                        if first_evaled == first {
                            first_evaled
                        } else {
                            mem.cons(first_evaled, Self::Nil)
                        }
                    } else {
                        let (second, tail) = rest.first(mem);
                        let second_evaled = second.clone().eval(mem, depth + 1);
                        let applied = first_evaled.clone().apply(mem, second_evaled, depth + 1);

                        mem.cons(applied, tail.unwrap_or(Self::Nil))
                    }
                }
                Self::Nil => unreachable!(),
                _ => self,
            }
        })
    }

    pub fn eval(self, mem: &mut Mem, depth: usize) -> Self {
        with_memo!(Op::Eval(self.clone()), (mem, depth, result), {
            let reduced = self.clone().reduce(mem, depth + 1);

            if reduced == self {
                reduced
            } else {
                reduced.eval(mem, depth + 1)
            }
        })
    }

    fn apply(self, mem: &mut Mem, a: Self, depth: usize) -> Self {
        with_memo!(
            Op::Apply(self.clone(), a.clone()),
            (mem, depth, result),
            match self {
                Self::S(_) => mem.S1(a.addr()),
                Self::S1(_, x) => mem.S2(x, a.addr()),
                Self::S2(_, x, y) => mem.S3(x, y, a.addr()),
                Self::K(_) => mem.K1(a.addr()),
                Self::K1(_, x) => mem.K2(x, a.addr()),
                Self::I(_) => mem.I1(a.addr()),
                Self::I1(_, x) => mem.get_term(x).apply(mem, a, depth + 1),
                Self::Cons(_, _, _) => {
                    let applied = self.clone().eval(mem, depth + 1).apply(mem, a, depth + 1);
                    applied
                }
                _ => unreachable!(),
            }
        )
    }
}

#[derive(Debug, Default)]
pub struct Mem {
    terms: Vec<WithMultiplicity<Term>>,
    steps: Vec<Step>,
    memo: HashMap<Op, WithMultiplicity<Term>>,
    s1: HashMap<Addr, Addr>,
    s2: HashMap<(Addr, Addr), Addr>,
    s3: HashMap<(Addr, Addr, Addr), Addr>,
    k1: HashMap<Addr, Addr>,
    k2: HashMap<(Addr, Addr), Addr>,
    i1: HashMap<Addr, Addr>,
    conses: HashMap<(Addr, Addr), Addr>,
}

impl Mem {
    pub fn new() -> Self {
        let mut mem = Mem::default();
        mem.terms = vec![
            WithMultiplicity::preallocate(Term::S(S_ADDR)),
            WithMultiplicity::preallocate(Term::K(K_ADDR)),
            WithMultiplicity::preallocate(Term::I(I_ADDR)),
            WithMultiplicity::preallocate(Term::Nil),
        ];

        for (i, WithMultiplicity(term, _)) in mem.terms.iter().enumerate() {
            assert_eq!(i, term.addr());
        }

        mem
    }

    pub fn input(&self) -> Term {
        match &self.steps[0].op {
            Op::Eval(input) => input.clone(),
            _ => panic!("Mem does not describe a toplevel evaluation."),
        }
    }

    pub fn output(&self) -> Term {
        self.steps[0].out.clone()
    }

    pub fn eval_steps(&self) -> Vec<Step> {
        self.steps
            .iter()
            .filter(|step| step.op.is_eval())
            .cloned()
            .collect()
    }

    pub fn reduce_steps(&self) -> Vec<Step> {
        self.steps
            .iter()
            .filter(|step| step.op.is_reduce())
            .cloned()
            .collect()
    }

    pub fn apply_steps(&self) -> Vec<Step> {
        self.steps
            .iter()
            .filter(|step| step.op.is_apply())
            .cloned()
            .collect()
    }

    pub fn borrow_term(&self, addr: Addr) -> &Term {
        &self.terms[addr].0
    }

    pub fn get_term(&self, addr: Addr) -> Term {
        self.terms[addr].0.clone()
    }

    pub fn query(&self, op: Op) -> Option<Term> {
        // TODO: this should be indexed to avoid the expensive scan.
        if let Some(found) = self.steps.iter().find(|step| step.op == op) {
            Some(found.out.clone())
        } else {
            None
        }
    }

    pub fn assert_memo_steps_consistency(&self) {
        for step in &self.steps {
            assert!(self.memo.get(&step.op).is_some());
        }
    }

    // NOTE: The clones are shallow.
    pub fn S(&mut self) -> Term {
        self.terms[0].query_value().clone()
    }
    pub fn K(&mut self) -> Term {
        self.terms[1].query_value().clone()
    }
    pub fn I(&mut self) -> Term {
        self.terms[2].query_value().clone()
    }

    pub fn S1(&mut self, x_addr: Addr) -> Term {
        if let Some(found) = self.s1.get(&x_addr) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::S1(addr, x_addr));
            self.s1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn S2(&mut self, x_addr: Addr, y_addr: Addr) -> Term {
        if let Some(found) = self.s2.get(&(x_addr, y_addr)) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::S2(addr, x_addr, y_addr));
            self.s2.insert((x_addr, y_addr), addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn S3(&mut self, x_addr: Addr, y_addr: Addr, z_addr: Addr) -> Term {
        if let Some(found) = self.s3.get(&(x_addr, y_addr, z_addr)) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::S3(addr, x_addr, y_addr, z_addr));
            self.s3.insert((x_addr, y_addr, z_addr), addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn K1(&mut self, x_addr: Addr) -> Term {
        if let Some(found) = self.k1.get(&x_addr) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::K1(addr, x_addr));
            self.k1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn K2(&mut self, x_addr: Addr, y_addr: Addr) -> Term {
        if let Some(found) = self.k2.get(&(x_addr, y_addr)) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::K2(addr, x_addr, y_addr));
            self.k2.insert((x_addr, y_addr), addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn I1(&mut self, x_addr: Addr) -> Term {
        if let Some(found) = self.i1.get(&x_addr) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::I1(addr, x_addr));
            self.i1.insert(x_addr, addr);
            self.terms.push(new.clone());
            new.0
        }
    }
    pub fn list(&mut self, addrs: &[Addr]) -> Term {
        if addrs.is_empty() {
            return Term::Nil;
        }
        let first_addr = addrs[0];
        let rest = self.list(&addrs[1..]);

        if let Some(found) = self.conses.get(&(first_addr, rest.addr())) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            if addrs.len() > 1 {
                self.conses.insert((first_addr, rest.addr()), addr);
                let new = WithMultiplicity::first_access(Term::Cons(addr, addrs[0], rest.addr()));
                self.terms.push(new.clone());
                new.0
            } else {
                let new = WithMultiplicity::first_access(Term::Cons(addr, addrs[0], NIL_ADDR));
                self.terms.push(new.clone());
                new.0
            }
        }
    }

    pub fn cons(&mut self, first: Term, rest: Term) -> Term {
        if let Some(found) = self.conses.get(&(first.addr(), rest.addr())) {
            self.terms[*found].query_value().clone()
        } else {
            let addr = self.terms.len();
            let new = WithMultiplicity::first_access(Term::Cons(addr, first.addr(), rest.addr()));
            self.terms.push(new.clone());
            new.0
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn eval_test(input: &str, expected: &str) {
        let mem = &mut Mem::new();
        let term = Term::from_str(mem, input).unwrap();
        let evaled = term.clone().eval(mem, 0);

        if expected != evaled.fmt_to_string(mem) {
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
            let term = Term::from_str(mem, input).unwrap();
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
