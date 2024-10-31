use std::cell::RefCell;

use ascent::Dual;
use itertools::Itertools;
use p3_field::{AbstractField, PrimeField32};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    loam::{allocation::Allocator, LEWrap, Num, Ptr, PtrEq, Wide, WidePtr, LE},
    lurk::{
        chipset::LurkChip,
        error::EvalErr,
        state::{StateRcCell, BUILTIN_SYMBOLS},
        tag::Tag,
        zstore::{self, builtin_set, lurk_zstore, ZPtr, ZStore},
    },
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Memory {
    pub cons_digest_mem: Vec<(Wide, LE)>,
    pub cons_mem: Vec<(Ptr, Ptr, LE)>,
    pub fun_digest_mem: Vec<(Wide, LE)>,
    pub fun_mem: Vec<(Ptr, Ptr, Ptr, LE)>,
    pub thunk_digest_mem: Vec<(Wide, LE)>,
    pub thunk_mem: Vec<(Ptr, Ptr, LE)>,

    pub sym_digest_mem: Vec<(Wide, LE)>,
    pub builtin_digest_mem: Vec<(Wide, LE)>,
    pub nil_digest_mem: Vec<(Wide, LE)>,
}

impl Memory {
    fn report_sizes(&self, summary: &mut DistillationSummary) {
        summary.set_distilled_size(Tag::Cons, self.cons_mem.len());
        summary.set_distilled_size(Tag::Fun, self.fun_mem.len());
        summary.set_distilled_size(Tag::Fix, self.thunk_mem.len());
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
/// Virtual pointer
pub struct VPtr(pub Ptr);

impl VPtr {
    fn new(tag: Tag, addr: u32) -> Self {
        VPtr(Ptr(tag.elt(), LE::from_canonical_u32(addr)))
    }

    fn num(addr: u32) -> Self {
        VPtr::new(Tag::Num, addr)
    }

    fn cons(addr: u32) -> Self {
        VPtr::new(Tag::Cons, addr)
    }

    fn fun(addr: u32) -> Self {
        VPtr::new(Tag::Fun, addr)
    }

    fn to_pptr(&self) -> PPtr {
        PPtr(self.0)
    }

    fn tag(&self) -> Tag {
        self.0.tag()
    }

    fn addr(&self) -> LE {
        self.0 .1
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
/// Physical pointer
pub struct PPtr(pub Ptr);

impl PPtr {
    fn new(tag: Tag, addr: u32) -> Self {
        PPtr(Ptr(tag.elt(), LE::from_canonical_u32(addr)))
    }

    fn nil() -> Self {
        PPtr(Ptr::nil())
    }

    fn t() -> Self {
        PPtr(Ptr::t())
    }

    fn num(addr: u32) -> Self {
        PPtr::new(Tag::Num, addr)
    }

    fn cons(addr: u32) -> Self {
        PPtr::new(Tag::Cons, addr)
    }

    fn fun(addr: u32) -> Self {
        PPtr::new(Tag::Fun, addr)
    }

    fn tag(&self) -> Tag {
        self.0.tag()
    }

    fn addr(&self) -> LE {
        self.0 .1
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PPtrKind {
    Tuple2(PPtr, PPtr),
    Tuple3(PPtr, PPtr, PPtr),
}

impl PPtrKind {
    fn get2(self) -> (PPtr, PPtr) {
        match self {
            PPtrKind::Tuple2(x, y) => (x, y),
            PPtrKind::Tuple3(_, _, _) => panic!(),
        }
    }

    fn get3(self) -> (PPtr, PPtr, PPtr) {
        match self {
            PPtrKind::Tuple2(_, _) => panic!(),
            PPtrKind::Tuple3(x, y, z) => (x, y, z),
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct VirtualMemory {
    pub ptr_value: FxHashMap<VPtr, Wide>,

    pub cons_mem: FxHashMap<VPtr, (VPtr, VPtr)>,
    pub fun_mem: FxHashMap<VPtr, (VPtr, VPtr, VPtr)>,
    pub thunk_mem: FxHashMap<VPtr, (VPtr, VPtr)>,
}

impl VirtualMemory {
    fn report_sizes(&self, summary: &mut DistillationSummary) {
        summary.set_original_size(Tag::Cons, self.cons_mem.len());
        summary.set_original_size(Tag::Fun, self.fun_mem.len());
        summary.set_original_size(Tag::Fix, self.thunk_mem.len());
    }

    pub fn distill(&self, options: &DistillationOptions) -> Memory {
        let mut store = Store::default();
        store.intern_virtual_memory(&self);
        let distilled_memory = store.reconstruct_memory();

        if let Some(threshold) = options.summary_threshold {
            let mut summary = DistillationSummary::new(threshold);
            self.report_sizes(&mut summary);
            distilled_memory.report_sizes(&mut summary);
            summary.report();
        }

        distilled_memory
    }

    pub fn distill_with_store(&self, store: &mut Store, options: &DistillationOptions) -> Memory {
        store.intern_virtual_memory(&self);
        let distilled_memory = store.reconstruct_memory();

        if let Some(threshold) = options.summary_threshold {
            let mut summary = DistillationSummary::new(threshold);
            self.report_sizes(&mut summary);
            distilled_memory.report_sizes(&mut summary);
            summary.report();
        }

        distilled_memory
    }
}

///
#[derive(Clone, Default, Debug)]
pub struct DistillationOptions {
    /// If this is `Some`, report a summary that reports the percentage reduction in distillation.
    /// This should alert the user if the percentage ever rises above the given threshold.
    pub summary_threshold: Option<f64>,
}

impl DistillationOptions {
    pub fn new() -> Self {
        DistillationOptions::default()
    }

    pub fn with_summary(mut self, threshold: f64) -> Self {
        self.summary_threshold = Some(threshold);
        self
    }
}

#[derive(Clone, Default, Debug)]
pub struct DistillationSummary {
    threshold: f64,
    original_sizes: FxHashMap<Tag, usize>,
    distilled_sizes: FxHashMap<Tag, usize>,
}

impl DistillationSummary {
    pub fn new(threshold: f64) -> Self {
        DistillationSummary {
            threshold,
            original_sizes: FxHashMap::default(),
            distilled_sizes: FxHashMap::default(),
        }
    }

    pub fn set_original_size(&mut self, tag: Tag, size: usize) {
        self.original_sizes.insert(tag, size);
    }

    pub fn set_distilled_size(&mut self, tag: Tag, size: usize) {
        self.distilled_sizes.insert(tag, size);
    }

    pub fn report(&self) {
        println!("-----------------------------------");
        println!("      Memory Reduction Report      ");
        println!("-----------------------------------");

        let mut total_original = 0;
        let mut total_distilled = 0;

        for (tag, &original) in &self.original_sizes {
            let distilled = self.distilled_sizes[tag];
            let reduction = 1.0 - (distilled as f64 / original as f64);

            println!("{:?}: {:.2}% reduction", tag, reduction * 100.0);
            println!("  Original: {}, Distilled: {}", original, distilled);

            total_original += original;
            total_distilled += distilled;
        }

        let total_reduction = 1.0 - (total_distilled as f64 / total_original as f64);

        println!("\nMem Relations Reduction: {:.2}%", total_reduction * 100.0);
        println!(
            "  Original: {}, Distilled: {}",
            total_original, total_distilled
        );
        println!("-----------------------------------");

        if total_reduction > self.threshold {
            eprintln!(
                "\nWARNING: Memory reduction ({:.2}%) exceeds threshold ({:.2}%)!",
                total_reduction * 100.0,
                self.threshold * 100.0
            );
        }
    }
}

#[derive(Clone, Default)]
pub struct Store {
    pub allocator: Allocator,

    pub dag: FxHashMap<PPtr, (PPtrKind, Option<Wide>)>,
    pub inv_dag: FxHashMap<(Tag, PPtrKind), PPtr>,

    /// These are opaque pointers that only have digests.
    pub pptr_digest: FxHashMap<PPtr, Wide>,

    /// ZPtr to PPtr translation
    pub digest_pptr: FxHashMap<Wide, PPtr>,

    /// Virtual to physical address translation.
    pub vptr_pptr: FxHashMap<VPtr, PPtr>,
}

impl Store {
    fn intern_tuple2(&mut self, tag: Tag, p1: PPtr, p2: PPtr) -> PPtr {
        let ptr_type = PPtrKind::Tuple2(p1, p2);

        if let Some(ptr) = self.inv_dag.get(&(tag, ptr_type)) {
            // println!("{:?} = inv_dag.get({:?})", ptr, ptr_type);
            *ptr
        } else {
            let next_addr = self.allocator.alloc_addr(tag.elt(), LE::zero());
            let ptr = PPtr(Ptr(tag.elt(), next_addr));
            self.dag.insert(ptr, (ptr_type, None));
            self.inv_dag.insert((tag, ptr_type), ptr);
            // println!("dag.insert({:?}, {:?})", ptr, ptr_type);
            ptr
        }
    }

    fn intern_tuple3(&mut self, tag: Tag, p1: PPtr, p2: PPtr, p3: PPtr) -> PPtr {
        let ptr_type = PPtrKind::Tuple3(p1, p2, p3);

        if let Some(ptr) = self.inv_dag.get(&(tag, ptr_type)) {
            *ptr
        } else {
            let addr = self.allocator.alloc_addr(tag.elt(), LE::zero());
            let ptr = PPtr(Ptr(tag.elt(), addr));
            self.dag.insert(ptr, (ptr_type, None));
            self.inv_dag.insert((tag, ptr_type), ptr);
            ptr
        }
    }

    // this is somewhat painful to write
    fn intern_ptr(&mut self, vptr: VPtr, memory: &VirtualMemory) -> PPtr {
        if let Some(ptr) = self.vptr_pptr.get(&vptr) {
            return *ptr;
        }

        match vptr.tag() {
            Tag::Cons => {
                let (vcar, vcdr) = memory
                    .cons_mem
                    .get(&vptr)
                    .expect("dangling virtual pointer");

                let car = self.intern_ptr(*vcar, memory);
                let cdr = self.intern_ptr(*vcdr, memory);
                let ptr = self.intern_tuple2(Tag::Cons, car, cdr);
                self.vptr_pptr.insert(vptr, ptr);
                // println!("v->p: {:?} -> {:?}", vptr, ptr);
                ptr
            }
            Tag::Fun => {
                let (vargs, vbody, vclosed_env) =
                    memory.fun_mem.get(&vptr).expect("dangling virtual pointer");

                let args = self.intern_ptr(*vargs, memory);
                let body = self.intern_ptr(*vbody, memory);
                let closed_env = self.intern_ptr(*vclosed_env, memory);
                let ptr = self.intern_tuple3(Tag::Fun, args, body, closed_env);
                self.vptr_pptr.insert(vptr, ptr);
                // println!("v->p: {:?} -> {:?}", vptr, ptr);
                ptr
            }
            Tag::Fix => {
                let (vbody, vclosed_env) = memory
                    .thunk_mem
                    .get(&vptr)
                    .expect("dangling virtual pointer");

                let body = self.intern_ptr(*vbody, memory);
                let closed_env = self.intern_ptr(*vclosed_env, memory);
                let ptr = self.intern_tuple2(Tag::Fix, body, closed_env);
                self.vptr_pptr.insert(vptr, ptr);
                // println!("v->p: {:?} -> {:?}", vptr, ptr);
                ptr
            }
            Tag::Sym => PPtr(vptr.0),
            Tag::Num => PPtr(vptr.0),
            Tag::Err => PPtr(vptr.0),
            Tag::Builtin => PPtr(vptr.0),
            _ => panic!("unimplemented: {:?}", &vptr),
        }
    }

    fn intern_digest(&mut self, vptr: VPtr, digest: Wide, memory: &VirtualMemory) -> PPtr {
        let tag = vptr.tag();
        let ptr = self.vptr_pptr.get(&vptr).copied().unwrap_or_else(|| {
            let ptr = PPtr(vptr.0);
            self.vptr_pptr.insert(vptr, ptr);
            ptr
        });

        if let Some((_, inner)) = self.dag.get_mut(&ptr) {
            self.digest_pptr.insert(digest, ptr);
            *inner = Some(digest);
        } else if let Some(other) = self.pptr_digest.insert(ptr, digest) {
            assert_eq!(digest, other); // if it exists, the digest better be the same
        } else {
            self.digest_pptr.insert(digest, ptr);
        }

        ptr
    }

    fn intern_virtual_memory(&mut self, memory: &VirtualMemory) {
        for (cons, _) in &memory.cons_mem {
            self.intern_ptr(*cons, memory);
        }
        for (fun, _) in &memory.fun_mem {
            self.intern_ptr(*fun, memory);
        }
        for (thunk, _) in &memory.thunk_mem {
            self.intern_ptr(*thunk, memory);
        }

        for (vptr, digest) in &memory.ptr_value {
            self.intern_digest(*vptr, *digest, memory);
        }
    }

    fn reconstruct_memory(&self) -> Memory {
        let sorted_memory = self
            .dag
            .clone()
            .into_iter()
            .sorted_by_key(|x| x.0)
            .collect::<Vec<_>>();

        let mut memory = Memory::default();

        for (ptr, (ptr_type, maybe_digest)) in sorted_memory {
            let tag = ptr.tag();
            match tag {
                Tag::Cons => {
                    let (car, cdr) = ptr_type.get2();
                    memory.cons_mem.push((car.0, cdr.0, ptr.addr()));
                    if let Some(digest) = maybe_digest {
                        memory.cons_digest_mem.push((digest, ptr.addr()));
                    }
                }
                Tag::Fun => {
                    let (args, body, closed_env) = ptr_type.get3();
                    memory
                        .fun_mem
                        .push((args.0, body.0, closed_env.0, ptr.addr()));
                    if let Some(digest) = maybe_digest {
                        memory.fun_digest_mem.push((digest, ptr.addr()));
                    }
                }
                Tag::Fix => {
                    let (body, closed_env) = ptr_type.get2();
                    memory.thunk_mem.push((body.0, closed_env.0, ptr.addr()));
                    if let Some(digest) = maybe_digest {
                        memory.thunk_digest_mem.push((digest, ptr.addr()));
                    }
                }
                _ => panic!("floating pointer: {:?}", &ptr),
            }
        }

        for (ptr, digest) in &self.pptr_digest {
            let tag = ptr.tag();
            match tag {
                Tag::Sym => memory.sym_digest_mem.push((*digest, ptr.addr())),
                Tag::Builtin => memory.builtin_digest_mem.push((*digest, ptr.addr())),
                Tag::Num => (),
                _ => panic!("unimplemented: {:?}", &ptr),
            }
        }

        memory
    }

    #[inline]
    pub fn fetch_tuple2(&self, ptr: &PPtr) -> (&PPtr, &PPtr) {
        let Some((PPtrKind::Tuple2(a, b), _)) = self.dag.get(ptr) else {
            panic!("Tuple2 data not found on DAG: {:?}", ptr)
        };
        (a, b)
    }

    #[inline]
    pub fn fetch_tuple3(&self, ptr: &PPtr) -> (&PPtr, &PPtr, &PPtr) {
        let Some((PPtrKind::Tuple3(a, b, c), _)) = self.dag.get(ptr) else {
            panic!("Tuple3 data not found on DAG: {:?}", ptr)
        };
        (a, b, c)
    }

    pub fn fetch_list<'a>(&'a self, mut ptr: &'a PPtr) -> (Vec<&PPtr>, Option<&'a PPtr>) {
        assert!(ptr.tag() == Tag::Cons || ptr == &PPtr::nil());
        let mut elts = vec![];
        while ptr.tag() == Tag::Cons {
            let (car, cdr) = self.fetch_tuple2(ptr);
            elts.push(car);
            ptr = cdr;
        }
        if ptr == &PPtr::nil() {
            (elts, None)
        } else {
            (elts, Some(ptr))
        }
    }

    pub fn zptr_ptr(&self, zptr: &ZPtr<LE>) -> Option<Ptr> {
        let digest = Wide(zptr.digest);
        self.digest_pptr.get(&digest).map(|pptr| pptr.0)
    }

    pub fn fmt(&self, zstore: &ZStore<LE, LurkChip>, ptr: &PPtr) -> String {
        match ptr.tag() {
            Tag::Num => format!("{}n", ptr.addr()),
            Tag::Builtin | Tag::BigNum | Tag::Sym | Tag::Key | Tag::Coroutine => self
                .pptr_digest
                .get(ptr)
                .map(|digest| {
                    let zptr = ZPtr {
                        tag: ptr.tag(),
                        digest: digest.0,
                    };
                    zstore.fmt(&zptr)
                })
                .unwrap_or(format!("<Opaque {:?}>", ptr.0)),
            Tag::Cons => {
                let (elts, last) = self.fetch_list(ptr);
                let elts_str = elts.iter().map(|z| self.fmt(zstore, z)).join(" ");
                if let Some(last) = last {
                    format!("({elts_str} . {})", self.fmt(zstore, last))
                } else {
                    format!("({elts_str})")
                }
            }
            Tag::Fun => {
                let (args, body, _) = self.fetch_tuple3(ptr);
                if args == &PPtr::nil() {
                    format!("<Fun () {}>", self.fmt(zstore, body))
                } else {
                    format!(
                        "<Fun {} {}>",
                        self.fmt(zstore, args),
                        self.fmt(zstore, body)
                    )
                }
            }
            Tag::Fix => {
                let (body, ..) = self.fetch_tuple3(ptr);
                format!("<Thunk {}>", self.fmt(zstore, body))
            }
            Tag::Err => format!("<Err {:?}>", EvalErr::from_field(&ptr.addr())),
            _ => unimplemented!(),
        }
    }
}

pub fn initial_builtin_relation() -> Vec<(Wide, Dual<LEWrap>)> {
    let zstore = &mut lurk_zstore();
    builtin_set()
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let ZPtr { tag, digest } = zstore.intern_symbol_no_lang(name);

            (Wide(digest), Dual(LEWrap(LE::from_canonical_u64(i as u64))))
        })
        .collect()
}

pub fn initial_builtin_addr() -> LE {
    LE::from_canonical_u64(BUILTIN_SYMBOLS.len() as u64)
}

pub fn initial_symbol_relation() -> Vec<(Wide, Dual<LEWrap>)> {
    let zstore = &mut lurk_zstore();

    let ZPtr {
        tag: _,
        digest: nil_digest,
    } = *zstore.nil();
    let ZPtr {
        tag: _,
        digest: t_digest,
    } = *zstore.t();
    vec![
        (Wide(nil_digest), Dual(LEWrap(LE::zero()))),
        (Wide(t_digest), Dual(LEWrap(LE::one()))),
    ]
}

pub fn initial_symbol_addr() -> LE {
    LE::from_canonical_u64(2)
}

pub fn initial_nil_relation() -> Vec<(Wide, Dual<LEWrap>)> {
    let zstore = &mut lurk_zstore();
    let ZPtr { tag: _, digest } = *zstore.nil();
    vec![(Wide(digest), Dual(LEWrap(LE::from_canonical_u64(0u64))))]
}

pub fn initial_nil_addr() -> LE {
    LE::from_canonical_u64(1)
}

pub fn initial_tag_relation() -> Vec<(LE, Wide)> {
    Tag::wide_relation()
}

pub fn generate_lisp_program(n: usize, op: &str) -> String {
    let mut program = String::new();

    let x = |i: usize| format!("x{i}");
    let y = |i: usize| format!("y{i}");
    let a = |i: usize| format!("a{i}");
    let b = |i: usize| format!("b{i}");

    // Generate lambda expression and parameters
    program.push_str("((lambda (");
    program.push_str(&(0..n).map(|i| x(i)).join(" "));
    program.push_str(")\n");

    // Generate let bindings
    program.push_str("    (let (");
    for i in 0..n {
        program.push_str(&format!(
            "({} (cons {}n {}n))\n          ",
            y(i),
            2 * i + 1,
            2 * i + 2
        ));
    }
    program.push('\n');

    // Generate first chain of cons
    program.push_str("          (a0 x0)\n          ");
    for i in 0..n - 1 {
        let curr = if i % 2 == 0 { y(i + 1) } else { x(i + 1) };
        program.push_str(&format!(
            "({} (cons {} {}))\n          ",
            a(i + 1),
            a(i),
            curr
        ));
    }
    program.push('\n');

    // Generate second chain of cons
    program.push_str("          (b0 y0)\n          ");
    for i in 0..n - 1 {
        let curr = if i % 2 == 1 { y(i + 1) } else { x(i + 1) };
        program.push_str(&format!(
            "({} (cons {} {}))\n          ",
            b(i + 1),
            b(i),
            curr
        ));
    }
    program.push_str(")\n");

    // Generate equality check
    program.push_str(&format!(
        "\n        ({} {} {})\n    ))\n    ",
        op,
        a(n - 1),
        b(n - 1),
    ));

    // Generate arguments
    for i in 0..n {
        program.push_str(&format!("'({}n . {}n) ", 2 * i + 1, 2 * i + 2));
    }
    program.push_str(")");

    program
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_sample_raw_memory() -> VirtualMemory {
        let mut memory = VirtualMemory::default();

        let n1 = VPtr::num(1);
        let n2 = VPtr::num(2);
        let n4 = VPtr::num(4);
        let n8 = VPtr::num(8);

        let c12 = VPtr::cons(0);
        let c48 = VPtr::cons(1);

        let k12 = VPtr::cons(2);
        let k48 = VPtr::cons(4);

        let c12_k48 = VPtr::cons(5);
        let k12_c48 = VPtr::cons(6);

        // Add some cons relations
        memory.cons_mem.insert(c12, (n1, n2));
        memory.cons_mem.insert(c48, (n4, n8));

        memory.cons_mem.insert(k12, (n1, n2));
        memory.cons_mem.insert(k48, (n4, n8));

        memory.cons_mem.insert(c12_k48, (c12, k48));
        memory.cons_mem.insert(k12_c48, (k12, c48));

        memory
    }

    #[test]
    fn test_distill_raw_memory() {
        let raw_memory = create_sample_raw_memory();
        let options = DistillationOptions::new().with_summary(0.9);
        let distilled_memory = raw_memory.distill(&options);

        // Check that all cons relations are preserved
        assert_eq!(distilled_memory.cons_mem.len(), 3);
    }

    #[test]
    fn test_distill_with_duplicates() {
        let mut raw_memory = create_sample_raw_memory();

        // Add a duplicate cons relation
        let v1 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(0)));
        let v2 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(1)));
        let v3 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(2)));
        raw_memory.cons_mem.insert(v3, (v1, v2));

        let options = DistillationOptions::new().with_summary(0.9);
        let distilled_memory = raw_memory.distill(&options);

        // Check that duplicates are removed
        assert_eq!(distilled_memory.cons_mem.len(), 4);
    }

    #[test]
    fn test_distill_with_dangling_pointers() {
        let mut raw_memory = create_sample_raw_memory();

        // Add a dangling pointer
        let v6 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(6)));
        raw_memory
            .ptr_value
            .insert(v6, Wide([LE::from_canonical_u32(60); 8]));

        let options = DistillationOptions::new().with_summary(0.9);
        let distilled_memory = raw_memory.distill(&options);

        // Check that dangling pointers are not included in the distilled memory
        assert_eq!(distilled_memory.cons_digest_mem.len(), 1);
    }

    #[test]
    fn test_distill_empty_memory() {
        let empty_memory = VirtualMemory::default();
        let options = DistillationOptions::new().with_summary(0.9);
        let distilled_memory = empty_memory.distill(&options);

        assert_eq!(distilled_memory.cons_mem.len(), 0);
        assert_eq!(distilled_memory.fun_mem.len(), 0);
        assert_eq!(distilled_memory.thunk_mem.len(), 0);
        assert_eq!(distilled_memory.cons_digest_mem.len(), 0);
        assert_eq!(distilled_memory.fun_digest_mem.len(), 0);
        assert_eq!(distilled_memory.thunk_digest_mem.len(), 0);
    }

    #[test]
    fn test_generate_lisp_program_n3() {
        let expected = r#"((lambda (x0 x1 x2) 
    (let ((y0 (cons 1n 2n))
          (y1 (cons 3n 4n))
          (y2 (cons 5n 6n))
          
          (a0 x0)
          (a1 (cons a0 y1))
          (a2 (cons a1 x2))
          
          (b0 y0)
          (b1 (cons b0 x1))
          (b2 (cons b1 y2))
          )

        (eq a2 b2)
    )) 
    '(1n . 2n) '(3n . 4n) '(5n . 6n) )"#;

        let result = generate_lisp_program(3, "eq");

        // Normalize whitespace for comparison
        let normalize_whitespace = |s: &str| s.split_whitespace().collect::<Vec<_>>().join(" ");

        assert_eq!(
            normalize_whitespace(&result),
            normalize_whitespace(expected)
        );
    }
}
