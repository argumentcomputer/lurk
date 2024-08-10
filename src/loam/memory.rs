use ascent::Dual;
use itertools::Itertools;
use p3_field::{AbstractField, PrimeField32};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    loam::{allocation::Allocator, LEWrap, Num, Ptr, PtrEq, Wide, WidePtr, LE},
    lurk::{
        chipset::LurkChip,
        state::{StateRcCell, LURK_PACKAGE_SYMBOLS_NAMES},
        tag::Tag,
        zstore::{self, builtin_vec, lurk_zstore, ZPtr, ZStore},
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

    pub num: Vec<(Ptr,)>,
}

impl Memory {
    pub fn initial_builtin_relation() -> Vec<(Wide, Dual<LEWrap>)> {
        let zstore = &mut lurk_zstore();
        builtin_vec()
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let ZPtr { tag, digest } = zstore.intern_symbol(name);

                (Wide(digest), Dual(LEWrap(LE::from_canonical_u64(i as u64))))
            })
            .collect()
    }

    pub fn initial_builtin_addr() -> LE {
        LE::from_canonical_u64(LURK_PACKAGE_SYMBOLS_NAMES.len() as u64)
    }

    pub fn initial_nil_relation() -> Vec<(Wide, Dual<LEWrap>)> {
        let zstore = &mut lurk_zstore();
        let ZPtr { tag: _, digest } = zstore.intern_nil();
        vec![(Wide(digest), Dual(LEWrap(LE::from_canonical_u64(0u64))))]
    }

    pub fn initial_nil_addr() -> LE {
        LE::from_canonical_u64(1)
    }

    pub fn initial_tag_relation() -> Vec<(LE, Wide)> {
        Tag::wide_relation()
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
        self.0.1
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
/// Physical pointer
struct PPtr(Ptr);



impl PPtr {
    fn new(tag: Tag, addr: u32) -> Self {
        PPtr(Ptr(tag.elt(), LE::from_canonical_u32(addr)))
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
        self.0.1
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PPtrType {
    Tuple2(PPtr, PPtr),
    Tuple3(PPtr, PPtr, PPtr),
}

impl PPtrType {
    fn get2(self) -> (PPtr, PPtr) {
        match self {
            PPtrType::Tuple2(x, y) => (x, y),
            PPtrType::Tuple3(_, _, _) => panic!(),
        }
    }

    fn get3(self) -> (PPtr, PPtr, PPtr) {
        match self {
            PPtrType::Tuple2(_, _) => panic!(),
            PPtrType::Tuple3(x, y, z) => (x, y, z),
        }
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct RawMemory {
    pub ptr_value: FxHashMap<VPtr, Wide>,

    pub cons_rel: Vec<(VPtr, VPtr, VPtr)>,
    pub fun_rel: Vec<(VPtr, VPtr, VPtr, VPtr)>,
    pub thunk_rel: Vec<(VPtr, VPtr, VPtr)>,
    pub num: Vec<(VPtr,)>,

    pub cons_rel_map: FxHashMap<VPtr, (VPtr, VPtr)>,
    pub fun_rel_map: FxHashMap<VPtr, (VPtr, VPtr, VPtr)>,
    pub thunk_rel_map: FxHashMap<VPtr, (VPtr, VPtr)>,
}

impl RawMemory {
    pub fn distill(&self) -> Memory {
        let mut store = Store::default();
        store.intern_raw_memory(&self);
        store.reconstuct_memory()
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
struct Store {
    pub allocator: Allocator,

    pub dag: FxHashMap<PPtr, (PPtrType, Option<Wide>)>,
    pub inv_dag: FxHashMap<(Tag, PPtrType), PPtr>,

    /// These are opaque pointers that only have digests.
    pub pptr_digest: FxHashMap<PPtr, Wide>,

    /// Virtual to physical address translation.
    pub vptr_pptr: FxHashMap<VPtr, PPtr>,
}

impl Store {
    fn intern_tuple2(&mut self, tag: Tag, p1: PPtr, p2: PPtr) -> PPtr {
        let ptr_type = PPtrType::Tuple2(p1, p2);

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
        let ptr_type = PPtrType::Tuple3(p1, p2, p3);

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
    fn intern_ptr(&mut self, vptr: VPtr, memory: &RawMemory) -> PPtr {
        if let Some(ptr) = self.vptr_pptr.get(&vptr) {
            return *ptr;
        }

        let tag = vptr.tag();
        match tag {
            Tag::Cons => {
                let (vcar, vcdr) = memory
                    .cons_rel_map
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
                let (vargs, vbody, vclosed_env) = memory
                    .fun_rel_map
                    .get(&vptr)
                    .expect("dangling virtual pointer");

                let args = self.intern_ptr(*vargs, memory);
                let body = self.intern_ptr(*vbody, memory);
                let closed_env = self.intern_ptr(*vclosed_env, memory);
                let ptr = self.intern_tuple3(Tag::Fun, args, body, closed_env);
                self.vptr_pptr.insert(vptr, ptr);
                // println!("v->p: {:?} -> {:?}", vptr, ptr);
                ptr
            }
            Tag::Thunk => {
                let (vbody, vclosed_env) = memory
                    .thunk_rel_map
                    .get(&vptr)
                    .expect("dangling virtual pointer");

                let body = self.intern_ptr(*vbody, memory);
                let closed_env = self.intern_ptr(*vclosed_env, memory);
                let ptr = self.intern_tuple2(Tag::Thunk, body, closed_env);
                self.vptr_pptr.insert(vptr, ptr);
                // println!("v->p: {:?} -> {:?}", vptr, ptr);
                ptr
            }
            Tag::Sym => PPtr(vptr.0),
            Tag::Nil => PPtr(vptr.0),
            Tag::Num => PPtr(vptr.0),
            Tag::Err => PPtr(vptr.0),
            Tag::Builtin => PPtr(vptr.0),
            _ => panic!("unimplemented: {:?}", &vptr),
        }
    }

    fn intern_digest(&mut self, vptr: VPtr, digest: Wide, memory: &RawMemory) -> PPtr {
        let tag = vptr.tag();
        let ptr = self.vptr_pptr.get(&vptr).copied().unwrap_or_else(|| {
            // let addr = if tag == Tag::Num {
            //     vptr.0.1
            // } else {
            //     self.allocator.alloc_addr(tag.elt(), LE::zero())
            // };

            let ptr = PPtr(vptr.0);
            self.vptr_pptr.insert(vptr, ptr);
            ptr
        });

        if let Some((_, inner)) = self.dag.get_mut(&ptr) {
            *inner = Some(digest);
        } else if let Some(other) = self.pptr_digest.insert(ptr, digest) {
            assert_eq!(digest, other); // if it exists, the digest better be the same
        }
        ptr
    }

    fn intern_raw_memory(&mut self, memory: &RawMemory) {
        for (_, _, cons) in &memory.cons_rel {
            self.intern_ptr(*cons, memory);
        }
        for (_, _, _, fun) in &memory.fun_rel {
            self.intern_ptr(*fun, memory);
        }
        for (_, _, thunk) in &memory.thunk_rel {
            self.intern_ptr(*thunk, memory);
        }

        for (vptr, digest) in &memory.ptr_value {
            self.intern_digest(*vptr, *digest, memory);
        }
    }

    fn reconstuct_memory(self) -> Memory {
        let sorted_memory = self
            .dag
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
                Tag::Thunk => {
                    let (body, closed_env) = ptr_type.get2();
                    memory.thunk_mem.push((body.0, closed_env.0, ptr.addr()));
                    if let Some(digest) = maybe_digest {
                        memory.thunk_digest_mem.push((digest, ptr.addr()));
                    }
                }
                _ => panic!("floating pointer: {:?}", &ptr),
            }
        }

        for (ptr, digest) in self.pptr_digest {
            let tag = ptr.tag();
            match tag {
                Tag::Sym => memory.sym_digest_mem.push((digest, ptr.addr())),
                Tag::Nil => memory.nil_digest_mem.push((digest, ptr.addr())),
                Tag::Builtin => memory.builtin_digest_mem.push((digest, ptr.addr())),
                Tag::Num => memory.num.push((ptr.0,)),
                _ => panic!("unimplemented: {:?}", &ptr),
            }
        }

        memory
    }
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

    fn create_sample_raw_memory() -> RawMemory {
        let mut memory = RawMemory::default();

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
        memory.cons_rel.push((n1, n2, c12));
        memory.cons_rel.push((n4, n8, c48));
        memory.cons_rel_map.insert(c12, (n1, n2));
        memory.cons_rel_map.insert(c48, (n4, n8));

        memory.cons_rel.push((n1, n2, k12));
        memory.cons_rel.push((n4, n8, k48));
        memory.cons_rel_map.insert(k12, (n1, n2));
        memory.cons_rel_map.insert(k48, (n4, n8));

        memory.cons_rel.push((c12, k48, c12_k48));
        memory.cons_rel.push((k12, c48, k12_c48));
        memory.cons_rel_map.insert(c12_k48, (c12, k48));
        memory.cons_rel_map.insert(k12_c48, (k12, c48));

        memory
    }

    #[test]
    fn test_distill_raw_memory() {
        let raw_memory = create_sample_raw_memory();
        let distilled_memory = raw_memory.distill();

        // Check that all cons relations are preserved
        assert_eq!(distilled_memory.cons_mem.len(), 3);
    }

    #[test]
    fn test_distill_with_duplicates() {
        let mut raw_memory = create_sample_raw_memory();
        
        // Add a duplicate cons relation
        let v1 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(1)));
        let v2 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(2)));
        let v3 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(3)));
        raw_memory.cons_rel.push((v1, v2, v3));

        let distilled_memory = raw_memory.distill();

        // Check that duplicates are removed
        assert_eq!(distilled_memory.cons_mem.len(), 2);
    }

    #[test]
    fn test_distill_with_dangling_pointers() {
        let mut raw_memory = create_sample_raw_memory();
        
        // Add a dangling pointer
        let v6 = VPtr(Ptr(Tag::Cons.elt(), LE::from_canonical_u32(6)));
        raw_memory.ptr_value.insert(v6, Wide([LE::from_canonical_u32(60); 8]));

        let distilled_memory = raw_memory.distill();

        // Check that dangling pointers are not included in the distilled memory
        assert_eq!(distilled_memory.cons_digest_mem.len(), 2);
    }

    #[test]
    fn test_distill_empty_memory() {
        let empty_memory = RawMemory::default();
        let distilled_memory = empty_memory.distill();

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
