use ascent::Dual;
use itertools::Itertools;
use p3_field::{AbstractField, PrimeField32};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    loam::{allocation::Allocator, LEWrap, Num, Ptr, PtrEq, Wide, WidePtr, LE},
    lurk::{
        chipset::LurkChip,
        state::LURK_PACKAGE_SYMBOLS_NAMES,
        tag::Tag,
        zstore::{builtin_vec, lurk_zstore, ZPtr, ZStore},
    },
};

pub trait MemoryType {
    fn get_address(&self) -> LEWrap;
    fn set_address(&mut self, new_address: LEWrap);
    fn update_references(&mut self, address_map: &FxHashMap<LEWrap, LEWrap>);
}

impl MemoryType for (Ptr, Ptr, Dual<LEWrap>) {
    fn get_address(&self) -> LEWrap {
        self.2 .0
    }
    fn set_address(&mut self, new_address: LEWrap) {
        self.2 = Dual(new_address);
    }
    fn update_references(&mut self, address_map: &FxHashMap<LEWrap, LEWrap>) {
        self.0 = Ptr(
            self.0 .0,
            address_map
                .get(&LEWrap(self.0 .1))
                .unwrap_or(&LEWrap(self.0 .1))
                .0,
        );
        self.1 = Ptr(
            self.1 .0,
            address_map
                .get(&LEWrap(self.1 .1))
                .unwrap_or(&LEWrap(self.1 .1))
                .0,
        );
    }
}

impl MemoryType for (Ptr, Ptr, Ptr, Dual<LEWrap>) {
    fn get_address(&self) -> LEWrap {
        self.3 .0
    }
    fn set_address(&mut self, new_address: LEWrap) {
        self.3 = Dual(new_address);
    }
    fn update_references(&mut self, address_map: &FxHashMap<LEWrap, LEWrap>) {
        self.0 = Ptr(
            self.0 .0,
            address_map
                .get(&LEWrap(self.0 .1))
                .unwrap_or(&LEWrap(self.0 .1))
                .0,
        );
        self.1 = Ptr(
            self.1 .0,
            address_map
                .get(&LEWrap(self.1 .1))
                .unwrap_or(&LEWrap(self.1 .1))
                .0,
        );
        self.2 = Ptr(
            self.2 .0,
            address_map
                .get(&LEWrap(self.2 .1))
                .unwrap_or(&LEWrap(self.2 .1))
                .0,
        );
    }
}

pub struct Memory {
    pub cons_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub cons_mem: Vec<(Ptr, Ptr, Dual<LEWrap>)>,
    pub fun_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub fun_mem: Vec<(Ptr, Ptr, Ptr, Dual<LEWrap>)>,
    pub thunk_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub thunk_mem: Vec<(Ptr, Ptr, Dual<LEWrap>)>,

    pub sym_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub builtin_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub nil_digest_mem: Vec<(Wide, Dual<LEWrap>)>,

    pub num: Vec<(Ptr,)>,
}

impl Memory {
    pub fn distill(&mut self) {
        let pointer_digests = self.pointer_digests();
        self.ensure_closure(&pointer_digests);
        self.compact_memory();
        self.partition_memory();
    }

    pub fn check_compact(&self) {
        println!("Checking memory compactness...");

        self.check_memory_type("cons_mem", &self.cons_mem);
        self.check_memory_type("fun_mem", &self.fun_mem);
        self.check_memory_type("thunk_mem", &self.thunk_mem);

        println!("Memory compactness check completed.");
    }

    fn check_memory_type<T: MemoryType>(&self, mem_type: &str, memory: &[(T)]) {
        // Sort memory by address
        let mut sorted_addresses: Vec<_> = memory.iter().map(|item| item.get_address().0).collect();
        sorted_addresses.sort();

        // Check for gaps
        for (i, addr) in sorted_addresses.iter().enumerate() {
            if addr.as_canonical_u32() as usize != i {
                println!("Warning: Mismatch found in {} at index {}", mem_type, i);
                println!("  Expected: {}", i);
                println!("  Actual:   {}", addr.as_canonical_u32());
            }
        }
    }

    fn pointer_digests(&self) -> FxHashMap<Ptr, Wide> {
        let mut map = FxHashMap::default();
        let conses = self.cons_digest_mem.iter().map(|(x, Dual(LEWrap(y)))| {
            let ptr = Ptr(Tag::Cons.elt(), *y);
            (ptr, *x)
        });
        let funs = self.fun_digest_mem.iter().map(|(x, Dual(LEWrap(y)))| {
            let ptr = Ptr(Tag::Fun.elt(), *y);
            (ptr, *x)
        });
        let thunks = self.thunk_digest_mem.iter().map(|(x, Dual(LEWrap(y)))| {
            let ptr = Ptr(Tag::Thunk.elt(), *y);
            (ptr, *x)
        });

        map.extend(conses);
        map.extend(funs);
        map.extend(thunks);
        map
    }

    fn ensure_closure(&mut self, pointer_digests: &FxHashMap<Ptr, Wide>) {
        // TODO: Implement closure logic
        // 1. Create a mapping of digests to addresses
        // 2. Iterate through cons_mem, fun_mem, and thunk_mem
        // 3. For each entry, check if a digest exists and update addresses accordingly
        // 4. Remove duplicate entries
    }

    fn compact_memory(&mut self) {
        println!("Starting memory compaction...");

        let mut allocator = Allocator::default();
        let mut address_map: FxHashMap<Ptr, Ptr> = FxHashMap::default();

        for (_, _, Dual(LEWrap(cons))) in &self.cons_mem {
            let addr = allocator.alloc_addr(Tag::Cons.elt(), LE::zero());
            let old_ptr = Ptr(Tag::Cons.elt(), *cons);
            let new_ptr = Ptr(Tag::Cons.elt(), addr);
            address_map.insert(old_ptr, new_ptr);
        }

        for (_, _, _, Dual(LEWrap(fun))) in &self.fun_mem {
            let addr = allocator.alloc_addr(Tag::Cons.elt(), LE::zero());
            let old_ptr = Ptr(Tag::Cons.elt(), *fun);
            let new_ptr = Ptr(Tag::Cons.elt(), addr);
            address_map.insert(old_ptr, new_ptr);
        }

        for (_, _, Dual(LEWrap(thunk))) in &self.thunk_mem {
            let addr = allocator.alloc_addr(Tag::Cons.elt(), LE::zero());
            let old_ptr = Ptr(Tag::Cons.elt(), *thunk);
            let new_ptr = Ptr(Tag::Cons.elt(), addr);
            address_map.insert(old_ptr, new_ptr);
        }

        // // Compact and update references for all memory types
        // self.compact_and_update_mem(&mut self.cons_mem);
        // self.compact_and_update_mem(&mut self.fun_mem);
        // self.compact_and_update_mem(&mut self.thunk_mem);

        // // Update digest_mem vectors
        // self.update_digest_mem(&mut self.cons_digest_mem, &address_map);
        // self.update_digest_mem(&mut self.fun_digest_mem, &address_map);
        // self.update_digest_mem(&mut self.thunk_digest_mem, &address_map);
        // self.update_digest_mem(&mut self.sym_digest_mem, &address_map);
        // self.update_digest_mem(&mut self.builtin_digest_mem, &address_map);
        // self.update_digest_mem(&mut self.nil_digest_mem, &address_map);

        println!("Memory compaction completed.");
    }

    fn compact_and_update_mem<T: MemoryType>(&mut self, mem: &mut Vec<T>) {
        let mut address_map: FxHashMap<LEWrap, LEWrap> = FxHashMap::default();
        let mut next_address = 0u32;

        // Helper function to get or assign new address
        let mut get_new_address = |old_addr: LEWrap| -> LEWrap {
            *address_map.entry(old_addr).or_insert_with(|| {
                let new_addr = LEWrap(LE::from_canonical_u32(next_address));
                next_address += 1;
                new_addr
            })
        };

        for item in mem.iter_mut() {
            let old_addr = item.get_address();
            let new_addr = get_new_address(old_addr);
            item.set_address(new_addr);
        }

        for item in mem.iter_mut() {
            item.update_references(&address_map);
        }
    }

    fn update_digest_mem(&mut self, digest_mem: &mut Vec<(Wide, Dual<LEWrap>)>) {
        let mut address_map: FxHashMap<LEWrap, LEWrap> = FxHashMap::default();
        let mut next_address = 0u32;

        // Helper function to get or assign new address
        let mut get_new_address = |old_addr: LEWrap| -> LEWrap {
            *address_map.entry(old_addr).or_insert_with(|| {
                let new_addr = LEWrap(LE::from_canonical_u32(next_address));
                next_address += 1;
                new_addr
            })
        };

        *digest_mem = digest_mem
            .iter()
            .map(|(digest, addr)| {
                let new_addr = address_map.get(&addr.0).unwrap_or(&addr.0);
                (*digest, Dual(*new_addr))
            })
            .collect();
    }

    fn partition_memory(&mut self) {
        // TODO: Implement partitioning logic
        // 1. Separate digest-only addresses
        // 2. Reorder memory vectors to ensure digest-only addresses come last
        // 3. Update address mappings accordingly
    }

    fn update_references(&mut self, old_to_new: &FxHashMap<LEWrap, LEWrap>) {
        // TODO: Implement reference updating
        // This helper function will be used in compact_memory and partition_memory
        // to update all references to use new addresses
    }

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

pub enum MPtrType {
    Digest(Wide),
    Tuple2(MPtr, MPtr),
    Tuple3(MPtr, MPtr, MPtr),
    DigestTuple2(Wide, MPtr, MPtr),
    DigestTuple3(Wide, MPtr, MPtr, MPtr),
}

pub struct MPtr {
    tag: Tag,
    address: LE,
}

pub struct Memory2 {
    pub zstore: ZStore<LE, LurkChip>,
    pub dag: FxHashMap<MPtr, MPtrType>,

    pub ptr_value: FxHashMap<Ptr, Wide>,

    pub cons_rel: Vec<(Ptr, Ptr, Ptr)>,
    pub fun_rel: Vec<(Ptr, Ptr, Ptr, Ptr)>,
    pub thunk_rel: Vec<(Ptr, Ptr, Ptr)>,
    pub num: Vec<(Ptr,)>,

    pub sym_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub builtin_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
    pub nil_digest_mem: Vec<(Wide, Dual<LEWrap>)>,
}

// impl Memory2 {
//     // this is somewhat painful to write
//     fn intern_ptr(&mut self, ptr: Ptr) -> ZPtr<LE> {
//         if let Some(zptr) = self.deref(&ptr) {
//             return zptr;
//         }

//         let tag = Tag::from_field(&ptr.0);
//         match tag {
//             Tag::Cons => {
//                 let data = self.cons_rel_indices_2.0.get(&(ptr,)).unwrap();
//                 assert_eq!(data.len(), 1);
//                 let (car, cdr) = data[0];
//                 let car = self.intern_ptr(car);
//                 let cdr = self.intern_ptr(cdr);
//                 let zptr = self.zstore.intern_tuple2(Tag::Cons, car, cdr);
//                 self.ptr_zptr.insert(ptr, zptr);
//                 zptr
//             }
//             Tag::Fun => {
//                 let data = self.fun_rel_indices_3.0.get(&(ptr,)).unwrap();
//                 assert_eq!(data.len(), 1);
//                 let (args, body, closed_env) = data[0];
//                 let args = self.intern_ptr(args);
//                 let body = self.intern_ptr(body);
//                 let closed_env = self.intern_ptr(closed_env);
//                 let zptr = self.zstore.intern_tuple3(Tag::Fun, args, body, closed_env);
//                 self.ptr_zptr.insert(ptr, zptr);
//                 zptr
//             }
//             Tag::Thunk => {
//                 let thunk_map = self
//                     .thunk_rel
//                     .iter()
//                     .map(|x| (x.2, (x.0, x.1)))
//                     .collect::<FxHashMap<_, _>>();
//                 let (body, closed_env) = thunk_map.get(&ptr).unwrap();
//                 let body = self.intern_ptr(*body);
//                 let closed_env = self.intern_ptr(*closed_env);
//                 let zptr = self.zstore.intern_tuple2(Tag::Thunk, body, closed_env);
//                 self.ptr_zptr.insert(ptr, zptr);
//                 zptr
//             }
//             Tag::Sym => self.deref(&ptr).unwrap(), // these should already exist
//             Tag::Nil => self.deref(&ptr).unwrap(),
//             Tag::Num => self.deref_imm(&ptr),
//             Tag::Err => self.deref(&ptr).unwrap(),
//             Tag::Builtin => self.deref(&ptr).unwrap(),
//             _ => panic!("unimplemented: {:?}", &ptr),
//         }
//     }
// }

// ((lambda (x0 x1 x2)
// (let ((y0 (cons 1 2))
// (y1 (cons 3 4))
// (y2 (cons 5 6))

// (a1 (cons x0 y1))
// (a2 (cons a1 x2))

// (b1 (cons y0 x1))
// (b2 (cons b1 y2)))

// (eq a2 b2)
// ))
// '(1 . 2) '(3 . 4) '(5 . 6))
fn generate_lisp_program(n: usize) -> String {
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
            "({} (cons {} {}))\n          ",
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
        "\n        (eq {} {})\n    ))\n    ",
        a(n - 1),
        b(n - 1),
    ));

    // Generate arguments
    for i in 0..n {
        program.push_str(&format!("'({} . {}) ", 2 * i + 1, 2 * i + 2));
    }
    program.push_str(")");

    program
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_lisp_program_n3() {
        let expected = r#"((lambda (x0 x1 x2) 
    (let ((y0 (cons 1 2))
          (y1 (cons 3 4))
          (y2 (cons 5 6))
          
          (a0 x0)
          (a1 (cons a0 y1))
          (a2 (cons a1 x2))
          
          (b0 y0)
          (b1 (cons b0 x1))
          (b2 (cons b1 y2))
          )

        (eq a2 b2)
    )) 
    '(1 . 2) '(3 . 4) '(5 . 6) )"#;

        let result = generate_lisp_program(3);

        // Normalize whitespace for comparison
        let normalize_whitespace = |s: &str| s.split_whitespace().collect::<Vec<_>>().join(" ");

        assert_eq!(
            normalize_whitespace(&result),
            normalize_whitespace(expected)
        );
    }
}
