# How does Loam work :sob: 

## Prove-time example execution

Evaluation of `(map-double ((1 . 2) . (2 . 4)))` from [`allocation.rs`](allocation.rs) as toy example.

```rust
let A = (1 . 2);
let B = (2 . 4);
let C = (4 . 8);
let X = ((1 . 2) . (2 . 4));
let Y = ((2 . 4) . (4 . 8));

output_expr(WideTag(Y), Digest(Y)) <-- 
    output_ptr(Ptr(Y)) ^ // [x]
    ptr_digest(Ptr(Y), Digest(Y)) // [x]

output_ptr(Addr(Y)) <-- 
    input_ptr(Addr(X)) ^ // non-deterministic input
    map_double(Addr(X), Addr(Y)) // [x]

ptr_digest(Addr(Y), Digest(Y)) <-- 
    cons_digest_mem(Digest(Y), Addr(Y))  // [x]

cons_digest_mem(Digest(Y), Addr(Y)) <--
    cons_mem(Addr(B), Addr(C), Addr(Y)) ^ // non-deterministic input (or pre-allocated)
    ptr_digest(Addr(B), Digest(B)) ^  // [x]
    ptr_digest(Addr(C), Digest(C)) ^  // [x]
    hash4_rel(Cons, Digest(B), Cons, Digest(C), Digest(Y)) // directly proved

ptr_digest(Addr(B), Digest(B)) <-- 
    cons_digest_mem(Digest(B), Addr(B)) // [x]

cons_digest_mem(Digest(B), Addr(B)) <--
    cons_mem(Addr(2), Addr(4), Addr(B)) ^ // non-deterministic input
    ptr_digest(Addr(2), Digest(2)) ^ // directly proved
    ptr_digest(Addr(4), Digest(4)) ^ // directly proved
    hash4_rel(Num, Digest(2), Num, Digest(4), Digest(B)) // directly proved

ptr_digest(Addr(C), Digest(C)) <-- 
    cons_digest_mem(Digest(C), Addr(C)) // [x]

cons_digest_mem(Digest(C), Addr(C)) <--
    cons_mem(Addr(4), Addr(8), Addr(C)) ^ // non-deterministic input
    ptr_digest(Addr(4), Digest(4)) ^ // directly proved
    ptr_digest(Addr(8), Digest(8)) ^ // directly proved
    hash4_rel(Num, Digest(4), Num, Digest(8), Digest(C)) // directly proved

map_double(Addr(X), Addr(Y)) <--
    cons_rel(Addr(A), Addr(B), Addr(X)) ^ // [x]
    cons_rel(Addr(B), Addr(C), Addr(Y)) ^ // [x]
    map_double(Addr(A), Addr(B)) ^ // [x]
    map_double(Addr(B), Addr(C)) // [x]

cons_rel(Addr(A), Addr(B), Addr(X)) <-- 
    cons_mem(Addr(A), Addr(B), Addr(X)) ^ // non-deterministic input

cons_rel(Addr(B), Addr(C), Addr(Y)) <-- 
    cons_mem(Addr(B), Addr(C), Addr(Y)) ^ // non-deterministic input

map_double(Addr(A), Addr(B)) <--
    cons_rel(Addr(1), Addr(2), Addr(A)) ^ // [x]
    cons_rel(Addr(2), Addr(4), Addr(B)) ^ // [x]
    map_double(Addr(1), Addr(2)) ^ // directly proved
    map_double(Addr(2), Addr(4)) // directly proved

cons_rel(Addr(1), Addr(2), Addr(A)) <-- 
    cons_mem(Addr(1), Addr(2), Addr(A)) ^ // non-deterministic input

cons_rel(Addr(2), Addr(4), Addr(B)) <-- 
    cons_mem(Addr(2), Addr(4), Addr(B)) ^ // non-deterministic input

map_double(Addr(B), Addr(C)) <--
    cons_rel(Addr(2), Addr(4), Addr(B)) ^ // [x]
    cons_rel(Addr(4), Addr(8), Addr(C)) ^ // [x]
    map_double(Addr(2), Addr(4)) ^ // directly proved
    map_double(Addr(4), Addr(8)) // directly proved

cons_rel(Addr(4), Addr(8), Addr(C)) <-- 
    cons_mem(Addr(4), Addr(8), Addr(C)) // non-deterministic input
```

Things to note:
1. Addresses of relational memory are nondeterministically provided.
2. There are no signal relations and rules!!
3. The user who provided the memory deduplicated the `(2 . 4)` pointers.
4. Many relations are directly proved -- I don't know how this would be implemented in practice, though.
5. The given memory is ideal -- there's no duplicated pointers. 
6. Furthermore, if the given memory had bad pointers, then these constraints are sufficient to stop the prover from generating a proof.

## Za plan

First, hand-write all of the Lair chips.

```rust
loam fn output_expr_rule(ptr: [2], digest: [8]) : [0] {
    // At prove-time, the prover has to provide the correct `provide!`s from the correct source.
    require!(output_ptr, ptr); 
    require!(ptr_digest, ptr, digest);
    let zeros = [0; 7];
    let (tag, addr) = ptr;
    let wide_tag = (tag, zeros);
    provide!(output_expr, wide_tag, digest); // This will be hardcoded to output to `public_values` in `QueryRecord`
}

loam fn output_ptr_rule(input: [2], output: [2]) : [0] {
    require!(input_ptr, input); 
    require!(map_double, input, output);
    provide!(output_ptr, output);
}

loam fn ptr_digest_cons_rule(addr: [1], digest: [8]) : [0] {
    require!(cons_digest_mem, digest, addr);
    let ptr = (Tag::Cons, addr);
    provide!(ptr_digest, ptr, digest);
}

loam fn cons_digest_mem_rule(
    car: [2], 
    car_digest: [8], 
    cdr: [2], 
    cdr_digest: [8],
    cons_addr: [1],
    cons_digest: [8],
) : [0] {
    require!(cons_mem, car, cdr, cons_addr); // pre-allocated and loaded?
    require!(ptr_digest, car, car_digest);
    require!(ptr_digest, cdr, cdr_digest);
    let zeros = [0; 7];
    let (car_tag, car_addr) = car;
    let (cdr_tag, cdr_addr) = cdr;
    let car_wide_tag = (car_tag, zeros);
    let cdr_wide_tag = (cdr_tag, zeros);
    require!(hash4_rel, car_wide_tag, car_digest, cdr_wide_tag, cdr_digest, cons_digest);
    provide!(cons_digest_mem, cons_digest, cons_addr);
}

loam fn map_double_cons_rule(
    in: [2], 
    out: [2], 
    car_in: [2], 
    car_out: [2], 
    cdr_in: [2], 
    cdr_out: [2],
) : [0] {
    require!(cons_rel(car_in, cdr_in, in));
    require!(map_double(car_in, car_out));
    require!(map_double(cdr_in, cdr_out));
    require!(cons_rel(car_out, cdr_out, out));
    provide!(map_double(in, out));
}

loam fn cons_rel_rule(car: [2], cdr: [2], addr: [1]) : [0] {
    require!(cons_mem(car, cdr, addr));
    let cons = (Tag::Cons, addr);
    provide!(cons_rel, car, cdr, cons);
}

loam fn map_double_num_rule(in: [1], out: [1]) : [0] {
    assert_eq!(2 * in, out);
    provide!(map_double, in, out);
}

// TODO: this might be overconstrained, maybe can replace `ptr` with just `addr` and drop the `assert_eq!(addr, value)`
loam fn ptr_digest_num_rule(ptr: [2], digest: [8]) : [0] {
    let (value, zeros: [7]) = digest;
    let (tag, addr) = ptr;
    assert_eq!(tag, Tag::Num);
    assert_eq!(addr, value); // For Nums, the address is the digest.
    provide!(ptr_digest, addr, digest);
}

// TODO: this might be overconstrained, maybe can drop `digest` arg
loam fn hash4_rel_rule(preimg: [32], digest: [8]) : [0] {
    let img = extern_call(hasher4, preimg);
    assert_eq!(img, digest);
    provide!(hash4_rel, preimg, img);
}
```

Question: How to implement `require!` and `provide!`?

- Syntax is `require!(relation_X(args, ...))`.
- Need a `LoamRelation(relation_idx, args, ...)`.

Next, write some glue to generate the correct `QueryRecords`.

Finally, make a proof!