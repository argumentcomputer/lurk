# NOTE: This script is a slightly modified version from https://github.com/HorizenLabs/poseidon2/blob/main/poseidon2_rust_params.sage
#       The modifications were made to support generating multiple constants for different t values.
#       A recent modification added generation for efficient partial MDS matrices
from functools import partial
from itertools import product, chain
from math import *
from multiprocessing import Pool

PRIME = 2013265921 # BabyBear
FIELD_SIZE = len(PRIME.bits())

def get_alpha(p):
    for alpha in range(3, p):
        if gcd(alpha, p-1) == 1:
            return alpha
    else:
        # Note: Mathematically this will never happen
        raise Exception(f"No alpha is generated for p = {p}")

def sat_inequiv(p, t, r_f, r_p, alpha, M, field_size):
    if alpha > 0:
        R_F_1 = 6 if M <= ((floor(log(p, 2) - ((alpha-1)/2.0))) * (t + 1)) else 10 # Statistical
        R_F_2 = 1 + ceil(log(2, alpha) * min(M, field_size)) + ceil(log(t, alpha)) - r_p # Interpolation
        R_F_3 = (log(2, alpha) * min(M, log(p, 2))) - r_p # Groebner 1
        R_F_4 = t - 1 + log(2, alpha) * min(M / float(t + 1), log(p, 2) / float(2)) - r_p # Groebner 2
        R_F_5 = (t - 2 + (M / float(2 * log(alpha, 2))) - r_p) / float(t - 1) # Groebner 3
        R_F_max = max(ceil(R_F_1), ceil(R_F_2), ceil(R_F_3), ceil(R_F_4), ceil(R_F_5))

        # Addition due to https://eprint.iacr.org/2023/537.pdf
        r_temp = floor(t / 3.0)
        over = (r_f - 1) * t + r_p + r_temp + r_temp * (r_f / 2.0) + r_p + alpha
        under = r_temp * (r_f / 2.0) + r_p + alpha
        binom_log = log(binomial(over, under), 2)
        if binom_log == inf:
            binom_log = M + 1
        cost_gb4 = ceil(2 * binom_log) # Paper uses 2.3727, we are more conservative here

        return ((r_f >= R_F_max) and (cost_gb4 >= M))
    else:
        raise Exception(f"Unexpected value of alpha: {alpha}")

def find_FD_round_numbers(p, t, alpha, M, cost_function, security_margin, field_size):
    n = ceil(log(p, 2))
    N = int(n * t)

    R_P = 0
    R_F = 0
    min_cost = float("inf")
    max_cost_rf = 0
    # Brute-force approach
    for R_P_t in range(1, 500):
        for R_F_t in range(4, 100):
            if R_F_t % 2 == 0:
                if (sat_inequiv(p, t, R_F_t, R_P_t, alpha, M, field_size) == True):
                    if security_margin == True:
                        R_F_t += 2
                        R_P_t = int(ceil(float(R_P_t) * 1.075))
                    cost = cost_function(R_F_t, R_P_t, N)
                    if (cost < min_cost) or ((cost == min_cost) and (R_F_t < max_cost_rf)):
                        R_P = ceil(R_P_t)
                        R_F = ceil(R_F_t)
                        min_cost = cost
                        max_cost_rf = R_F
    return (int(R_F), int(R_P))

def get_sbox_cost(r_f, r_p, t):
    return int(t * r_f + r_p)

def poseidon_calc_final_numbers_fixed(p, t, alpha, M, security_margin, field_size):
    # [Min. S-boxes] Find best possible for t and N
    n = ceil(log(p, 2))
    N = int(n * t)
    ret_list = []
    (R_F, R_P) = find_FD_round_numbers(p, t, alpha, M, get_sbox_cost, security_margin, field_size)
    min_sbox_cost = get_sbox_cost(R_F, R_P, N)
    ret_list.append(R_F)
    ret_list.append(R_P)
    ret_list.append(min_sbox_cost)

    # [Min. Size] Find best possible for t and N
    # Minimum number of S-boxes for fixed n results in minimum size also (round numbers are the same)!
    min_size_cost = get_sbox_cost(R_F, R_P, N)
    ret_list.append(min_size_cost)

    return ret_list # [R_F, R_P, min_sbox_cost, min_size_cost]

def init_generator(n, t, r_f, r_p):
    # Generate initial sequence based on parameters
    field_tag = 1
    sbox_tag = 0
    bit_list_field = [_ for _ in (bin(field_tag)[2:].zfill(2))]
    bit_list_sbox = [_ for _ in (bin(sbox_tag)[2:].zfill(4))]
    bit_list_n = [_ for _ in (bin(n)[2:].zfill(12))]
    bit_list_t = [_ for _ in (bin(t)[2:].zfill(12))]
    bit_list_R_F = [_ for _ in (bin(r_f)[2:].zfill(10))]
    bit_list_R_P = [_ for _ in (bin(r_p)[2:].zfill(10))]
    bit_list_1 = [1] * 30
    init_sequence = bit_list_field + bit_list_sbox + bit_list_n + bit_list_t + bit_list_R_F + bit_list_R_P + bit_list_1
    init_sequence = [int(_) for _ in init_sequence]

    return init_sequence

def grain_sr_generator(init_sequence):
    bit_sequence = init_sequence
    for _ in range(0, 160):
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)

    while True:
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)
        while new_bit == 0:
            new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
            bit_sequence.pop(0)
            bit_sequence.append(new_bit)
            new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
            bit_sequence.pop(0)
            bit_sequence.append(new_bit)
        new_bit = bit_sequence[62] ^^ bit_sequence[51] ^^ bit_sequence[38] ^^ bit_sequence[23] ^^ bit_sequence[13] ^^ bit_sequence[0]
        bit_sequence.pop(0)
        bit_sequence.append(new_bit)
        yield new_bit

def grain_random_bits(grain_gen, num_bits):
    random_bits = [next(grain_gen) for _ in range(num_bits)]
    random_int = int("".join(str(i) for i in random_bits), 2)

    return random_int

def generate_constants(n, t, r_f, r_p, prime_number, grain_gen):
    full_round_constants = []
    partial_round_constants = []
    num_constants = (r_f * t) + r_p # Poseidon2

    for i in range(num_constants):
        random_int = grain_random_bits(grain_gen, n)
        while random_int >= prime_number:
            random_int = grain_random_bits(grain_gen, n)
        # Add (t-1) zeroes for Poseidon2 if partial round
        if i >= ((r_f/2) * t) and i < (((r_f/2) * t) + r_p):
            partial_round_constants.append(random_int)
        else:
            full_round_constants.append(random_int)
    return (full_round_constants, partial_round_constants)

def check_minpoly_condition(M, num_cells):
    max_period = 2*num_cells
    all_fulfilled = True
    M_temp = M
    for _ in range(max_period):
        if not ((M_temp.minimal_polynomial().degree() == num_cells) and (M_temp.minimal_polynomial().is_irreducible() == True)):
            all_fulfilled = False
            break
        M_temp = M * M_temp
    return all_fulfilled

def generate_vectorspace(round_num, M_round, num_cells, F):
    t = num_cells
    s = 1
    V = VectorSpace(F, t)
    if round_num == 0:
        return V
    elif round_num == 1:
        return V.subspace(V.basis()[s:])
    else:
        mat_temp = matrix(F)
        for i in range(0, round_num-1):
            add_rows = []
            for j in range(0, s):
                add_rows.append(M_round[i].rows()[j][s:])
            mat_temp = matrix(mat_temp.rows() + add_rows)
        r_k = mat_temp.right_kernel()
        extended_basis_vectors = []
        for vec in r_k.basis():
            extended_basis_vectors.append(vector([0]*s + list(vec)))
        S = V.subspace(extended_basis_vectors)

        return S

def subspace_times_matrix(subspace, M, num_cells, F):
    t = num_cells
    V = VectorSpace(F, t)
    subspace_basis = subspace.basis()
    new_basis = []
    for vec in subspace_basis:
        new_basis.append(M * vec)
    new_subspace = V.subspace(new_basis)
    return new_subspace

def algorithm_1(M, num_cells, F):
    t = num_cells
    s = 1
    r = floor((t - s) / float(s))

    # Generate round matrices
    M_round = []
    for j in range(0, t+1):
        M_round.append(M^(j+1))

    for i in range(1, r+1):
        mat_test = M^i
        entry = mat_test[0, 0]
        mat_target = matrix.circulant(vector([entry] + ([F(0)] * (t-1))))

        if (mat_test - mat_target) == matrix.circulant(vector([F(0)] * (t))):
            return [False, 1]

        S = generate_vectorspace(i, M_round, t, F)
        V = VectorSpace(F, t)

        basis_vectors= []
        for eigenspace in mat_test.eigenspaces_right(format='galois'):
            if (eigenspace[0] not in F):
                continue
            vector_subspace = eigenspace[1]
            intersection = S.intersection(vector_subspace)
            basis_vectors += intersection.basis()
        IS = V.subspace(basis_vectors)

        if IS.dimension() >= 1 and IS != V:
            return [False, 2]
        for j in range(1, i+1):
            S_mat_mul = subspace_times_matrix(S, M^j, t, F)
            if S == S_mat_mul:
                print("S.basis():\n", S.basis())
                return [False, 3]

    return [True, 0]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_2(M, num_cells, F):
    t = num_cells
    s = 1

    V = VectorSpace(F, t)
    test_next = False
    I = range(0, s)
    I_powerset = list(sage.combinat.subset.powerset(I))[1:]
    for I_s in I_powerset:
        test_next = False
        new_basis = []
        for l in I_s:
            new_basis.append(V.basis()[l])
        IS = V.subspace(new_basis)
        for i in range(s, t):
            new_basis.append(V.basis()[i])
        full_iota_space = V.subspace(new_basis)
        for l in I_s:
            v = V.basis()[l]
            while True:
                delta = IS.dimension()
                v = M * v
                IS = V.subspace(IS.basis() + [v])
                if IS.dimension() == t or IS.intersection(full_iota_space) != IS:
                    test_next = True
                    break
                if IS.dimension() <= delta:
                    break
            if test_next == True:
                break
        if test_next == True:
            continue
        return [False, [IS, I_s]]

    return [True, None]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_3(M, num_cells, F):
    t = num_cells

    l = 4*t
    for r in range(2, l+1):
        res_alg_2 = algorithm_2(M^r, t, F)
        if res_alg_2[0] == False:
            return [False, None]

    return [True, None]

def generate_matrix_candidate(field_size, num_cells, grain_gen, F):
    return matrix.diagonal([F(grain_random_bits(grain_gen, field_size)) for _ in range(0, num_cells)])

def get_skips(num_cells, num_skips):
    return product(range(num_cells - 2), repeat=num_skips)

def get_diags(num_cells, num_skips, F):
    diags = list()

    for skip_list in get_skips(num_cells, num_skips):
        steps = [0] * num_cells
        for x in skip_list:
            steps[x] += 1

        shift_list = [0, 0]
        for i in range(num_cells - 2):
            shift_list.append(shift_list[-1] + 1 + steps[i])

        new_vect = vector(map(lambda x: F(1 << x), shift_list))
        new_vect[0] = -2
        diags.append(new_vect)

    diags.reverse() # Prioritize checking matrices with smaller entries first

    return diags

def generate_efficient_matrix_candidates(num_cells, num_skips, F) -> list:
    return [matrix.diagonal(F, vect) for vect in get_diags(num_cells, num_skips, F)]

def generate_matrix_partial(field_size, num_cells, grain_gen, F):
    M = None
    if num_cells == 2:
        M = matrix(F, [[F(2), F(1)], [F(1), F(3)]])
    elif num_cells == 3:
        M = matrix(F, [[F(2), F(1), F(1)], [F(1), F(2), F(1)], [F(1), F(1), F(3)]])
    else:
        M_circulant = matrix.circulant(vector([F(0)] + [F(1) for _ in range(num_cells - 1)]))
        for i in range(4): # 4 is a random choice here, but anything bigger would take too long
            candidates = generate_efficient_matrix_candidates(num_cells, i, F)
            for candidate in candidates:
                M = M_circulant + candidate + matrix.identity(F, num_cells)
                if check_minpoly_condition(M, num_cells) == True:
                    return M
        else:
            M_diagonal = generate_matrix_candidate(field_size, num_cells, grain_gen, F)
            M = M_circulant + M_diagonal
            while check_minpoly_condition(M, num_cells) == False:
                M_diagonal = generate_matrix_candidate(field_size, num_cells, grain_gen, F)
                M = M_circulant + M_diagonal

    return M

def final_check(M, num_cells, F):
    if(algorithm_1(M, num_cells, F)[0] == False or algorithm_2(M, num_cells, F)[0] == False or algorithm_3(M, num_cells, F)[0] == False):
        raise Exception("Generated partial matrix is not secure w.r.t. subspace trails.")


def printed_field_elt(value, p):
    l = len(hex(p - 1))
    if l % 2 == 1:
        l = l + 1
    value = hex(int(value))[2:]
    value = "0x" + value.zfill(l - 2)

    return f"BabyBear::from_canonical_u32({value}),"

def generate_head():
    header_strings = [
"""
//! This module defines all of the constants used by the Poseidon 2 hasher
//! The constants are generated using the `poseidon2_rust_params.sage` script which is a
//! modified version of the script found at
//! https://github.com/HorizenLabs/poseidon2/blob/main/poseidon2_rust_params.sage
""",
    "\n",
    "use lazy_static::lazy_static;",
    "use hybrid_array::{Array, typenum::*};",
    "use p3_baby_bear::BabyBear;",
    "use p3_field::AbstractField;",
    "\n"
    ]
    return "\n".join(header_strings)

def generate_arity_data(t, alpha):
    r_f_fixed, r_p_fixed, _, _ = poseidon_calc_final_numbers_fixed(PRIME, t, alpha, 128, True, FIELD_SIZE)
    init_sequence = init_generator(FIELD_SIZE, t, r_f_fixed, r_p_fixed)
    F = GF(PRIME)
    grain_gen = grain_sr_generator(init_sequence)

    # Round constants
    (full_round_constants, partial_round_constants) = generate_constants(FIELD_SIZE, t, r_f_fixed, r_p_fixed, PRIME, grain_gen)

    # Matrix
    matrix_partial = generate_matrix_partial(FIELD_SIZE, t, grain_gen, F)
    final_check(matrix_partial, t, F)
    matrix_partial_diag_plus_one = [matrix_partial[i,i] for i in range(t)]

    return r_f_fixed, r_p_fixed, full_round_constants, partial_round_constants, matrix_partial_diag_plus_one

def generate_arity_string(t, r_f_fixed, r_p_fixed, matrix_partial_diag_plus_one, full_round_constants, partial_round_constants):
    header = f"// +++ t = {t}, R_F = {r_f_fixed}, R_P = {r_p_fixed} +++"
    lazy_static_start = "lazy_static! {"
    lazy_static_end = "}\n"

    # Partial round Matrix
    partial_matrix_header = f"pub static ref MATRIX_DIAG_{t}_BABYBEAR: Array<BabyBear, U{t}> = Array::try_from(["
    partial_matrix_vals = [printed_field_elt(val - 1, PRIME) for val in matrix_partial_diag_plus_one]
    partial_matrix_end = "].as_ref()).unwrap();\n"

    # Full round constants
    full_rc_header = f"pub static ref FULL_RC_{t}_{r_f_fixed}: [[BabyBear; {t}]; {r_f_fixed}] = ["
    full_rc_vals = []
    for (i,val) in enumerate(full_round_constants):
        if i % t == 0:
            full_rc_vals.append("[")
        full_rc_vals.append(printed_field_elt(val, PRIME))
        if i % t == t - 1:
            full_rc_vals.append("],\n")
    full_rc_end = "];\n"

    # Partial round constants
    partial_rc_header = f"pub static ref PART_RC_{t}_{r_p_fixed}: [BabyBear; {r_p_fixed}] = ["
    partial_rc_vals = []
    for val in partial_round_constants:
        partial_rc_vals.append(printed_field_elt(val, PRIME))
    partial_rc_end = "];\n"

    return "\n".join(chain(
        [header], [lazy_static_start], [partial_matrix_header],
        partial_matrix_vals, [partial_matrix_end], [full_rc_header],
        full_rc_vals, [full_rc_end], [partial_rc_header], partial_rc_vals,
        [partial_rc_end], [lazy_static_end]
    ))

def arity_func(t, alpha):
    r_f_fixed, r_p_fixed, full_rc, part_rc, part_mat = generate_arity_data(t, alpha)
    return generate_arity_string(t, r_f_fixed, r_p_fixed, part_mat, full_rc, part_rc)

def generate_constants_file():
    alpha = get_alpha(PRIME)

    pool = Pool(processes=12)

    file_head = generate_head()
    inputs = range(4, 52, 4)
    outputs = pool.map(partial(arity_func, alpha=alpha), inputs)

    print(file_head)
    print("\n".join(outputs))

if __name__ == '__main__':
    generate_constants_file()
