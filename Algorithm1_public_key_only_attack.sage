import time

# ==============================================================================
# 0) Helper Classes & Functions
# ==============================================================================

class GenPool:
    def __init__(self):
        self.gens = []
    def add(self, g):
        self.gens.append(g)
    def __len__(self):
        return len(self.gens)

def sample_elem_in_I_target_strict(O, A_prime, t_list, target, coeff_bound=10):

    m = len(A_prime)
    res = O(0)
    for j in range(m):
        if j == target: continue
        r = ZZ.random_element(-coeff_bound, coeff_bound + 1)
        res += A_prime[j] * r
    return res

def alt_t(q, n):
    q = ZZ(q); n = ZZ(n)
    t = ZZ(0)
    for e in range(int(n), -1, -1):
        sign = 1 if ((n - e) % 2 == 0) else -1
        t += sign * (q**e)
    return ZZ(t)

def Oelt_to_vec(a, n):
    L = list(a.list())
    if len(L) < n: L += [0]*(n-len(L))
    return vector(ZZ, [ZZ(x) for x in L[:n]])

def vec_to_Oelt(O, zeta, v):
    n = len(v)
    return sum(O(ZZ(v[j])) * (zeta**j) for j in range(n))

def ideal_matrix_from_alpha(O, zeta, alpha, n):
    cols = []
    for j in range(n):
        cols.append(Oelt_to_vec(O(alpha) * (zeta**j), n))
    return matrix(ZZ, cols).transpose()

# ==============================================================================
# 1) HNF & Linear Algebra
# ==============================================================================
def col_hnf(M):
    return M.transpose().hermite_form().transpose()

def is_upper_triangular_int(B):
    n = B.nrows()
    for i in range(n):
        for j in range(i):
            if B[i, j] != 0: return False
    return True

def is_lower_triangular_int(B):
    n = B.nrows()
    for i in range(n):
        for j in range(i+1, n):
            if B[i, j] != 0: return False
    return True

def alg2_reduce_mod_I_triangular(B, cvec):
    n = B.nrows()
    diag = [ZZ(B[i, i]) for i in range(n)]
    k = [ZZ(0)] * n
    
    if is_upper_triangular_int(B):
        for i in range(n-1, -1, -1):
            s = ZZ(cvec[i])
            for j in range(i+1, n):
                s -= k[j] * ZZ(B[i, j])
            k[i] = s // diag[i]
    elif is_lower_triangular_int(B):
        for i in range(n):
            s = ZZ(cvec[i])
            for j in range(0, i):
                s -= k[j] * ZZ(B[i, j])
            k[i] = s // diag[i]
    else:
        pass 

    kvec = vector(ZZ, k)
    w = cvec - B * kvec
    w = vector(ZZ, [ZZ(w[i] % diag[i]) for i in range(n)])
    return w, kvec, diag

def smith_solve_integer(A, b):
    out = A.smith_form()
    D, U, V = out
    b2 = U * b
    m, n = D.nrows(), D.ncols()
    r = 0
    for i in range(min(m, n)):
        if D[i, i] != 0: r += 1
        else: break
    
    y = vector(ZZ, [0]*n)
    for i in range(r):
        y[i] = b2[i] // D[i, i]
    return V * y

# ==============================================================================
# 2) Setup Helpers (CRT & PK)
# ==============================================================================
def build_crt_idempotents_from_alphas(O, zeta, n, alpha_list):
    m = len(alpha_list)
    one_vec = Oelt_to_vec(O(1), n)
    A_list = []
    for i in range(m):
        Mgen = O(1)
        for j in range(m):
            if j != i: Mgen *= O(alpha_list[j])
        
        HM = ideal_matrix_from_alpha(O, zeta, Mgen, n)
        HI = ideal_matrix_from_alpha(O, zeta, alpha_list[i], n)
        A_big = HM.augment(HI)
        x = smith_solve_integer(A_big, one_vec)
        u = x[:n]
        r = vec_to_Oelt(O, zeta, u)
        s = Mgen * r
        A_list.append(O(s))
    return A_list

def verify_crt_by_membership(O, I_list, A_list):
    m = len(A_list)
    ok = True
    for i in range(m):
        ok &= ((A_list[i] - O(1)) in I_list[i])
    for i in range(m):
        for j in range(m):
            if i == j: continue
            ok &= (A_list[i] in I_list[j])
    return ok

def sample_a_list(t_list):
    return [ZZ.random_element(0, ZZ(t)) for t in t_list]

def randomized_pk(O, A_list, t_list):
    m = len(A_list)
    a = sample_a_list(t_list)
    E_list, A_prime = [], []
    for i in range(m):
        Ei = O(0)
        for j in range(m):
            if j == i: Ei += A_list[j] * O(1)
            else:      Ei += A_list[j] * O(a[j])
        E_list.append(Ei)
        A_prime.append(A_list[i] * Ei)
    return A_prime, E_list, a

def enc_with_pk_mod_t(O, A_used, u_list, t_list):
    c = O(0)
    for ui, ti, Ai in zip(u_list, t_list, A_used):
        c += O(ZZ(ui) % ZZ(ti)) * Ai
    return c

# ==============================================================================
# 3) KeyGen / Setup with Detailed Timing
# ==============================================================================
def setup_and_keygen(p, q_list):
    # Setup Start
    t_start = time.perf_counter()
    
    # 1. Field Setup
    t0 = time.perf_counter()
    p = ZZ(p)
    q_list = [ZZ(q) for q in q_list]
    m = len(q_list)
    K = CyclotomicField(p)
    zeta = K.gen()
    O = K.ring_of_integers()
    n = int(p - 1)
    print(f" CyclotomicField + ring_of_integers : {time.perf_counter()-t0:.6f} sec")
    
    # 2. t_list
    t0 = time.perf_counter()
    t_list = [alt_t(q, n) for q in q_list]
    print(f" t_list : {time.perf_counter()-t0:.6f} sec")
    
    # 3. Secret Ideals
    t0 = time.perf_counter()
    alpha_list = [O(zeta**(n-1) + q) for q in q_list]
    I_list = [O.ideal(a) for a in alpha_list]
    print(f" secret ideals : {time.perf_counter()-t0:.6f} sec")
    
    # 4. CRT Idempotents
    t0 = time.perf_counter()
    A_list = build_crt_idempotents_from_alphas(O, zeta, n, alpha_list)
    print(f" CRT idempotents : {time.perf_counter()-t0:.6f} sec")
    
    if not verify_crt_by_membership(O, I_list, A_list):
        raise RuntimeError("CRT verification failed.")
    # print(f" CRT verify : (skipped)")

    # 5. Randomized PK
    t0 = time.perf_counter()
    A_prime, E_list, a = randomized_pk(O, A_list, t_list)
    print(f" randomized PK : {time.perf_counter()-t0:.6f} sec")
    
    # Total Setup Time
    t_total_setup = time.perf_counter() - t_start
    print(f" [setup] TOTAL : {t_total_setup:.6f} sec")

    return {
        "K": K, "zeta": zeta, "O": O, "n": n, "m": m,
        "q_list": q_list, "t_list": t_list,
        "alpha_list": alpha_list, "I_list": I_list,
        "A_list": A_list, "A_prime": A_prime, "E_list": E_list, "a": a,
    }

# ==============================================================================
# 4) Attack Functions
# ==============================================================================
def lattice_basis_matrix_from_ideal(O, zeta, n, I_hat):
    bs = I_hat.basis()
    cols = [Oelt_to_vec(O(b), n) for b in bs]
    return matrix(ZZ, cols).transpose()

import sys 

def recover_ideal_batch(ctx, target_i, base_batch=8, max_batches=40, coeff_bound=10):
    O = ctx["O"]
    t_list = ctx["t_list"]
    t_i = ZZ(t_list[target_i])
    
    pool = GenPool()
    ideal_build_count = 0
    I_hat = None

    print(f"[recover i={target_i}] Processing...", end="", flush=True)

    for b in range(1, max_batches+1):

        print(".", end="", flush=True) 

        # Sample
        for _ in range(base_batch):
            g = sample_elem_in_I_target_strict(
                O, ctx["A_prime"], t_list, target=target_i, coeff_bound=coeff_bound
            )
            pool.add(g)

        # Build Ideal
        ideal_build_count += 1
        I_hat = O.ideal(pool.gens)
        N = ZZ(I_hat.norm())

        # Check success
        if N == abs(t_i):
            print(" Done!") 
            return {
                "ok": True, 
                "I_hat": I_hat, 
                "gens_used": len(pool), 
                "ideal_builds": ideal_build_count
            }

    print(" Failed.") 
    return {
        "ok": False, 
        "I_hat": I_hat, 
        "gens_used": len(pool), 
        "ideal_builds": ideal_build_count,
        "reason": "ideal budget exceeded"
    }

def dec_one_component_from_Ihat(O, zeta, n, q_i, t_i, I_hat, c):
    # Basis Construction
    M = lattice_basis_matrix_from_ideal(O, zeta, n, I_hat)
    # HNF
    B = col_hnf(M)
    # Reduction
    cvec = Oelt_to_vec(O(c), n)
    w, _, diag = alg2_reduce_mod_I_triangular(B, cvec)

    k = ZZ(w[n-1])
    t_extracted = ZZ(diag[n-1])
    u = (-ZZ(q_i) * k) % ZZ(t_extracted)
    return u, t_extracted

# ==============================================================================
# 5) Main Attack Loop with Formatted Output
# ==============================================================================
def attack_ideal_sense(ctx, upto_batches=40, base_batch=8, coeff_bound=10):
    t_attack_start = time.perf_counter()
    
    O = ctx["O"]; zeta = ctx["zeta"]; n = ctx["n"]; m = ctx["m"]
    q_list = ctx["q_list"]; t_list = ctx["t_list"]; A_prime = ctx["A_prime"]

    # 1. Encrypt
    u = [ZZ(i+1) for i in range(len(q_list))]
    t_enc0 = time.perf_counter()
    c = enc_with_pk_mod_t(O, A_prime, u, t_list)
    print(f" [attack] encrypt : {time.perf_counter() - t_enc0:.6f} sec")

    # 2. Recover Ideals
    I_hats = []
    t_rec_total_start = time.perf_counter()
    
    for i in range(len(q_list)):
        t_i_start = time.perf_counter()
        
        out = recover_ideal_batch(
            ctx, i, base_batch=base_batch, max_batches=upto_batches, coeff_bound=coeff_bound
        )
        
        dt = time.perf_counter() - t_i_start
        
        if out["ok"]:

            print(f" [recover i={i}] OK : time={dt:.3f}s |gens|={out['gens_used']} ideal_builds={out['ideal_builds']}")
            I_hats.append(out["I_hat"])
        else:
            print(f" [recover i={i}] FAIL : time={dt:.3f}s |gens|={out['gens_used']} reason={out.get('reason','?')}")
            return None

    t_rec_total = time.perf_counter() - t_rec_total_start

    # 3. Decrypt & Verify
    u_hat, t_hat = [], []
    t_dec_total_start = time.perf_counter()
    ok_u, ok_t = True, True

    for i in range(m):
        t_dec0 = time.perf_counter()
        
        ui, ti_hat = dec_one_component_from_Ihat(
            O, zeta, n, q_list[i], t_list[i], I_hats[i], c
        )
        
        dt_dec = time.perf_counter() - t_dec0
        print(f" [attack] dec i={i} : {dt_dec:.6f} sec")
        
        u_hat.append(ui)
        t_hat.append(ti_hat)

        if ZZ(ui) % ZZ(t_list[i]) != ZZ(u[i]) % ZZ(t_list[i]): ok_u = False
        if ZZ(ti_hat) != ZZ(t_list[i]): ok_t = False

    t_dec_total = time.perf_counter() - t_dec_total_start
    t_attack_total = time.perf_counter() - t_attack_start
    success = (ok_u and ok_t)

    print(f" [attack] recover(all) : {t_rec_total:.6f} sec")
    print(f" [attack] decrypt(all) : {t_dec_total:.6f} sec")
    print(f" [attack] TOTAL          : {t_attack_total:.6f} sec")
    print(f"[check] u_mod_match={ok_u}  t_match={ok_t}  success={success}")

    return {
        "success": success,
        "time_total": t_attack_total
    }

def run_many_p(p_list, q_list=[2,3,5,7], upto_batches=30, base_batch=2, coeff_bound=10):
    results = []
    for p in p_list:
        print("\n" + "="*80)
        print(f"[RUN] p={p}, q_list={tuple(q_list)}")
        print("="*80)
        
        # Setup 
        t0 = time.perf_counter()
        ctx = setup_and_keygen(ZZ(p), [ZZ(x) for x in q_list])
        t_setup = time.perf_counter() - t0
        
        # Attack 
        res = attack_ideal_sense(
            ctx, upto_batches=upto_batches, base_batch=base_batch, coeff_bound=coeff_bound
        )

        if res is None:
            print(f"[SUMMARY] p={p} : FAIL (setup={t_setup:.3f}s)")
            results.append({"p": p, "ok": False})
        else:
            print(f"[SUMMARY] p={p} : success={res['success']}  setup={t_setup:.3f}s  attack_total={res['time_total']:.3f}s")
            results.append({"p": p, "ok": True})
            
    return results

# ==============================================================================
# Execute
# ==============================================================================
if __name__ == "__main__":
    p_list = [107,109,127,131] 
    
    R = run_many_p(p_list, 
                   q_list=[11,71,263,547,1039], 
                   upto_batches=30, 
                   base_batch=2, 
                   coeff_bound=10)