import time, random
from sage.all import ZZ, gcd

COL_HNF_ALG = "flint" 

print("=== Algorithm 2 : START ===", flush=True)


import time
from contextlib import contextmanager

@contextmanager
def Timer(label, enabled=True):
    if not enabled:
        yield
        return
    t0 = time.perf_counter()
    yield
    dt = time.perf_counter() - t0
    print(f"{label} : {dt:.6f} sec")

# ------------------------------------------------------------
# 0) t(q) = q^n - q^(n-1) + ... - q + 1
# ------------------------------------------------------------
def alt_t(q, n):
    q = ZZ(q); n = ZZ(n)
    t = ZZ(0)
    for e in range(int(n), -1, -1):
        sign = 1 if ((n - e) % 2 == 0) else -1
        t += sign * (q**e)
    return ZZ(t)

# ------------------------------------------------------------
# 1) O element <-> Z^n vector (power basis)
# ------------------------------------------------------------
def Oelt_to_vec(a, n):
    L = list(a.list())
    if len(L) < n:
        L += [0]*(n-len(L))
    return vector(ZZ, [ZZ(x) for x in L[:n]])

def vec_to_Oelt(O, zeta, v):
    n = len(v)
    return sum(O(ZZ(v[j])) * (zeta**j) for j in range(n))

# ------------------------------------------------------------
# 2) Ideal matrix for principal ideal <alpha>
#    H(alpha)[:,j] = tau(alpha*zeta^j)
# ------------------------------------------------------------
def ideal_matrix_from_alpha(O, zeta, alpha, n):
    cols = []
    for j in range(n):
        cols.append(Oelt_to_vec(O(alpha) * (zeta**j), n))
    return matrix(ZZ, cols).transpose()


# ------------------------------------------------------------
# 4) Smith solver (generic ZZ linear algebra)
# ------------------------------------------------------------
def smith_solve_integer(A, b):
    D, U, V = A.smith_form()  # U*A*V = D
    b2 = U * b

    m = D.nrows()
    n = D.ncols()
    r = 0
    for i in range(min(m, n)):
        if D[i, i] != 0:
            r += 1
        else:
            break

    for i in range(r):
        if b2[i] % D[i, i] != 0:
            raise RuntimeError("No integer solution (divisibility fails).")
    for i in range(r, m):
        if b2[i] != 0:
            raise RuntimeError("No integer solution (zero rows constraint fails).")

    y = vector(ZZ, [0]*n)
    for i in range(r):
        y[i] = b2[i] // D[i, i]

    x = V * y
    return x

# ------------------------------------------------------------
# 5) CRT idempotents A_i (KeyGen helper)
# ------------------------------------------------------------
def build_crt_idempotents_from_alphas(O, zeta, n, alpha_list):
    m = len(alpha_list)
    one_vec = Oelt_to_vec(O(1), n)

    A_list = []
    for i in range(m):
        Mgen = O(1)
        for j in range(m):
            if j != i:
                Mgen *= O(alpha_list[j])

        HM = ideal_matrix_from_alpha(O, zeta, Mgen, n)
        HI = ideal_matrix_from_alpha(O, zeta, alpha_list[i], n)

        A_big = HM.augment(HI)  # n x (2n)
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
            if i != j:
                ok &= (A_list[i] in I_list[j])
    return ok

# ------------------------------------------------------------
# 6) Randomized PK 
# ------------------------------------------------------------
def sample_a_list(t_list):
    return [ZZ.random_element(0, ZZ(t)) for t in t_list]

def randomized_pk(O, A_list, t_list):
    m = len(A_list)
    a = sample_a_list(t_list)
    E_list = []
    A_prime = []
    for i in range(m):
        Ei = O(0)
        for j in range(m):
            if j == i:
                Ei += A_list[j] * O(1)
            else:
                Ei += A_list[j] * O(a[j])
        E_list.append(Ei)
        A_prime.append(A_list[i] * Ei)
    return A_prime, E_list, a

# ------------------------------------------------------------
# 7) Encryption / Decryption 
# ------------------------------------------------------------
def enc_with_pk_mod_t(O, A_used, u_list, t_list):
    if not (len(A_used) == len(u_list) == len(t_list)):
        raise ValueError("length mismatch")
    c = O(0)
    for ui, ti, Ai in zip(u_list, t_list, A_used):
        c += O(ZZ(ui) % ZZ(ti)) * Ai
    return c

def col_hnf_echelon(M, algorithm=COL_HNF_ALG):

    H = M.transpose().echelon_form(algorithm=algorithm).transpose()
    H = matrix(ZZ, H)
    # diagonal sign normalize
    for i in range(min(H.nrows(), H.ncols())):
        if H[i, i] < 0:
            H.set_column(i, -H.column(i))
    return H

def col_hnf(M):
    return col_hnf_echelon(M, algorithm=COL_HNF_ALG)

def dec_one_component(O, zeta, n, alpha_i, q_i, c):
    H = ideal_matrix_from_alpha(O, zeta, alpha_i, n)
    B = col_hnf(H)

    cvec = Oelt_to_vec(O(c), n)
    w, _, diag = alg2_reduce_mod_I_triangular(B, cvec)

    k = ZZ(w[n-1])
    t = ZZ(diag[n-1])
    u = (-ZZ(q_i) * k) % t
    return u, t

def dec_full(O, zeta, n, alpha_list, q_list, c):
    u_list = []
    t_list = []
    for i in range(len(alpha_list)):
        u, t = dec_one_component(O, zeta, n, alpha_list[i], q_list[i], c)
        u_list.append(u)
        t_list.append(t)
    return u_list, t_list

def enc_with_pk_mod_t(O, A_used, u_list, t_list):
    if not (len(A_used) == len(u_list) == len(t_list)):
        raise ValueError("length mismatch")
    c = O(0)
    for ui, ti, Ai in zip(u_list, t_list, A_used):
        c += O(ZZ(ui) % ZZ(ti)) * Ai
    return c

# ------------------------------------------------------------
# 4) Triangular checks 
# ------------------------------------------------------------
def is_upper_triangular_int(B):
    n = B.nrows()
    for i in range(n):
        for j in range(i):
            if B[i, j] != 0:
                return False
    return True

def is_lower_triangular_int(B):
    n = B.nrows()
    for i in range(n):
        for j in range(i+1, n):
            if B[i, j] != 0:
                return False
    return True

# ------------------------------------------------------------
# 5) Algorithm 2 reduction 
# ------------------------------------------------------------

def alg2_reduce_mod_I_triangular(B, cvec):
    n = B.nrows()
    diag = [ZZ(B[i, i]) for i in range(n)]
    if any(d <= 0 for d in diag):
        raise RuntimeError("HNF diagonal must be positive.")

    k = [ZZ(0)] * n

    if is_upper_triangular_int(B):
        # bottom-up
        for i in range(n-1, -1, -1):
            s = ZZ(cvec[i])
            for j in range(i+1, n):
                s -= k[j] * ZZ(B[i, j])
            k[i] = s // diag[i]

    elif is_lower_triangular_int(B):
        # top-down
        for i in range(n):
            s = ZZ(cvec[i])
            for j in range(0, i):
                s -= k[j] * ZZ(B[i, j])
            k[i] = s // diag[i]
    else:
        raise RuntimeError("HNF basis is neither upper nor lower triangular.")

    kvec = vector(ZZ, k)
    w = cvec - B * kvec
    w = vector(ZZ, [ZZ(w[i] % diag[i]) for i in range(n)])
    return w, kvec, diag

def lattice_basis_matrix_from_ideal(O, zeta, n, I_hat):
    bs = I_hat.basis()   # length n
    if len(bs) != n:
        raise RuntimeError(f"I_hat.basis() length mismatch: got {len(bs)}, expected {n}")

    cols = [Oelt_to_vec(O(b), n) for b in bs]     # each in Z^n
    M = matrix(ZZ, cols).transpose()             # n x n (columns)
    return M

def dec_one_component_from_Ihat(O, zeta, n, q_i, t_i, I_hat, c, timing=True):
    with Timer("[dec] build basis matrix from I_hat", enabled=timing):
        M = lattice_basis_matrix_from_ideal(O, zeta, n, I_hat)   # n x n

    with Timer("[dec] col_hnf(basis_matrix)", enabled=timing):
        B = col_hnf(M)   # n x n triangular

    cvec = Oelt_to_vec(O(c), n)
    w, _, diag = alg2_reduce_mod_I_triangular(B, cvec)

    k = ZZ(w[n-1])
    t_extracted = ZZ(diag[n-1])      
    u = (-ZZ(q_i) * k) % ZZ(t_extracted)

    return u, t_extracted

def setup_and_keygen(p, q_list, timing=True, do_verify=False):
    p = ZZ(p)
    q_list = [ZZ(q) for q in q_list]
    m = len(q_list)

    with Timer("CyclotomicField + ring_of_integers", enabled=timing):
        K = CyclotomicField(p)
        zeta = K.gen()
        O = K.ring_of_integers()
        n = int(p - 1)

    with Timer("t_list", enabled=timing):
        t_list = [alt_t(q, n) for q in q_list]

    with Timer("secret ideals", enabled=timing):
        zn1 = zeta**(n-1)
        alpha_list = [O(zn1 + q) for q in q_list]
        I_list = [O.ideal(a) for a in alpha_list]

    with Timer("CRT idempotents", enabled=timing):
        A_list = build_crt_idempotents_from_alphas(O, zeta, n, alpha_list)

    
    if do_verify:
        with Timer("CRT verify", enabled=timing):
            if not verify_crt_by_membership(O, I_list, A_list):
                raise RuntimeError("CRT idempotent verification failed.")
    else:
        if timing:
            print("CRT verify : (skipped)")


    with Timer("randomized PK", enabled=timing):
        A_prime, E_list, a = randomized_pkO, A_list, t_list)

    return {
        "K": K, "zeta": zeta, "O": O, "n": n, "m": m,
        "q_list": q_list, "t_list": t_list,
        "alpha_list": alpha_list, "I_list": I_list,
        "A_list": A_list, "A_prime": A_prime,
        "E_list": E_list, "a_list": a,
    }


def sample_elem_in_I_target_strict(O, A_prime, t_list, target=0, coeff_bound=10**6):
    m = len(A_prime)
    elem = O(0)
    for j in range(m):
        if j == target:
            continue
        r = ZZ.random_element(-coeff_bound, coeff_bound+1)
        if r == 0:
            r = 1

        if (r % ZZ(t_list[j])) == 0:
            r += 1
        elem += O(r) * O(A_prime[j])
    return O(elem)


def compress_two_gens_with_prefilter(O, gens, t_i,
                                     trials=400,
                                     coeff_bits=10,
                                     max_ideal_builds=3,
                                     timing=False,
                                     seed=0):
    random.seed(seed)
    t_i = ZZ(abs(t_i))
    ideal_builds = 0

    L = len(gens)


    for it in range(1, trials+1):
        r = [ZZ(random.randrange(-2**coeff_bits, 2**coeff_bits+1)) for _ in range(L)]
        s = [ZZ(random.randrange(-2**coeff_bits, 2**coeff_bits+1)) for _ in range(L)]
        a = sum(r[j]*gens[j] for j in range(L))
        b = sum(s[j]*gens[j] for j in range(L))

        Na = ZZ(abs(a.norm()))
        Nb = ZZ(abs(b.norm()))
        g_ab = gcd(Na, Nb)

        # prefilter: t_i | gcd(Na,Nb) 
        if g_ab % t_i != 0:
            continue

        t0 = time.perf_counter()
        J = O.ideal(a, b)
        dt = time.perf_counter() - t0
        ideal_builds += 1

        Nj = ZZ(abs(J.norm()))
        if timing:
            print(f"    [pair it={it}] build#{ideal_builds} ideal={dt:.3f}s  Norm==t_i? {Nj==t_i}")

        if Nj == t_i:
            return {"ok": True, "I_hat": J, "a": a, "b": b, "ideal_builds": ideal_builds}

        if ideal_builds >= max_ideal_builds:
            return {"ok": False, "ideal_builds": ideal_builds, "reason": "ideal budget exceeded"}

    return {"ok": False, "ideal_builds": ideal_builds, "reason": "trials exhausted"}


def recover_ideal_prefilter_compress(ctx, target_i,
                                    S0=12, S_step=6, S_max=48,
                                    coeff_bound=10**6,
                                    trials=400, coeff_bits=10,
                                    max_ideal_builds=3,
                                    timing=True, brief=True,
                                    seed=0):

    O = ctx["O"]
    A_prime = ctx["A_prime"]
    t_list = ctx["t_list"]
    t_i = ZZ(abs(t_list[target_i]))

    gens = []
    S = S0
    total_samples = 0

    while True:

        need = max(0, S - len(gens))
        if need > 0:
            t0 = time.perf_counter()
            for _ in range(need):
                x = sample_elem_in_I_target_strict(O, A_prime, t_list,
                                                   target=target_i,
                                                   coeff_bound=coeff_bound)
                gens.append(O(x))
                total_samples += 1
            dt = time.perf_counter() - t0
            if timing and (not brief):
                print(f"  ✓ [rec i={target_i}] collect to S={S} (added {need}) : {dt:.6f}s")

        # compress 
        if timing and (not brief):
            print(f"  [rec i={target_i}] try compress: |gens|={len(gens)} trials={trials} budget={max_ideal_builds}")

        t1 = time.perf_counter()
        out = compress_two_gens_with_prefilter(O, gens, t_i,
                                               trials=trials,
                                               coeff_bits=coeff_bits,
                                               max_ideal_builds=max_ideal_builds,
                                               timing=(timing and (not brief)),
                                               seed=seed + 1000*target_i + len(gens))
        dt1 = time.perf_counter() - t1

        if out["ok"]:
            if timing:
                print(f"✓ [recover i={target_i}] OK : |gens|={len(gens)} samples={total_samples} "
                      f"ideal_builds={out['ideal_builds']}  compress_time={dt1:.3f}s")
            return {"ok": True, "I_hat": out["I_hat"], "gens": gens, "samples": total_samples, "out": out}


        if timing:
            print(f"✗ [recover i={target_i}] FAIL : |gens|={len(gens)} "
                  f"ideal_builds={out.get('ideal_builds')} reason={out.get('reason')}  (try bigger S)")

        if S >= S_max:
            return {"ok": False, "I_hat": None, "gens": gens, "samples": total_samples, "out": out}

        S = min(S + S_step, S_max)

        
def attack_ideal_sense_fast(ctx,
                           S0=12, S_step=6, S_max=48,
                           coeff_bound=10**6,
                           trials=400, coeff_bits=10,
                           max_ideal_builds=3,
                           timing=True, brief=True):
    t_total0 = time.perf_counter()

    O = ctx["O"]; zeta = ctx["zeta"]; n = ctx["n"]; m = int(ctx["m"])
    q_list = ctx["q_list"]; t_list = ctx["t_list"]
    A_prime = ctx["A_prime"]


    u = [ZZ(i+1) for i in range(m)]

    t_enc0 = time.perf_counter()
    c = enc_with_pk_mod_t(O, A_prime, u, t_list)
    t_enc = time.perf_counter() - t_enc0
    if timing:
        print(f"[attack] encrypt : {t_enc:.6f} sec")
    if (not brief):
        print("[victim] u mod t =", [ZZ(u[i]) % ZZ(t_list[i]) for i in range(m)])

    # recover ideals (FAST)
    I_hats = []
    t_rec0 = time.perf_counter()

    for i in range(m):
        if not brief:
            print("-"*60)
            print(f"[attacker] recover i={i}")

        out = recover_ideal_prefilter_compress(
            ctx, i,
            S0=S0, S_step=S_step, S_max=S_max,
            coeff_bound=coeff_bound,
            trials=trials, coeff_bits=coeff_bits,
            max_ideal_builds=max_ideal_builds,
            timing=timing, brief=brief,
            seed=1234
        )
        if not out["ok"]:
            if timing:
                print(f"✗ [attack] recover i={i} : FAIL (samples={out['samples']}, |gens|={len(out['gens'])})")
            return {"success": False, "failed_i": i, "out": out}

        I_hats.append(out["I_hat"])

    t_rec = time.perf_counter() - t_rec0


    u_hat = []
    t_hat = []
    ok_u = True
    ok_t = True

    t_dec0 = time.perf_counter()
    for i in range(m):
        ti0 = time.perf_counter()
        ui, ti_hat = dec_one_component_from_Ihat(
            O, zeta, n,
            q_list[i],
            t_list[i],
            I_hats[i],
            c,
            timing=False
        )
        dt = time.perf_counter() - ti0

        if timing:
            print(f" [attack] dec i={i} : {dt:.6f} sec")

        u_hat.append(ui); t_hat.append(ti_hat)
        ok_u &= (ZZ(ui) % ZZ(t_list[i]) == ZZ(u[i]) % ZZ(t_list[i]))
        ok_t &= (ZZ(ti_hat) == ZZ(t_list[i]))

    t_dec = time.perf_counter() - t_dec0

    t_total = time.perf_counter() - t_total0
    success = (ok_u and ok_t)

    if timing:
        print(f" [attack] recover(all) : {t_rec:.6f} sec")
        print(f" [attack] decrypt(all) : {t_dec:.6f} sec")
        print(f" [attack] TOTAL        : {t_total:.6f} sec")
        print(f"[check] u_mod_match={ok_u}  t_match={ok_t}  success={success}")

    return {
        "success": success,
        "u": u, "u_hat": u_hat,
        "ok_u": ok_u, "ok_t": ok_t,
        "I_hats": I_hats, "c": c,
        "time_encrypt": t_enc,
        "time_recover": t_rec,
        "time_decrypt": t_dec,
        "time_total": t_total
    }

def run_attack_many_ps(ps, q_list=(2,3,5,7),
                       S0=12, S_step=6, S_max=48,
                       coeff_bound=10**6,
                       trials=400, coeff_bits=10,
                       max_ideal_builds=3,
                       timing=True, brief=True):
    results = []
    for p in ps:
        print("\n" + "="*80)
        print(f"[RUN] p={p}, q_list={q_list}")
        print("="*80)

        t0 = time.perf_counter()
        ctx = setup_and_keygen(ZZ(p), [ZZ(x) for x in q_list], timing=True, do_verify = False)
        t_setup = time.perf_counter() - t0
        if timing:
            print(f" [setup] TOTAL : {t_setup:.6f} sec")

        res = attack_ideal_sense_fast(ctx,
                                      S0=S0, S_step=S_step, S_max=S_max,
                                      coeff_bound=coeff_bound,
                                      trials=trials, coeff_bits=coeff_bits,
                                      max_ideal_builds=max_ideal_builds,
                                      timing=timing, brief=brief)
        results.append((p, t_setup, res.get("success", False), res))
        if timing:
            print(f"[SUMMARY] p={p} : success={res.get('success', False)}  setup={t_setup:.3f}s  attack_total={res.get('time_total', -1):.3f}s")
    return results



ps = [127]

out = run_attack_many_ps(ps, q_list=(11,71,263,547,1039),
                         S0=12, S_step=6, S_max=60,
                         trials=400, coeff_bits=10,
                         max_ideal_builds=3,
                         timing=True, brief=True)