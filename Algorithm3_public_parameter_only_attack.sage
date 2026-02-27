# ============================================================
# newpk_attack_with_timing.sage
# ============================================================

import time

# -----------------------------
# Logger / Timer
# -----------------------------
class Logger:
    def __init__(self, enabled=True):
        self.enabled = enabled
        self.ind = 0

    def _p(self, msg):
        if self.enabled:
            print("  "*self.ind + str(msg), flush=True)

    def section(self, title):
        log = self
        class _Sec:
            def __enter__(self):
                log._p(f"[{title}]")
                log.ind += 1
            def __exit__(self, exc_type, exc, tb):
                log.ind -= 1
        return _Sec()

    def info(self, msg): self._p(msg)
    def ok(self, msg):   self._p(f"✓ {msg}")
    def warn(self, msg): self._p(f"(!) {msg}")

class Timer:
    def __init__(self, label, log, enabled=True):
        self.label = label
        self.log = log
        self.enabled = enabled
    def __enter__(self):
        if self.enabled:
            self.t0 = time.perf_counter()
    def __exit__(self, exc_type, exc, tb):
        if self.enabled:
            dt = time.perf_counter() - self.t0
            self.log.ok(f"{self.label}: {dt:.6f} sec")

# -----------------------------
# Helper
# -----------------------------

def alt_t(q, n):
    q = ZZ(q); n = ZZ(n)
    t = ZZ(0)
    for e in range(int(n), -1, -1):
        sign = 1 if ((n - e) % 2 == 0) else -1
        t += sign * (q**e)
    return ZZ(t)

def eval_Oelt_at_a_mod_t(xO, a, t_i, n):
    t_i = ZZ(t_i)
    Rmod = Integers(t_i)
    aR = Rmod(ZZ(a))

    poly = xO.lift()
    coeffs = poly.list()

    if len(coeffs) < n:
        coeffs += [0]*(n - len(coeffs))
    else:
        coeffs = coeffs[:n]

    v = Rmod(0)
    for k in reversed(range(n)):
        v = v*aR + Rmod(ZZ(coeffs[k]))
    return ZZ(v)

def tau_root_from_q(q_i, t_i):
    q_i = ZZ(q_i); t_i = ZZ(t_i)
    return ZZ((-inverse_mod(q_i % t_i, t_i)) % t_i)

def tau_decrypt_scaled(ctx_pub, c, q_rec, log=None):
    O = ctx_pub["O"]
    A_prime = ctx_pub["A_prime"]
    t_list = ctx_pub["t_list"]
    n = int(ctx_pub["n"])

    u_hat = []
    for i, (qi, ti) in enumerate(zip(q_rec, t_list)):
        ti = ZZ(ti)
        ai = tau_root_from_q(qi, ti)

        # s = c(ai) mod t_i
        s = eval_Oelt_at_a_mod_t(O(c), ai, ti, n)

        # e = A'_i(ai) mod t_i
        e = eval_Oelt_at_a_mod_t(O(A_prime[i]), ai, ti, n)

        g = gcd(e, ti)
        if g != 1:
            raise RuntimeError(f"i={i}: A'_i(ai) not invertible mod t_i (gcd={g})")

        ui = (ZZ(s) * inverse_mod(ZZ(e), ti)) % ti
        u_hat.append(ui)
    
    return u_hat

# -----------------------------
# public key
# -----------------------------

def zeta_inv_in_quotient(zeta, n):
    s = zeta.parent()(0)
    for k in range(n):
        s += zeta**k
    return -s

def build_crt_idempotents_closed_form(O, zeta, q_list, t_list):
    m = len(q_list)
    n = int(O.modulus().degree()) 

    zinv = zeta_inv_in_quotient(zeta, n)
    alpha_list = [O(zinv + ZZ(q)) for q in q_list]

    A_list = []
    for i in range(m):
        ti = ZZ(t_list[i])
        qi = ZZ(q_list[i])

        M = O(1)
        denom = ZZ(1)
        for j in range(m):
            if j == i:
                continue
            M *= alpha_list[j]
            denom = (denom * (ZZ(q_list[j]) - qi)) % ti

        g = gcd(denom, ti)
        if g != 1:
            raise RuntimeError(f"[NEW CRT] denom not invertible: i={i}, gcd={g}")

        ci = inverse_mod(denom, ti)
        if ci > ti//2:
            ci -= ti

        A_list.append(M * O(ci))

    return A_list

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

def make_large_plaintext(t_list, mode="random_big", scale=10, rand_scale=None):
    u = []
    for i, t in enumerate(t_list):
        t = ZZ(t)
        if mode == "small":
            u_i = ZZ(i+1)
        elif mode == "mixed":
            u_i = ZZ(scale) * t + ZZ(i+1)
        elif mode == "random_big":
            rs = ZZ(rand_scale) if rand_scale is not None else ZZ(scale)
            u_i = ZZ.random_element(0, rs * t)
        else:
            raise ValueError("unknown plaintext mode")
        u.append(ZZ(u_i))
    return u


def enc_with_pk_mod_t(O, A_prime, u_list, t_list):
    c = O(0)
    for ui, ti, Ai in zip(u_list, t_list, A_prime):
        c += O(ZZ(ui) % ZZ(ti)) * Ai
    return c

# -----------------------------
# t -> q recovery 
# -----------------------------

def recover_q_from_t(t, p, q_min=2, max_q=None, log=None):
    t = ZZ(t); p = ZZ(p)

    def f(q):
        q = ZZ(q)
        return (q**p + 1) // (q + 1)

    def check(q):
        q = ZZ(q)
        return (q + 1) * t == q**p + 1

    lo = ZZ(q_min)
    hi = ZZ(q_min)

    # 1) find upper bound by doubling
    while True:
        if max_q is not None and hi > ZZ(max_q):
            hi = ZZ(max_q)
            break
        if f(hi) >= t:
            break
        hi *= 2
        if max_q is not None and hi > ZZ(max_q):
            hi = ZZ(max_q)
            break

    if f(hi) < t:
        return None

    # 2) binary search
    while lo <= hi:
        mid = (lo + hi) // 2
        v = f(mid)
        if v == t:
            if check(mid):
                return ZZ(mid)
            else:
                return None
        elif v < t:
            lo = mid + 1
        else:
            hi = mid - 1

    return None

# -----------------------------
# Attack with Timing
# -----------------------------

def attack_t_to_q_then_tau_decrypt(ctx_pub, c, log):
    p = ZZ(ctx_pub["p"])
    t_list = ctx_pub["t_list"]

    q_rec = []
    a_rec = []

    # 1. Measure Recovery Time
    t_rec_start = time.perf_counter()
    with log.section("recover q_i from public t_i"):
        for i, ti in enumerate(t_list):
            q = recover_q_from_t(ti, p, log=None) 
            if q is None:
                raise RuntimeError(f"q recovery failed at i={i}")
            q_rec.append(ZZ(q))
            log.ok(f"i={i}: Recovered q={q}")
    t_rec_total = time.perf_counter() - t_rec_start

    # Compute a_i 
    for i, (q, ti) in enumerate(zip(q_rec, t_list)):
        ai = tau_root_from_q(q, ti)
        a_rec.append(ZZ(ai))

    # 2. Measure Decryption Time
    t_dec_start = time.perf_counter()
    with log.section("tau-evaluation decrypt (scaled)"):
        u_hat = tau_decrypt_scaled(ctx_pub, c, q_rec, log=log)
    t_dec_total = time.perf_counter() - t_dec_start

    # 3. Print Summary
    t_attack_total = time.perf_counter() - t_rec_start # From start of recovery to end of dec

    print("\n" + "="*50)
    print(f"   [Attack Summary] p={p}, m={len(t_list)}")
    print(f"   - Recover q (Binary Search) : {t_rec_total:.6f} sec")
    print(f"   - Decrypt (Eval + Invert)   : {t_dec_total:.6f} sec")
    print(f"   - TOTAL ATTACK TIME         : {t_attack_total:.6f} sec")
    print("="*50 + "\n")

    return q_rec, a_rec, u_hat

# -----------------------------
# KeyGen in quotient ring
# -----------------------------

def keygen_newpk_quotient(p, q_list_secret, log, timing=True):
    t_setup_start = time.perf_counter()
    
    p = ZZ(p)
    n = int(p - 1)
    q_list = [ZZ(q) for q in q_list_secret]
    m = len(q_list)

    with Timer("Build O = ZZ[x]/(Phi_p)", log, enabled=timing):
        R.<x> = PolynomialRing(ZZ)
        Phi = cyclotomic_polynomial(p)      
        O.<zeta> = R.quotient(Phi)          

    with Timer("t_list", log, enabled=timing):
        t_list = [alt_t(q, n) for q in q_list]

    with Timer("A_list (closed-form)", log, enabled=timing):
        A_list = build_crt_idempotents_closed_form(O, zeta, q_list, t_list)

    with Timer("randomized pk (A_prime)", log, enabled=timing):
        A_prime, E_list, a_rand = randomized_pk(O, A_list, t_list)

    t_setup_total = time.perf_counter() - t_setup_start
    if timing:
        print(f" [Setup] TOTAL TIME         : {t_setup_total:.6f} sec")

    ctx_pub = {
        "p": p, "n": n, "m": m, "O": O,
        "t_list": t_list, "A_prime": A_prime,
    }
    ctx_sec = {
        "q_list": q_list, "zeta": zeta,
        "A_list": A_list, "E_list": E_list, "a_rand": a_rand,
    }
    return ctx_pub, ctx_sec

# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    log = Logger(enabled=True)


    p = 83
    q_secret = [11, 71, 263, 547, 1039]
   
    log.info(f"STARTING ATTACK TEST: p={p}, n={p-1}, m={len(q_secret)}")
    print("="*60)

    # 1. Setup
    ctx_pub, ctx_sec = keygen_newpk_quotient(p, q_secret, log, timing=True)
    t_list = ctx_pub["t_list"]

    # 2. Encrypt
    u = make_large_plaintext(t_list, "random_big", 10)
    with log.section("Encrypting random msg"):
        t0 = time.perf_counter()
        c = enc_with_pk_mod_t(ctx_pub["O"], ctx_pub["A_prime"], u, t_list)
        dt = time.perf_counter() - t0
        log.ok(f"Encryption time: {dt:.6f} sec")

    # 3. Attack (Recover + Decrypt)
    q_rec, a_rec, u_hat = attack_t_to_q_then_tau_decrypt(ctx_pub, c, log)

    # 4. Verify
    with log.section("Verification"):
        ok = all(ZZ(u_hat[i]) % ZZ(t_list[i]) == ZZ(u[i]) % ZZ(t_list[i]) for i in range(len(u)))
        if ok:
            log.ok("SUCCESS! Decrypted messages match original plaintexts.")
        else:
            log.warn("FAILURE! Decryption mismatch.")
            log.info(f"Original: {u}")
            log.info(f"Decrypted: {u_hat}")