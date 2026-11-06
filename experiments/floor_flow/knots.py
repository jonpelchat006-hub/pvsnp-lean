"""
Part 13: the knot ladder. Untie SHA-256's knots one kind at a time.

Four versions of the SHA-256 round function (message schedule included):
  salt     every modular addition -> XOR, Ch -> e^f^g, Maj -> a^b^c
           (no AND gates at all: a linear map over GF(2))
  chmaj    additions -> XOR, Ch and Maj kept (degree-2 knots, no carries)
  carries  additions kept, Ch -> e^f^g, Maj -> a^b^c (only the carry knots)
  full     real SHA-256 (all knots)

The task: the message's first u words are unknown, the other 16 - u words are
known; the 256-bit working state after r rounds is known. Find unknown words
that give that state.

The circuit is written out as SAT with constant propagation (known bits cost
nothing). XOR gates go to the solver either as native XOR constraints
(CryptoMiniSat, which can run Gaussian elimination on them) or as ordinary
clauses (CaDiCaL, which only resolves clauses).
"""

import os
import random
import select
import signal
import time

import numpy as np

MASK = 0xFFFFFFFF
K = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
IV = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
VARIANTS = {"salt": (False, False), "chmaj": (False, True), "carries": (True, False), "full": (True, True)}


# ------------------------------------------------------------------ plain evaluation

def _rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK


def evaluate(W16, rounds, variant):
    """Working state after `rounds` rounds of the chosen version."""
    carries, knots = VARIANTS[variant]
    add = (lambda x, y: (x + y) & MASK) if carries else (lambda x, y: x ^ y)
    ch = (lambda e, f, g: (e & f) ^ (~e & g & MASK)) if knots else (lambda e, f, g: e ^ f ^ g)
    mj = (lambda a, b, c: (a & b) ^ (a & c) ^ (b & c)) if knots else (lambda a, b, c: a ^ b ^ c)
    W = list(W16)
    for t in range(16, rounds):
        s0 = _rotr(W[t - 15], 7) ^ _rotr(W[t - 15], 18) ^ (W[t - 15] >> 3)
        s1 = _rotr(W[t - 2], 17) ^ _rotr(W[t - 2], 19) ^ (W[t - 2] >> 10)
        W.append(add(add(add(W[t - 16], s0), W[t - 7]), s1))
    a, b, c, d, e, f, g, h = IV
    for t in range(rounds):
        S1 = _rotr(e, 6) ^ _rotr(e, 11) ^ _rotr(e, 25)
        T1 = add(add(add(add(h, S1), ch(e, f, g)), K[t]), W[t])
        S0 = _rotr(a, 2) ^ _rotr(a, 13) ^ _rotr(a, 22)
        T2 = add(S0, mj(a, b, c))
        h, g, f, e, d, c, b, a = g, f, e, add(d, T1), c, b, a, add(T1, T2)
    return [a, b, c, d, e, f, g, h]


def _rotr_np(x, n):
    return (x >> np.uint32(n)) | (x << np.uint32(32 - n))


def evaluate_many(W0s, W16, rounds, variant):
    """evaluate() for many choices of word 0 at once (W0s: uint32 array; the
    other words from W16). Returns the 8 state words as arrays."""
    carries, knots = VARIANTS[variant]
    add = (lambda x, y: x + y) if carries else (lambda x, y: x ^ y)          # uint32 wraps
    ch = (lambda e, f, g: (e & f) ^ (~e & g)) if knots else (lambda e, f, g: e ^ f ^ g)
    mj = (lambda a, b, c: (a & b) ^ (a & c) ^ (b & c)) if knots else (lambda a, b, c: a ^ b ^ c)
    ones = np.ones_like(W0s)
    W = [W0s] + [ones * np.uint32(w) for w in W16[1:]]
    for t in range(16, rounds):
        s0 = _rotr_np(W[t - 15], 7) ^ _rotr_np(W[t - 15], 18) ^ (W[t - 15] >> np.uint32(3))
        s1 = _rotr_np(W[t - 2], 17) ^ _rotr_np(W[t - 2], 19) ^ (W[t - 2] >> np.uint32(10))
        W.append(add(add(add(W[t - 16], s0), W[t - 7]), s1))
    a, b, c, d, e, f, g, h = (ones * np.uint32(v) for v in IV)
    for t in range(rounds):
        S1 = _rotr_np(e, 6) ^ _rotr_np(e, 11) ^ _rotr_np(e, 25)
        T1 = add(add(add(add(h, S1), ch(e, f, g)), np.uint32(K[t])), W[t])
        S0 = _rotr_np(a, 2) ^ _rotr_np(a, 13) ^ _rotr_np(a, 22)
        T2 = add(S0, mj(a, b, c))
        h, g, f, e, d, c, b, a = g, f, e, add(d, T1), c, b, a, add(T1, T2)
    return [a, b, c, d, e, f, g, h]


def brute_force(W_known, bits, rounds, variant, target, limit, chunk=1 << 18):
    """Try the lowest `bits` bits of word 0 in order 0, 1, 2, ... (numpy, in
    chunks) until the state matches. Returns (status, word 0 or None, seconds,
    candidates tried)."""
    t0 = time.perf_counter()
    high = W_known[0] & ~((1 << bits) - 1) & MASK
    tried = 0
    for start in range(0, 1 << bits, chunk):
        if time.perf_counter() - t0 > limit:
            return "timeout", None, time.perf_counter() - t0, tried
        low = np.arange(start, min(start + chunk, 1 << bits), dtype=np.uint64)
        W0s = (low | np.uint64(high)).astype(np.uint32)
        st = evaluate_many(W0s, W_known, rounds, variant)
        hit = np.ones(len(W0s), dtype=bool)
        for word, x in zip(st, target):
            hit &= word == np.uint32(x)
        tried += len(W0s)
        if hit.any():
            i = int(np.argmax(hit))
            return "solved", int(W0s[i]), time.perf_counter() - t0, start + i + 1
    return "unsat", None, time.perf_counter() - t0, tried


# ------------------------------------------------------------------ circuit to SAT

class Circuit:
    """Bits are True/False constants or nonzero ints (SAT literals)."""

    def __init__(self, native_xor):
        self.n = 0
        self.clauses = []
        self.xors = []
        self.native_xor = native_xor
        self.ands = 0

    def var(self):
        self.n += 1
        return self.n

    @staticmethod
    def neg(a):
        return (not a) if isinstance(a, bool) else -a

    def xor(self, a, b):
        if isinstance(a, bool) and isinstance(b, bool):
            return a != b
        if isinstance(a, bool):
            return self.neg(b) if a else b
        if isinstance(b, bool):
            return self.neg(a) if b else a
        if a == b:
            return False
        if a == -b:
            return True
        v = self.var()
        if self.native_xor:
            self.xors.append(([v, abs(a), abs(b)], (a < 0) != (b < 0)))
        else:
            self.clauses += [[-v, a, b], [-v, -a, -b], [v, -a, b], [v, a, -b]]
        return v

    def and_(self, a, b):
        if isinstance(a, bool):
            return b if a else False
        if isinstance(b, bool):
            return a if b else False
        if a == b:
            return a
        if a == -b:
            return False
        v = self.var()
        self.ands += 1
        self.clauses += [[-v, a], [-v, b], [v, -a, -b]]
        return v

    def or_(self, a, b):
        return self.neg(self.and_(self.neg(a), self.neg(b)))

    def maj(self, a, b, c):
        for x, y, z in ((a, b, c), (b, a, c), (c, a, b)):
            if isinstance(x, bool):
                return self.or_(y, z) if x else self.and_(y, z)
        if a == b or a == c:
            return a
        if b == c:
            return b
        if a == -b:
            return c
        if a == -c:
            return b
        if b == -c:
            return a
        v = self.var()
        self.ands += 2
        self.clauses += [[-a, -b, v], [-a, -c, v], [-b, -c, v], [a, b, -v], [a, c, -v], [b, c, -v]]
        return v

    def ch(self, e, f, g):
        """e ? f : g"""
        if isinstance(e, bool):
            return f if e else g
        if isinstance(f, bool) and isinstance(g, bool):
            return e if f and not g else (self.neg(e) if g and not f else f)
        if isinstance(f, bool):                    # f = 1: e or g;  f = 0: not e and g
            return self.or_(e, g) if f else self.and_(self.neg(e), g)
        if isinstance(g, bool):                    # g = 1: not e or f;  g = 0: e and f
            return self.or_(self.neg(e), f) if g else self.and_(e, f)
        if f == g:                                 # (only literals reach here: True == 1 in Python)
            return f
        v = self.var()
        self.ands += 1
        self.clauses += [[-e, -f, v], [-e, f, -v], [e, -g, v], [e, g, -v]]
        return v

    # words: lists of 32 bits, index 0 = least significant
    @staticmethod
    def const(x):
        return [bool((x >> i) & 1) for i in range(32)]

    def fresh(self):
        return [self.var() for _ in range(32)]

    @staticmethod
    def rotr(w, n):
        return [w[(i + n) % 32] for i in range(32)]

    @staticmethod
    def shr(w, n):
        return [w[i + n] if i + n < 32 else False for i in range(32)]

    def xorw(self, *ws):
        out = ws[0]
        for w in ws[1:]:
            out = [self.xor(x, y) for x, y in zip(out, w)]
        return out

    def addw(self, x, y):
        out, c = [], False
        for i in range(32):
            out.append(self.xor(self.xor(x[i], y[i]), c))
            c = self.maj(x[i], y[i], c)
        return out


def build(W_known, unknown, rounds, variant, native_xor, bits=None):
    """Circuit for the chosen version with message words 0..unknown-1 as
    variables, or, if bits is given, only the lowest `bits` bits of word 0
    (unknown is then ignored and the rest of word 0 is known).
    Returns (circuit, unknown words, state words)."""
    carries, knots = VARIANTS[variant]
    C = Circuit(native_xor)
    if bits is not None:
        unknown = 1
        words = [[C.var() for _ in range(bits)] + C.const(W_known[0])[bits:]] + \
                [C.const(W_known[i]) for i in range(1, 16)]
    else:
        words = [C.fresh() if i < unknown else C.const(W_known[i]) for i in range(16)]
    add = C.addw if carries else (lambda x, y: C.xorw(x, y))
    ch = (lambda e, f, g: [C.ch(x, y, z) for x, y, z in zip(e, f, g)]) if knots else \
        (lambda e, f, g: C.xorw(e, f, g))
    mj = (lambda a, b, c: [C.maj(x, y, z) for x, y, z in zip(a, b, c)]) if knots else \
        (lambda a, b, c: C.xorw(a, b, c))
    W = list(words)
    for t in range(16, rounds):
        s0 = C.xorw(C.rotr(W[t - 15], 7), C.rotr(W[t - 15], 18), C.shr(W[t - 15], 3))
        s1 = C.xorw(C.rotr(W[t - 2], 17), C.rotr(W[t - 2], 19), C.shr(W[t - 2], 10))
        W.append(add(add(add(W[t - 16], s0), W[t - 7]), s1))
    a, b, c, d, e, f, g, h = (C.const(v) for v in IV)
    for t in range(rounds):
        S1 = C.xorw(C.rotr(e, 6), C.rotr(e, 11), C.rotr(e, 25))
        T1 = add(add(add(add(h, S1), ch(e, f, g)), C.const(K[t])), W[t])
        S0 = C.xorw(C.rotr(a, 2), C.rotr(a, 13), C.rotr(a, 22))
        T2 = add(S0, mj(a, b, c))
        h, g, f, e, d, c, b, a = g, f, e, add(d, T1), c, b, a, add(T1, T2)
    return C, words[:unknown], [a, b, c, d, e, f, g, h]


def pin_output(C, state, target):
    """Unit clauses fixing the state to the target. False if a constant bit
    already disagrees."""
    for w, x in zip(state, target):
        for i, bit in enumerate(w):
            t = bool((x >> i) & 1)
            if isinstance(bit, bool):
                if bit != t:
                    return False
            else:
                C.clauses.append([bit] if t else [-bit])
    return True


def read_words(model_value, words):
    out = []
    for w in words:
        x = 0
        for i, bit in enumerate(w):
            val = bit if isinstance(bit, bool) else model_value(bit)
            x |= int(val) << i
        out.append(x)
    return out


# ------------------------------------------------------------------ solving

def solve(C, solver, limit):
    """Returns (status, model function or None, seconds).

    The solve runs in a forked child that is killed when the time is up:
    CaDiCaL through PySAT ignores an interrupt from another thread (it keeps the
    interpreter lock), and CryptoMiniSat's own time limit is soft (a first run
    let some solves go past 400 s on a 30 s limit). Killing the child gives both
    the same hard limit."""
    t0 = time.perf_counter()
    rfd, wfd = os.pipe()
    pid = os.fork()
    if pid == 0:                                   # child: never returns
        try:
            os.close(rfd)
            if solver == "cryptominisat":
                import pycryptosat
                s = pycryptosat.Solver(threads=1)
                for cl in C.clauses:
                    s.add_clause(cl)
                for vs, rhs in C.xors:
                    s.add_xor_clause(vs, rhs)
                res, model = s.solve()
                pos = [v for v in range(1, len(model)) if model[v]] if res else []
            else:
                from pysat.solvers import Solver
                s = Solver(name="cadical195", bootstrap_with=C.clauses)
                res = s.solve()
                pos = [l for l in s.get_model() if l > 0] if res else []
            out = b"U" if not res else b"S" + b" ".join(str(l).encode() for l in pos)
            with os.fdopen(wfd, "wb") as fh:
                fh.write(out)
        except BaseException:
            os.write(wfd, b"E")
        finally:
            os._exit(0)
    os.close(wfd)
    data = b""
    eof = False
    deadline = t0 + limit
    with os.fdopen(rfd, "rb", buffering=0) as fh:
        while True:
            left = deadline - time.perf_counter()
            if left <= 0:
                break
            ready, _, _ = select.select([fh], [], [], left)
            if not ready:
                break
            chunk = fh.read(1 << 20)
            if not chunk:
                eof = True
                break
            data += chunk
    dt = time.perf_counter() - t0
    if not eof or not data:
        os.kill(pid, signal.SIGKILL)
        os.waitpid(pid, 0)
        return "timeout", None, dt
    os.waitpid(pid, 0)
    if data[:1] == b"E":
        raise RuntimeError("solver child failed")
    if data[:1] == b"U":
        return "unsat", None, dt
    m = set(int(x) for x in data[1:].split())
    return "solved", (lambda v: v in m), dt


def gauss_salt(W_known, unknown, rounds, target):
    """Solve the salt version by linear algebra over GF(2) directly: the map
    from the unknown bits to the state is affine, so probe it with unit vectors
    and eliminate. Returns (unknown words or None, seconds)."""
    t0 = time.perf_counter()
    nb = 32 * unknown
    base_W = list(W_known)
    for i in range(unknown):
        base_W[i] = 0
    def out_bits(W):
        st = evaluate(W, rounds, "salt")
        return sum(v << (32 * j) for j, v in enumerate(st))
    c0 = out_bits(base_W)
    cols = []
    for j in range(nb):
        W = list(base_W)
        W[j // 32] ^= 1 << (j % 32)
        cols.append(out_bits(W) ^ c0)
    rhs_all = sum(v << (32 * j) for j, v in enumerate(target)) ^ c0
    # rows: 256 equations, each a bitmask over the nb unknowns
    rows = []
    for r in range(256):
        mask = 0
        for j in range(nb):
            if (cols[j] >> r) & 1:
                mask |= 1 << j
        rows.append([mask, (rhs_all >> r) & 1])
    piv = {}
    for mask, b in rows:
        while mask:
            p = mask.bit_length() - 1
            if p not in piv:
                piv[p] = [mask, b]
                break
            mask ^= piv[p][0]
            b ^= piv[p][1]
        else:
            if b:
                return None, time.perf_counter() - t0
    x = 0
    for p in sorted(piv):                         # back-substitute, low pivots first
        mask, b = piv[p]
        rest = mask & ~(1 << p)
        val = b ^ (bin(rest & x).count("1") & 1)
        x |= val << p
    words = [(x >> (32 * i)) & MASK for i in range(unknown)]
    return words, time.perf_counter() - t0
