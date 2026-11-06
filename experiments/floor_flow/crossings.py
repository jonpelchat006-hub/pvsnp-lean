"""
Part 14: crossings and blind eyes.

A. Crossings by view (the lifted elimination eye).
   Same task as part 13's bits ladder: the lowest k bits of message word 0 are
   unknown, the other bits and words are known, and the 256-bit working state
   after r rounds is known. Every wire is written as an affine form over GF(2)
   in the unknown bits. XOR, rotation and shifting keep forms affine. A knot
   (an AND inside Ch, Maj or a carry) between two forms that are both still
   undetermined is a CROSSING: one line passes over another, and its output is
   hidden, so it becomes a new unknown (a hidden variable). That is
   linearization: lift each crossing into its own dimension.

   A view is the order the circuit is read in. SHA-256's rounds are written as
   the sequence a_i, e_i (i = -3 .. r); the IV gives a_-3..a_0, e_-3..e_0 and
   the target gives a_(r-3)..a_r, e_(r-3)..e_r. A split at s reads rounds
   1..s forwards from the IV and rounds r..s+1 backwards from the target
   (undoing a round is exact once its message word is known); the two meet at
   a_(s-3)..a_s, e_(s-3)..e_s. s = r is the front view, s = 0 the back view.
   The message schedule is always read forwards.

   Wherever a computed word is already known (target, IV, or the other side at
   the meeting point), its bits are matched as they come out, lowest first, so
   a matched bit can stop the carry above it from crossing. Before every knot
   both inputs are reduced by the equations found so far: a line that is
   already determined does not cross anything.

   At the end the eye eliminates the hidden variables. What is left is the
   number of unknown bits the equations did not pin down, d' (the dimension of
   the candidate set for the k unknown bits). The eye then has 2^d' candidates
   to try. d' = 0: elimination alone finds the answer. d' = k: the hidden lines
   covered the eye completely, and it is back to counting.

B. Blind eyes.
   An eye that is blind to a kind of knot sees the version of SHA-256 with that
   knot taken out. On random messages, how many bits of the real state does it
   still predict, round by round? Eyes: carry-blind (part 13's chmaj),
   Ch/Maj-blind (carries), blind to both (salt). Also run on a version of
   SHA-256 with every rotation amount set to zero (Sigma0, Sigma1, sigma0,
   sigma1 become the identity), to see whether the rotations are what take the
   blind eye's view away.
"""

import numpy as np

from knots import IV, K, MASK, VARIANTS, _rotr_np, evaluate


# ------------------------------------------------------------------ A. the lifted eye

class Eye:
    """Affine forms are Python ints: bit 0 is the constant 1, bits 1..k the
    unknown message bits, higher bits hidden variables (one per crossing).
    Equations (form = 0) are kept in echelon form, pivot = highest bit, so the
    newest hidden variables are eliminated first."""

    def __init__(self, k, x_true, carries, knots):
        self.k = k
        self.nv = k
        self.truth = 1 | sum(((x_true >> i) & 1) << (i + 1) for i in range(k))
        self.piv = {}
        self.pmask = 0
        self.crossings = 0
        self.equations = 0
        self.carries, self.knots = carries, knots
        self.phase = "schedule"
        self.by_phase = {"schedule": 0, "forward": 0, "backward": 0}
        self.open = []                                  # crossings whose hidden line is not yet seen
        self.closed = 0

    # forms
    def value(self, f):
        return bin(f & self.truth).count("1") & 1

    def reduce(self, f):
        m = f & self.pmask
        while m:
            p = m.bit_length() - 1
            f ^= self.piv[p]
            m = f & self.pmask
        return f

    def equate(self, f):
        assert self.value(f) == 0, "the true answer broke an equation"
        f = self.reduce(f)
        if f == 0:
            return
        assert f != 1, "inconsistent"
        p = f.bit_length() - 1
        self.piv[p] = f
        self.pmask |= 1 << p
        self.equations += 1

    def mul(self, u, v):
        u, v = self.reduce(u), self.reduce(v)
        if u <= 1:
            return v if u == 1 else 0
        if v <= 1:
            return u if v == 1 else 0
        if u == v:
            return u
        if u ^ v == 1:
            return 0
        self.nv += 1                                   # a crossing: the output is hidden
        if self.value(u) & self.value(v):
            self.truth |= 1 << self.nv
        self.crossings += 1
        self.by_phase[self.phase] += 1
        self.open.append((self.nv, u, v))
        return 1 << self.nv

    @staticmethod
    def _product(u, v):
        """The product as an affine form when one is constant or they are equal
        or opposite; otherwise None."""
        if u <= 1:
            return v if u == 1 else 0
        if v <= 1:
            return u if v == 1 else 0
        if u == v:
            return u
        if u ^ v == 1:
            return 0
        return None

    def close(self):
        """Once both lines at a crossing are seen (determined, or equal), the
        hidden line is seen too: add z = u*v as a linear equation. Repeat until
        nothing changes."""
        changed = True
        while changed:
            changed = False
            still = []
            for z, u, v in self.open:
                u, v = self.reduce(u), self.reduce(v)
                p = self._product(u, v)
                if p is None:
                    still.append((z, u, v))
                else:
                    self.equate((1 << z) ^ p)
                    self.closed += 1
                    changed = True
            self.open = still

    # words: lists of 32 forms, index = bit position
    @staticmethod
    def const(x):
        return [(x >> i) & 1 for i in range(32)]

    @staticmethod
    def xor(*ws):
        out = [0] * 32
        for w in ws:
            out = [a ^ b for a, b in zip(out, w)]
        return out

    @staticmethod
    def rotr(w, n):
        return [w[(i + n) % 32] for i in range(32)]

    @staticmethod
    def shr(w, n):
        return [w[i + n] if i + n < 32 else 0 for i in range(32)]

    def add(self, x, y, target=None, cin=0):
        if not self.carries:
            out = [a ^ b for a, b in zip(x, y)]
            if cin:                                     # only subtraction uses cin; XOR undoes XOR
                raise ValueError
            if target is not None:
                for o, t in zip(out, target):
                    self.equate(o ^ t)
                self.close()
            return out
        out, c = [], cin
        for i in range(32):
            s = x[i] ^ y[i] ^ c
            if target is not None:
                self.equate(s ^ target[i])              # match this bit before the carry above it
            out.append(s)
            if i < 31:
                c = y[i] ^ self.mul(x[i] ^ y[i], y[i] ^ c)   # Maj(x, y, c)
        if target is not None:
            self.close()
        return out

    def sub(self, x, y, target=None):
        if not self.carries:
            return self.add(x, y, target)
        return self.add(x, [b ^ 1 for b in y], target, cin=1)

    def ch(self, e, f, g):
        if not self.knots:
            return self.xor(e, f, g)
        return [gi ^ self.mul(ei, fi ^ gi) for ei, fi, gi in zip(e, f, g)]

    def maj(self, a, b, c):
        if not self.knots:
            return self.xor(a, b, c)
        return [bi ^ self.mul(ai ^ bi, bi ^ ci) for ai, bi, ci in zip(a, b, c)]

    def S0(self, w):
        return self.xor(self.rotr(w, 2), self.rotr(w, 13), self.rotr(w, 22))

    def S1(self, w):
        return self.xor(self.rotr(w, 6), self.rotr(w, 11), self.rotr(w, 25))

    def s0(self, w):
        return self.xor(self.rotr(w, 7), self.rotr(w, 18), self.shr(w, 3))

    def s1(self, w):
        return self.xor(self.rotr(w, 17), self.rotr(w, 19), self.shr(w, 10))

    def projection_dim(self):
        """d': unknown bits not pinned down once the hidden variables are
        eliminated (pivots at or below bit k involve unknown bits only)."""
        return self.k - sum(1 for p in self.piv if p <= self.k)

    def solve_unknowns(self):
        """When d' = 0: read the unknown bits off the echelon rows."""
        x = {}
        for p in sorted(p for p in self.piv if p <= self.k):
            row = self.piv[p]
            val = row & 1
            for j in range(1, p):
                if (row >> j) & 1:
                    val ^= x[j]
            x[p] = val
        return sum(x[j + 1] << j for j in range(self.k))


def view(W, k, r, variant, s):
    """Read r rounds split at s (s = r: front, s = 0: back), with the lowest k
    bits of W[0] unknown. Returns a dict of counts."""
    assert 4 <= r <= 64 and 0 <= s <= r
    carries, knots = VARIANTS[variant]
    target = evaluate(W, r, variant)
    eye = Eye(k, W[0] & ((1 << k) - 1), carries, knots)
    C = eye.const
    w0 = [(1 << (i + 1)) if i < k else (W[0] >> i) & 1 for i in range(32)]
    Ws = [w0] + [C(W[i]) for i in range(1, 16)]
    for t in range(16, r):                              # schedule, always forwards
        x = eye.add(Ws[t - 16], eye.s0(Ws[t - 15]))
        x = eye.add(x, Ws[t - 7])
        Ws.append(eye.add(x, eye.s1(Ws[t - 2])))
    A, E = {}, {}
    for j in range(4):
        A[-j], E[-j] = C(IV[j]), C(IV[4 + j])
        A[r - j], E[r - j] = C(target[j]), C(target[4 + j])
    eye.phase = "forward"
    for i in range(1, s + 1):
        T1 = eye.add(E[i - 4], eye.S1(E[i - 1]))
        T1 = eye.add(T1, eye.ch(E[i - 1], E[i - 2], E[i - 3]))
        T1 = eye.add(T1, C(K[i - 1]))
        T1 = eye.add(T1, Ws[i - 1])
        T2 = eye.add(eye.S0(A[i - 1]), eye.maj(A[i - 1], A[i - 2], A[i - 3]))
        a = eye.add(T1, T2, A.get(i))
        e = eye.add(A[i - 4], T1, E.get(i))
        A.setdefault(i, a)
        E.setdefault(i, e)
    eye.phase = "backward"
    for i in range(r, s, -1):
        T2 = eye.add(eye.S0(A[i - 1]), eye.maj(A[i - 1], A[i - 2], A[i - 3]))
        T1 = eye.sub(A[i], T2)
        a = eye.sub(E[i], T1, A.get(i - 4))
        R = eye.sub(T1, eye.S1(E[i - 1]))
        R = eye.sub(R, eye.ch(E[i - 1], E[i - 2], E[i - 3]))
        R = eye.sub(R, C(K[i - 1]))
        e = eye.sub(R, Ws[i - 1], E.get(i - 4))
        A.setdefault(i - 4, a)
        E.setdefault(i - 4, e)
    eye.close()
    d = eye.projection_dim()
    solved = ""
    if d == 0:
        solved = int(eye.solve_unknowns() == (W[0] & ((1 << k) - 1)))
        assert solved == 1
    return {"crossings": eye.crossings, "schedule_crossings": eye.by_phase["schedule"],
            "forward_crossings": eye.by_phase["forward"], "backward_crossings": eye.by_phase["backward"],
            "closed": eye.closed, "equations": eye.equations, "pinned": k - d, "d_prime": d,
            "solved": solved}


# ------------------------------------------------------------------ B. blind eyes

def states_by_round(W, variant, rotations, rounds=64):
    """W: 16 uint32 arrays (one entry per message). Yields the 8 state words
    after each round, for the chosen version, with or without rotations."""
    carries, knots = VARIANTS[variant]
    add = (lambda x, y: x + y) if carries else (lambda x, y: x ^ y)
    ch = (lambda e, f, g: (e & f) ^ (~e & g)) if knots else (lambda e, f, g: e ^ f ^ g)
    mj = (lambda a, b, c: (a & b) ^ (a & c) ^ (b & c)) if knots else (lambda a, b, c: a ^ b ^ c)
    if rotations:
        S0 = lambda x: _rotr_np(x, 2) ^ _rotr_np(x, 13) ^ _rotr_np(x, 22)
        S1 = lambda x: _rotr_np(x, 6) ^ _rotr_np(x, 11) ^ _rotr_np(x, 25)
        s0 = lambda x: _rotr_np(x, 7) ^ _rotr_np(x, 18) ^ (x >> np.uint32(3))
        s1 = lambda x: _rotr_np(x, 17) ^ _rotr_np(x, 19) ^ (x >> np.uint32(10))
    else:                                               # every rotation and shift amount set to 0
        S0 = S1 = s0 = s1 = lambda x: x
    W = list(W)
    for t in range(16, rounds):
        W.append(add(add(add(W[t - 16], s0(W[t - 15])), W[t - 7]), s1(W[t - 2])))
    ones = np.ones_like(W[0])
    a, b, c, d, e, f, g, h = (ones * np.uint32(v) for v in IV)
    for t in range(rounds):
        T1 = add(add(add(add(h, S1(e)), ch(e, f, g)), np.uint32(K[t])), W[t])
        T2 = add(S0(a), mj(a, b, c))
        h, g, f, e, d, c, b, a = g, f, e, add(d, T1), c, b, a, add(T1, T2)
        yield t + 1, (a, b, c, d, e, f, g, h)


def bits(words):
    """m uint32 arrays of length N -> (N, 32 m) array of 0/1, word-major, bit 0 first."""
    x = np.stack(words, axis=1)                         # (N, m)
    return ((x[:, :, None] >> np.arange(32, dtype=np.uint32)) & 1).reshape(len(x), 32 * len(words))
