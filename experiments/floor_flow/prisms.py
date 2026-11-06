"""
Part 12: prisms meeting at the wall (meet in the middle).

A. Double encryption. Speck32/64 (Beaulieu et al. 2013; 22 rounds on two
   16-bit words), vectorized over keys with numpy and checked against the
   published test vector. A toy key of k bits fills the low bits of the 64-bit
   key. Double encryption: C = E_k2(E_k1(P)), two independent k-bit keys.
     brute force       try every (k1, k2): 2^(2k) encryptions
     meet in middle    encrypt P under every k1, decrypt C under every k2,
                       match the middles, check survivors on a second pair:
                       about 2 * 2^k cipher calls, and a table of 2^k middles

B. Even-Mansour. E(x) = k2 xor P(x xor k1) on n-bit blocks, with P a public
   scramble (a 4-round Feistel network with random round tables, which is a
   pseudorandom permutation by Luby-Rackoff) and two secret n-bit keys.
     key search        guess k1 (k2 follows from one query): 2^n calls of P
     Daemen's attack   query pairs (x, x xor D); the outer key cancels in
                       E(x) xor E(x xor D). Compute P(u) xor P(u xor D) offline
                       for random u and match the two sets: about 2^(n/2)
                       queries and 2^(n/2) calls of P (Daemen 1991)
"""

import numpy as np

U16 = np.uint16


# ------------------------------------------------------------------ Speck32/64

def _ror(x, r):
    return (x >> U16(r)) | (x << U16(16 - r))


def _rol(x, r):
    return (x << U16(r)) | (x >> U16(16 - r))


def round_keys(key64):
    """key64: uint64 array of keys (k0 = bits 0-15, l0 = 16-31, l1 = 32-47,
    l2 = 48-63). Returns (22, N) uint16 round keys."""
    key64 = np.asarray(key64, dtype=np.uint64)
    k = (key64 & np.uint64(0xFFFF)).astype(U16)
    ls = [((key64 >> np.uint64(16 * (j + 1))) & np.uint64(0xFFFF)).astype(U16) for j in range(3)]
    out = np.empty((22, key64.shape[0]), dtype=U16)
    with np.errstate(over="ignore"):
        for i in range(22):
            out[i] = k
            if i == 21:
                break
            new_l = (k + _ror(ls[i % 3], 7)) ^ U16(i)
            ls[i % 3] = new_l
            k = _rol(k, 2) ^ new_l
    return out


def encrypt(x, y, rk):
    with np.errstate(over="ignore"):
        for i in range(22):
            x = (_ror(x, 7) + y) ^ rk[i]
            y = _rol(y, 2) ^ x
    return x, y


def decrypt(x, y, rk):
    with np.errstate(over="ignore"):
        for i in range(21, -1, -1):
            y = _ror(y ^ x, 2)
            x = _rol((x ^ rk[i]) - y, 7)
    return x, y


def check_speck():
    """Published test vector: key 1918 1110 0908 0100, plaintext 6574 694c,
    ciphertext a868 42f2."""
    key = np.array([0x1918111009080100], dtype=np.uint64)
    rk = round_keys(key)
    cx, cy = encrypt(np.array([0x6574], U16), np.array([0x694c], U16), rk)
    px, py = decrypt(cx, cy, rk)
    return (int(cx[0]), int(cy[0])) == (0xa868, 0x42f2) and (int(px[0]), int(py[0])) == (0x6574, 0x694c)


def enc32(block, keys):
    """Encrypt one 32-bit block (or one per key) under an array of keys."""
    rk = round_keys(keys)
    b = np.broadcast_to(np.asarray(block, dtype=np.uint32), keys.shape)
    x, y = encrypt((b >> np.uint32(16)).astype(U16), (b & np.uint32(0xFFFF)).astype(U16), rk)
    return (x.astype(np.uint32) << np.uint32(16)) | y.astype(np.uint32)


def dec32(block, keys):
    rk = round_keys(keys)
    b = np.broadcast_to(np.asarray(block, dtype=np.uint32), keys.shape)
    x, y = decrypt((b >> np.uint32(16)).astype(U16), (b & np.uint32(0xFFFF)).astype(U16), rk)
    return (x.astype(np.uint32) << np.uint32(16)) | y.astype(np.uint32)


def double_enc(block, k1, k2):
    return int(enc32(enc32(block, np.array([k1], np.uint64)), np.array([k2], np.uint64))[0])


CHUNK = 1 << 20


def brute_force(k, pairs):
    """Every (k1, k2). Returns (found key pairs, encryptions)."""
    (P1, C1), (P2, C2) = pairs
    keys = np.arange(1 << k, dtype=np.uint64)
    mids = enc32(P1, keys)                                   # 2^k
    found, calls = [], 1 << k
    for k1 in range(1 << k):
        out = enc32(np.full(1 << k, mids[k1], np.uint32), keys)   # 2^k per k1
        calls += 1 << k
        for k2 in np.flatnonzero(out == C1):
            if double_enc(P2, k1, int(k2)) == C2:
                found.append((k1, int(k2)))
            calls += 2
    return found, calls


def meet_in_middle(k, pairs):
    """Returns (found key pairs, cipher calls, survivors of the first match)."""
    (P1, C1), (P2, C2) = pairs
    n = 1 << k
    fwd = np.empty(n, np.uint32)
    for s in range(0, n, CHUNK):
        ks = np.arange(s, min(n, s + CHUNK), dtype=np.uint64)
        fwd[s:s + len(ks)] = enc32(P1, ks)
    order = np.argsort(fwd, kind="stable")
    fs = fwd[order]
    found, survivors, calls = [], 0, 2 * n
    for s in range(0, n, CHUNK):
        ks = np.arange(s, min(n, s + CHUNK), dtype=np.uint64)
        back = dec32(C1, ks)
        lo = np.searchsorted(fs, back, "left")
        hi = np.searchsorted(fs, back, "right")
        for j in np.flatnonzero(hi > lo):
            for k1 in order[lo[j]:hi[j]]:
                survivors += 1
                calls += 2
                if double_enc(P2, int(k1), int(ks[j])) == C2:
                    found.append((int(k1), int(ks[j])))
    return found, calls, survivors


# ------------------------------------------------------------------ Even-Mansour

class Feistel:
    """A public 4-round Feistel permutation on n bits with random tables."""

    def __init__(self, n, rng):
        assert n % 2 == 0
        self.h = n // 2
        self.mask = np.uint64((1 << self.h) - 1)
        self.T = [rng.integers(0, 1 << self.h, size=1 << self.h, dtype=np.uint64) for _ in range(4)]
        self.calls = 0

    def __call__(self, x):
        x = np.asarray(x, dtype=np.uint64)
        self.calls += x.size
        L, R = x >> np.uint64(self.h), x & self.mask
        for T in self.T:
            L, R = R, L ^ T[R]
        return (L << np.uint64(self.h)) | R


class EvenMansour:
    def __init__(self, P, k1, k2):
        self.P, self.k1, self.k2 = P, np.uint64(k1), np.uint64(k2)
        self.queries = 0

    def __call__(self, x):
        x = np.asarray(x, dtype=np.uint64)
        self.queries += x.size
        calls = self.P.calls
        out = self.P(x ^ self.k1) ^ self.k2
        self.P.calls = calls                     # the oracle's own work is not the attacker's
        return out


def key_search(E, P, n, rng):
    """Guess k1; k2 follows from one query; a second query filters the
    guesses and three more confirm the survivors (two queries alone leave
    about one wrong key pair)."""
    xs = rng.integers(0, 1 << n, size=5, dtype=np.uint64)
    es = E(xs)
    for s in range(0, 1 << n, CHUNK):
        k1 = np.arange(s, min(1 << n, s + CHUNK), dtype=np.uint64)
        k2 = P(xs[0] ^ k1) ^ es[0]
        for i in np.flatnonzero((P(xs[1] ^ k1) ^ k2) == es[1]):
            if np.array_equal(P(xs[2:] ^ k1[i]) ^ k2[i], es[2:]):
                return int(k1[i]), int(k2[i])
    return None


def daemen(E, P, n, rng, start=1.0):
    """Daemen's attack with sets of size start * 2^(n/2), doubled until it
    succeeds."""
    D = np.uint64(rng.integers(1, 1 << n))
    size = int(start * 2 ** (n / 2))
    while True:
        X = rng.integers(0, 1 << n, size=size, dtype=np.uint64)
        dE = E(X) ^ E(X ^ D)
        Uu = rng.integers(0, 1 << n, size=size, dtype=np.uint64)
        PU, PUD = P(Uu), P(Uu ^ D)
        dP = PU ^ PUD
        order = np.argsort(dP, kind="stable")
        ds = dP[order]
        lo = np.searchsorted(ds, dE, "left")
        hi = np.searchsorted(ds, dE, "right")
        xt = rng.integers(0, 1 << n, size=2, dtype=np.uint64)
        et = E(xt)
        for i in np.flatnonzero(hi > lo):
            for j in order[lo[i]:hi[i]]:
                for u, pu in ((Uu[j], PU[j]), (Uu[j] ^ D, PUD[j])):
                    k1 = X[i] ^ u
                    k2 = E(np.array([X[i]]))[0] ^ pu
                    if np.array_equal(P(xt ^ k1) ^ k2, et):
                        return int(k1), int(k2)
        size *= 2
