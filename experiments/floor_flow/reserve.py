"""
Part 7b: the tape's reserve.

Four sheets with one layer of tape (sheets.py), but with exact 64-bit totals
(n <= 56, n-bit pieces: every partial total is below 2^61), so the layer's
modulus M can be any whole number, not only a power of two.

The planted answer x splits as x = x1 + x2 in reps = C(n/4, n/8)^2 ways. A
layer keeps the choices x1 whose total is R mod M (and x2 with T - R mod M),
so on average c = reps / M copies of the answer survive: c is the reserve.
c = 1 keeps one copy on average; c = 1.1416 keeps a 0.1416 (pi - 3) reserve
above one copy.

Cost of one try with a fresh random R:
  probes - entries looked up (|Y| for each of the two layer joins, |L1| for
           the final join); a fixed cost per try, independent of c
  pairs  - matching pairs produced (grows with c)
  pins   - pins in the two layer sheets (grows with c)
and the seconds it takes. The sorted lookup keys of Z mod M are built once per
instance and reused by every try (they do not depend on R).

If a try's chance of keeping a copy is p(c) = 1 - e^(-c) (Poisson) and a try
costs A + B c, the cost per success (A + B c) / (1 - e^(-c)) is smallest where
    e^c - 1 - c = A / B.
"""

from math import comb

import numpy as np

from sheets import leaves


class TryCost:
    def __init__(self):
        self.probes = 0
        self.pairs = 0
        self.pins = 0


def _pairs(sa, ma, order, lo, hi, sb, mb, cost, disjoint):
    counts = hi - lo
    total = int(counts.sum())
    cost.pairs += total
    if total == 0:
        return np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.uint64)
    ai = np.repeat(np.arange(len(sa)), counts)
    starts = np.repeat(lo, counts)
    within = np.arange(total) - np.repeat(np.cumsum(counts) - counts, counts)
    bj = order[starts + within]
    ss = sa[ai] + sb[bj]
    ms = ma[ai] | mb[bj]
    if disjoint:
        keep = (ma[ai] & mb[bj]) == 0
        ss, ms = ss[keep], ms[keep]
    return ss, ms


class Layer:
    """Leaves Y (left half) and Z (right half) and the sorted keys of Z mod M."""

    def __init__(self, a64, n, M):
        h = n // 2
        ys, ym = leaves(a64[:h], n // 8, 0)
        zs, zm = leaves(a64[h:], n // 8, h)
        self.ys, self.ym = ys.astype(np.int64), ym
        self.zs, self.zm = zs.astype(np.int64), zm
        self.M = np.int64(M)
        keys = self.zs % self.M
        self.order = np.argsort(keys, kind="stable")
        self.keys = keys[self.order]

    def join(self, R, cost):
        need = (np.int64(R) - self.ys) % self.M
        lo = np.searchsorted(self.keys, need, "left")
        hi = np.searchsorted(self.keys, need, "right")
        cost.probes += len(self.ys)
        ss, ms = _pairs(self.ys, self.ym, self.order, lo, hi, self.zs, self.zm, cost, False)
        cost.pins += len(ss)
        return ss, ms


def final_join(L1, L2, T, cost):
    s1, m1 = L1
    s2, m2 = L2
    order = np.argsort(s2, kind="stable")
    keys = s2[order]
    need = np.int64(T) - s1
    lo = np.searchsorted(keys, need, "left")
    hi = np.searchsorted(keys, need, "right")
    cost.probes += len(s1)
    return _pairs(s1, m1, order, lo, hi, s2, m2, cost, True)


def verified(a, T, masks):
    n = len(a)
    for m in masks[:1000]:
        m = int(m)
        if sum(a[i] for i in range(n) if (m >> i) & 1) == T:
            return m
    return None


def reps_of(n):
    return comb(n // 4, n // 8) ** 2


def one_try(layer, a, T, rng, cost):
    M = int(layer.M)
    R1 = int(rng.integers(0, M))
    R2 = (T - R1) % M
    L1 = layer.join(R1, cost)
    L2 = layer.join(R2, cost)
    F = final_join(L1, L2, T, cost)
    return verified(a, T, F[1])
