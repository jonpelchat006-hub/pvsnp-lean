"""
Sheets of pins: meet in the middle and the representation technique.

The problem: n pieces a_i, a target T, and a hidden answer x in {0,1}^n with
a . x = T. The answer is planted with exactly n/4 ones in each half of the
positions (the "balanced" assumption used by Howgrave-Graham and Joux).

A *sheet* is a list of pins. Each pin is a choice of pieces (stored as a bit
mask) together with its total (stored mod 2^64; every answer is checked again
exactly in Python integers).

  2 sheets (meet in the middle): all choices of n/4 pieces from the left half
     and from the right half; fold one against the other and look for totals
     that add to exactly T.

  4 sheets (one layer of tape): split the answer x = x1 + x2, each with n/8
     ones per half. Many splits (representations) exist. Lift one layer: keep
     only choices x1 whose total is R mod M1, and x2 with T - R mod M1. M1 is
     about the number of representations, so about one survives.
     Leaves: choices of n/8 pieces in each half (4 sheets: 2 for x1, 2 for x2).

  8 sheets (two layers of tape): split again, x1 = u + v with n/16 ones per
     half each, and lift a thinner layer mod M2 first. Leaves: choices of
     n/16 pieces in each half (8 sheets). This is the Howgrave-Graham-Joux
     structure; its predicted cost is about 2^(0.337 n).

Moduli are powers of two, so totals stored mod 2^64 have consistent residues.
"""

from itertools import chain, combinations
from math import comb

import numpy as np

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)


class Work:
    """Counts pins built and pairs examined."""

    def __init__(self):
        self.pins = 0
        self.pairs = 0
        self.largest = 0

    def sheet(self, s):
        self.pins += len(s[0])
        self.largest = max(self.largest, len(s[0]))
        return s


def leaves(vals, w, offset):
    """All choices of w pieces from vals (positions offset..offset+len-1)."""
    h = len(vals)
    if w == 0:
        return np.zeros(1, dtype=U64), np.zeros(1, dtype=U64)
    cnt = comb(h, w)
    idx = np.fromiter(chain.from_iterable(combinations(range(h), w)),
                      dtype=np.int64, count=cnt * w).reshape(cnt, w)
    sums = np.asarray(vals, dtype=U64)[idx].sum(axis=1, dtype=U64)
    masks = (U64(1) << (idx.astype(U64) + U64(offset))).sum(axis=1, dtype=U64)
    return sums, masks


def join(A, B, M_bits, r, work, disjoint=True, limit=60_000_000):
    """Pairs (a, b) with a.total + b.total = r mod 2^M_bits (M_bits = 64 means
    exact mod 2^64). Returns the merged sheet."""
    sa, ma = A
    sb, mb = B
    mask = ALL if M_bits >= 64 else U64((1 << M_bits) - 1)
    kb = sb & mask
    order = np.argsort(kb, kind="stable")
    kb_s = kb[order]
    need = (U64(r) - sa) & mask
    lo = np.searchsorted(kb_s, need, "left")
    hi = np.searchsorted(kb_s, need, "right")
    counts = hi - lo
    total = int(counts.sum())
    work.pairs += total
    if total > limit:
        raise MemoryError(f"join would produce {total} pairs")
    if total == 0:
        return np.zeros(0, dtype=U64), np.zeros(0, dtype=U64)
    ai = np.repeat(np.arange(len(sa)), counts)
    starts = np.repeat(lo, counts)
    within = np.arange(total) - np.repeat(np.cumsum(counts) - counts, counts)
    bj = order[starts + within]
    ms = ma[ai] | mb[bj]
    ss = sa[ai] + sb[bj]
    if disjoint:
        keep = (ma[ai] & mb[bj]) == 0
        ss, ms = ss[keep], ms[keep]
    return ss, ms


def dedupe(S):
    s, m = S
    _, i = np.unique(m, return_index=True)
    return s[i], m[i]


def check(a, T, masks):
    """Exact check in Python integers. Returns a verified answer mask or None."""
    n = len(a)
    for m in masks[:1000]:
        m = int(m)
        if sum(a[i] for i in range(n) if (m >> i) & 1) == T:
            return m
    return None


def two_sheets(a, T, a64, T64, rng):
    n = len(a)
    h = n // 2
    work = Work()
    A = work.sheet(leaves(a64[:h], n // 4, 0))
    B = work.sheet(leaves(a64[h:], n // 4, h))
    F = join(A, B, 64, T64, work)
    return check(a, T, F[1]), work, 1


def four_sheets(a, T, a64, T64, rng, max_tries=40, slack=0):
    """slack s: the tape layer keeps about 2^s representations of the answer."""
    n = len(a)
    h = n // 2
    reps1 = comb(n // 4, n // 8) ** 2
    m1 = max(1, reps1.bit_length() - 1 - slack)   # M1 = 2^m1 <= reps1 / 2^slack
    work = Work()
    Y = work.sheet(leaves(a64[:h], n // 8, 0))
    Z = work.sheet(leaves(a64[h:], n // 8, h))
    for tries in range(1, max_tries + 1):
        R1 = int(rng.integers(0, 1 << m1))
        R2 = (T64 - R1) % (1 << m1)
        L1 = work.sheet(join(Y, Z, m1, R1, work))
        L2 = work.sheet(join(Y, Z, m1, R2, work))
        F = join(L1, L2, 64, T64, work)
        x = check(a, T, F[1])
        if x is not None:
            return x, work, tries
    return None, work, max_tries


def eight_sheets(a, T, a64, T64, rng, max_tries=40, slack=0):
    n = len(a)
    h = n // 2
    reps1 = comb(n // 4, n // 8) ** 2
    reps2 = comb(n // 8, n // 16) ** 2
    m2 = max(1, reps2.bit_length() - 1 - slack)
    m1 = max(m2, reps1.bit_length() - 1 - slack)
    work = Work()
    Y = work.sheet(leaves(a64[:h], n // 16, 0))
    Z = work.sheet(leaves(a64[h:], n // 16, h))
    for tries in range(1, max_tries + 1):
        R1 = int(rng.integers(0, 1 << m1))
        R2 = (T64 - R1) % (1 << m1)
        halves = []
        for R in (R1, R2):
            Ra = int(rng.integers(0, 1 << m2))
            Rb = (R - Ra) % (1 << m2)
            La = work.sheet(join(Y, Z, m2, Ra, work))
            Lb = work.sheet(join(Y, Z, m2, Rb, work))
            halves.append(work.sheet(dedupe(join(La, Lb, m1, R, work))))
        F = join(halves[0], halves[1], 64, T64, work)
        x = check(a, T, F[1])
        if x is not None:
            return x, work, tries
    return None, work, max_tries


def planted_instance(rng, n):
    bits = n
    a = [int(v) for v in rng.integers(1, 2 ** bits, size=n, dtype=np.uint64)]
    h = n // 2
    left = rng.choice(h, size=n // 4, replace=False)
    right = h + rng.choice(h, size=n // 4, replace=False)
    x = np.zeros(n, dtype=int)
    x[left] = 1
    x[right] = 1
    T = sum(ai for ai, xi in zip(a, x) if xi)
    a64 = np.array(a, dtype=U64)
    return a, T, a64, T % (1 << 64)
