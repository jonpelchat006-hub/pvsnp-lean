"""
Part 7a: the threshold.

Pieces: n numbers drawn uniformly from 1 .. 2^b - 1. Load kappa = b / n
(bits per piece over number of pieces). A *perfect* split is one whose gap
equals the parity of the total (0 if the total is even, 1 if odd), the
smallest gap any split can have.

For each instance we record:
  count   - the exact number of perfect splits (meet in the middle, each split
            counted once: the first piece is fixed upright)
  floor   - the smallest gap (meet in the middle)
  nodes   - the work of complete Karmarkar-Karp (Korf 1998), a complete search
            that stops as soon as it finds a perfect split, or after it has
            proven the floor. Its floor is checked against meet in the middle.

Predictions compared:
  Mertens (1998): expected number of perfect splits
      E = 2^(n(1-kappa)) * sqrt(6 / (pi n))   (odd total; half that if even)
  so the expected count is 1 at kappa_c(n) = 1 - log2(pi n / 6) / (2n).
  The pi here comes from the bell curve of the signed totals.
"""

import numpy as np
from numba import njit

INT64_MAX = np.iinfo(np.int64).max


@njit(cache=True)
def ckk(a, limit):
    """Complete Karmarkar-Karp. a: int64 pieces sorted largest first.
    Returns (best gap found, nodes visited, finished)."""
    n = a.shape[0]
    total = 0
    for i in range(n):
        total += a[i]
    parity = total & 1
    lists = np.zeros((n + 1, n), dtype=np.int64)
    lens = np.zeros(n + 1, dtype=np.int64)
    child = np.zeros(n + 1, dtype=np.int64)
    for i in range(n):
        lists[0, i] = a[i]
    lens[0] = n
    best = INT64_MAX
    nodes = 0
    d = 0
    while d >= 0:
        m = lens[d]
        if child[d] == 0:
            nodes += 1
            if nodes > limit:
                return best, nodes, False
            rest = 0
            for i in range(1, m):
                rest += lists[d, i]
            if lists[d, 0] >= rest:          # the largest outweighs the rest: a leaf
                diff = lists[d, 0] - rest
                if diff < best:
                    best = diff
                    if best <= parity:
                        return best, nodes, True
                d -= 1
                continue
            child[d] = 1
            x = lists[d, 0] - lists[d, 1]     # first branch: put the two largest apart
            k = 0
            placed = False
            for i in range(2, m):
                if not placed and x >= lists[d, i]:
                    lists[d + 1, k] = x
                    k += 1
                    placed = True
                lists[d + 1, k] = lists[d, i]
                k += 1
            if not placed:
                lists[d + 1, k] = x
            lens[d + 1] = m - 1
            child[d + 1] = 0
            d += 1
        elif child[d] == 1:
            child[d] = 2
            lists[d + 1, 0] = lists[d, 0] + lists[d, 1]   # second branch: together
            for i in range(2, m):
                lists[d + 1, i - 1] = lists[d, i]
            lens[d + 1] = m - 1
            child[d + 1] = 0
            d += 1
        else:
            child[d] = 0
            d -= 1
    return best, nodes, True


def _signed_sums(a):
    sums = np.zeros(1, dtype=np.int64)
    for x in a:
        x = np.int64(x)
        sums = np.concatenate([sums + x, sums - x])
    return sums


def mitm_count(a):
    """(floor, number of perfect splits). The first piece is fixed upright, so
    every split is counted once."""
    a = np.asarray(a, dtype=np.int64)
    n = len(a)
    parity = int(a.sum()) & 1
    h = max(1, n // 2)
    left = a[0] + _signed_sums(a[1:h])
    right = np.sort(_signed_sums(a[h:]))
    idx = np.searchsorted(right, -left)
    floor = None
    for shift in (0, -1):
        j = np.clip(idx + shift, 0, len(right) - 1)
        g = int(np.abs(left + right[j]).min())
        floor = g if floor is None else min(floor, g)
    targets = (0,) if parity == 0 else (-1, 1)
    count = 0
    for t in targets:                       # left + right == t
        need = t - left
        count += int((np.searchsorted(right, need, "right")
                      - np.searchsorted(right, need, "left")).sum())
    return floor, count


def mertens_expected(n, b):
    """Expected number of perfect splits, Gaussian approximation, averaged over
    the parity of the total. Pieces uniform on 1 .. 2^b - 1."""
    M = 2.0 ** b
    second = (M - 1) * (2 * M - 1) / 6.0          # E[a^2] for a uniform on 1..M-1
    sigma = np.sqrt(n * second)
    dens = 1.0 / (np.sqrt(2 * np.pi) * sigma)     # density of the signed total at 0
    even = 2.0 ** n * 2 * dens / 2                # S = 0 on the even lattice, mirror pairs
    odd = 2.0 ** n * 2 * (2 * dens) / 2           # S = +-1 on the odd lattice, mirror pairs
    return 0.5 * even + 0.5 * odd, even, odd


def kappa_c(n):
    return 1 - np.log2(np.pi * n / 6) / (2 * n)
