"""
Folding: lattice basis reduction (LLL and BKZ) on the pieces.

Embedding (Coster, Joux, LaMacchia, Odlyzko, Schnorr, Stern 1992). For pieces
a_1..a_n and a target s, the basis rows are

    b_i     = (2 e_i,          W * a_i)    i = 1..n
    b_{n+1} = (1, 1, ..., 1,   W * s)

A choice x in {0,1}^n gives  sum x_i b_i - b_{n+1} = (2x - 1, W * (sum x a - s)):
its first n coordinates are all +-1, an orientation of every piece, and its
last coordinate is W times how far the picked total is from the target. A
folded (reduced) basis is made of short vectors, so if a vector with all
first coordinates +-1 and last coordinate 0 exists and is short enough, the
folding tends to bring it out. For PARTITION the target is half the total.

Every answer read out of the folded basis is checked exactly in integers.
"""

import os
import time
from pathlib import Path

import numpy as np
from fpylll import BKZ, LLL, IntegerMatrix
from fpylll.algorithms.bkz2 import BKZReduction  # noqa: F401  (ensures BKZ 2.0 is available)


# BKZ 2.0 pruning strategies from fplll (strategies/default.json). Set
# FPLLL_STRATEGIES to its path; without it BKZ runs without pruning (slower).
STRATEGIES = os.environ.get("FPLLL_STRATEGIES",
                            str(Path(__file__).parent / "strategies" / "default.json"))
if not Path(STRATEGIES).exists():
    STRATEGIES = None


def embed(a, s, W):
    n = len(a)
    rows = []
    for i in range(n):
        r = [0] * (n + 1)
        r[i] = 2
        r[n] = W * int(a[i])
        rows.append(r)
    rows.append([1] * n + [W * int(s)])
    return IntegerMatrix.from_matrix(rows)


def fold(A, method):
    """Reduce A in place. method: 'lll' or an int block size for BKZ.
    Returns wall time in seconds."""
    t = time.perf_counter()
    if method == "lll":
        LLL.reduction(A, delta=0.99)
    else:
        beta = min(int(method), A.nrows)
        kw = {"strategies": STRATEGIES} if STRATEGIES else {}
        par = BKZ.Param(block_size=beta, flags=BKZ.AUTO_ABORT | BKZ.MAX_LOOPS,
                        max_loops=30, **kw)
        BKZ.reduction(A, par)
    return time.perf_counter() - t


def orientations(A, n):
    """Every +-1 orientation readable from the folded basis: single rows and
    sums/differences of two rows whose first n coordinates are all +-1."""
    M = np.array([[A[i, j] for j in range(n)] for i in range(A.nrows)], dtype=np.int64)
    found = []
    ok = np.all(np.abs(M) == 1, axis=1)
    found.extend(M[ok])
    for j in range(M.shape[0]):
        for sgn in (1, -1):
            P = M[j] + sgn * M
            ok = np.all(np.abs(P) == 1, axis=1)
            found.extend(P[ok])
    if not found:
        return np.zeros((0, n), dtype=np.int64)
    return np.unique(np.array(found), axis=0)


def best_partition(a, sigmas):
    """Smallest exact gap |sum sigma_i a_i| among the orientations (None if none)."""
    best = None
    for sg in sigmas:
        g = abs(sum(int(x) * int(s) for x, s in zip(a, sg)))
        if best is None or g < best[0]:
            best = (g, sg)
    return best


def solves_subset(a, s, sigmas):
    """True if some orientation picks a subset summing exactly to s."""
    for sg in sigmas:
        for x in ((1 + sg) // 2, (1 - sg) // 2):
            if sum(int(ai) for ai, xi in zip(a, x) if xi) == int(s):
                return True
    return False
