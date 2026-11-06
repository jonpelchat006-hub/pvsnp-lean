"""
Part 10: random 3-XORSAT. Same kind of landscape as 3-SAT, a different leg of
the table.

An instance: n variables and m = alpha n equations x_i + x_j + x_k = b (mod 2),
three distinct variables each, b random. Satisfiability threshold about 0.918;
clustering sets in near 0.818 (Mezard, Ricci-Tersenghi, Zecchina 2003).

Every equation is also written as 4 ordinary 3-SAT clauses, one forbidding each
wrong-parity assignment of its three variables. An assignment then breaks
exactly one clause per equation it breaks, so the part-9 tools (exhaustive
energies and clusters, DPLL) run on it unchanged.

Gaussian elimination over GF(2) solves it directly. Its work is counted as row
operations (one XOR of two equations).
"""

import numpy as np


def random_3xor(rng, n, m):
    var = np.empty((m, 3), dtype=np.int64)
    for i in range(m):
        var[i] = rng.choice(n, size=3, replace=False)
    rhs = rng.integers(0, 2, size=m).astype(np.int64)
    return var, rhs


def to_cnf(var, rhs):
    """4 clauses per equation. sat3's convention: a clause with neg = f is
    broken exactly when its variables take the values f."""
    cv, cn = [], []
    for i in range(var.shape[0]):
        for f in range(8):
            bits = [(f >> j) & 1 for j in range(3)]
            if (sum(bits) & 1) != rhs[i]:          # wrong parity: forbid it
                cv.append(var[i])
                cn.append(bits)
    return np.array(cv, dtype=np.int64).reshape(-1, 3), np.array(cn, dtype=np.int64).reshape(-1, 3)


def gauss(var, rhs, n):
    """Gaussian elimination over GF(2). Returns (satisfiable, row operations)."""
    rows = []
    for i in range(var.shape[0]):
        r = 0
        for v in var[i]:
            r ^= 1 << int(v)
        rows.append((r, int(rhs[i])))
    pivots = {}                                    # pivot bit -> (row, rhs)
    ops = 0
    for r, b in rows:
        while r:
            p = r.bit_length() - 1
            if p not in pivots:
                pivots[p] = (r, b)
                break
            pr, pb = pivots[p]
            r ^= pr
            b ^= pb
            ops += 1
        else:
            if b:                                  # 0 = 1: no solution
                return False, ops
    return True, ops
