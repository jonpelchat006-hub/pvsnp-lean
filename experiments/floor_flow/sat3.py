"""
Part 9: random 3-SAT next to partition. Is there a sponge?

A random 3-SAT instance: n variables, m = alpha n clauses, each clause three
distinct variables, each negated with chance 1/2. An assignment's energy is
the number of clauses it breaks. Its ground states are the assignments with
the smallest energy (the solutions, when there are any).

Exhaustive (n <= 24): the energy of every one of the 2^n assignments, then
  backbone       fraction of variables with the same value in every ground state
  clusters       ground states joined when they differ in one variable
                 (connected pieces of the solution space)
  frozen inside  for each cluster, the fraction of variables that never change
                 inside it; averaged over clusters weighted by size
  distances      flips between ground states in different clusters

Search work (any n): DPLL with unit propagation, branching on the literal with
the largest Jeroslow-Wang score; work = branch nodes.
"""

import numpy as np
from numba import njit


def random_3sat(rng, n, m):
    """Clauses as (var[m,3], neg[m,3]) with three distinct variables per clause."""
    var = np.empty((m, 3), dtype=np.int64)
    for i in range(m):
        var[i] = rng.choice(n, size=3, replace=False)
    neg = rng.integers(0, 2, size=(m, 3)).astype(np.int64)
    return var, neg


# ------------------------------------------------------------------ exhaustive

@njit(cache=True)
def energies(var, neg, n):
    m = var.shape[0]
    mask = np.zeros(m, dtype=np.int64)
    bad = np.zeros(m, dtype=np.int64)
    for i in range(m):
        for j in range(3):
            mask[i] |= 1 << var[i, j]
            if neg[i, j]:
                bad[i] |= 1 << var[i, j]      # a negated literal is false when the variable is 1
    N = 1 << n
    E = np.zeros(N, dtype=np.uint8)
    for x in range(N):
        e = 0
        for i in range(m):
            if (x & mask[i]) == bad[i]:
                e += 1
        E[x] = min(e, 255)
    return E


@njit(cache=True)
def _clusters(states, n):
    """Union-find over ground states joined by single flips."""
    k = states.shape[0]
    N = 1 << n
    where = -np.ones(N, dtype=np.int64)
    for i in range(k):
        where[states[i]] = i
    parent = np.arange(k)
    for i in range(k):
        x = states[i]
        for v in range(n):
            j = where[x ^ (1 << v)]
            if j >= 0:
                a, b = i, j
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                while parent[b] != b:
                    parent[b] = parent[parent[b]]
                    b = parent[b]
                if a != b:
                    parent[a] = b
    for i in range(k):
        a = i
        while parent[a] != a:
            a = parent[a]
        parent[i] = a
    return parent


def _frozen(states, n):
    """Fraction of variables constant across these states."""
    bits = (states[:, None] >> np.arange(n)[None, :]) & 1
    return float(np.mean(np.all(bits == bits[0], axis=0)))


def structure(var, neg, n, rng, max_pairs=2000):
    E = energies(var, neg, n)
    e0 = int(E.min())
    states = np.flatnonzero(E == e0).astype(np.int64)
    roots = _clusters(states, n)
    labels, sizes = np.unique(roots, return_counts=True)
    frozen_in = []
    for lab, sz in zip(labels, sizes):
        frozen_in.append((_frozen(states[roots == lab], n), sz))
    w = np.array([s for _, s in frozen_in], float)
    f = np.array([fr for fr, _ in frozen_in])
    # flips between ground states in different clusters (sampled pairs)
    between = []
    if len(labels) > 1:
        for _ in range(max_pairs):
            i, j = rng.integers(0, len(states), 2)
            if roots[i] != roots[j]:
                between.append(bin(int(states[i] ^ states[j])).count("1") / n)
    return {
        "energy": e0, "ground": int(len(states)),
        "backbone": _frozen(states, n),
        "clusters": int(len(labels)), "largest_share": float(sizes.max() / len(states)),
        "frozen_inside": float(np.average(f, weights=w)),
        "partly_frozen": float(np.average((f > 0) & (f < 1), weights=w)),
        "between_median": float(np.median(between)) if between else None,
    }


# ------------------------------------------------------------------ DPLL

def dpll(var, neg, n, limit=10 ** 7):
    """Returns (satisfiable, branch nodes). Literal (v, s) is true when x_v == 1 - s."""
    m = var.shape[0]
    want = 1 - neg                    # value that makes each literal true
    nodes = 0

    def propagate(a):
        while True:
            val = a[var]                              # -1 unassigned
            true = val == want
            false = (val >= 0) & ~true
            sat = true.any(axis=1)
            nfalse = false.sum(axis=1)
            if np.any(~sat & (nfalse == 3)):
                return False
            unit = ~sat & (nfalse == 2)
            if not unit.any():
                return True
            rows = np.flatnonzero(unit)
            cols = np.argmax(val[rows] < 0, axis=1)
            v = var[rows, cols]
            w = want[rows, cols]
            # the same variable forced both ways is a conflict
            order = np.argsort(v, kind="stable")
            v, w = v[order], w[order]
            same = v[1:] == v[:-1]
            if np.any(same & (w[1:] != w[:-1])):
                return False
            a[v] = w

    def choose(a):
        val = a[var]
        true = val == want
        open_ = ~true.any(axis=1)
        if not open_.any():
            return None
        un = (val < 0) & open_[:, None]
        k = un.sum(axis=1)
        score = np.zeros((n, 2))
        rr, cc = np.nonzero(un)
        np.add.at(score, (var[rr, cc], want[rr, cc]), 2.0 ** -k[rr])
        flat = int(np.argmax(score))
        return flat // 2, flat % 2

    def solve(a):
        nonlocal nodes
        if not propagate(a):
            return False
        pick = choose(a)
        if pick is None:
            return True
        nodes += 1
        if nodes > limit:
            raise RuntimeError("node limit")
        v, w = pick
        for value in (w, 1 - w):
            b = a.copy()
            b[v] = value
            if solve(b):
                return True
        return False

    a = -np.ones(n, dtype=np.int64)
    return solve(a), nodes
