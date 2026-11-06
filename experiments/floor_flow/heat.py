"""
Heat: let closed branches reopen and swing through pi to the other closure.

A move flips one branch (a full half-turn, theta 0 <-> pi). Moves that bring
the total closer to the wall are always taken. Moves that push it away are
taken with probability exp(-cost / T), where the cost is measured in bits:
log2(|gap after| + 1) - log2(|gap before| + 1). T starts hot and cools
geometrically. With T = infinity every move is taken: heat that never cools,
a blind walk over the corners (the control).

Uses numba if it is installed; otherwise falls back to plain Python (slow).
"""

import math

import numpy as np

try:
    from numba import njit
except ImportError:                     # pragma: no cover
    def njit(*args, **kwargs):
        if args and callable(args[0]):
            return args[0]
        return lambda f: f


@njit(cache=True)
def _anneal(a, s0, steps, T0, T1, seed, checkpoints):
    np.random.seed(seed)
    n = a.shape[0]
    s = s0.copy()
    S = 0
    for i in range(n):
        S += s[i] * a[i]
    best = abs(S)
    best_s = s.copy()
    hot_forever = T0 <= 0.0            # T0 <= 0 means infinite temperature
    ratio = 1.0
    if not hot_forever:
        ratio = (T1 / T0) ** (1.0 / steps)
    T = T0
    rec = np.empty(checkpoints.shape[0], dtype=np.int64)
    ci = 0
    E = math.log2(abs(S) + 1.0)
    for t in range(steps):
        i = np.random.randint(n)
        S2 = S - 2 * s[i] * a[i]
        E2 = math.log2(abs(S2) + 1.0)
        dE = E2 - E
        if hot_forever or dE <= 0.0 or np.random.random() < math.exp(-dE / T):
            s[i] = -s[i]
            S = S2
            E = E2
            if abs(S) < best:
                best = abs(S)
                for j in range(n):
                    best_s[j] = s[j]
        if not hot_forever:
            T *= ratio
        while ci < checkpoints.shape[0] and t + 1 == checkpoints[ci]:
            rec[ci] = best
            ci += 1
    return best, best_s, rec


def anneal(a, start_signs, steps, T0, T1, seed, checkpoints):
    """Returns (best gap, best signs, best gap at each checkpoint)."""
    cps = np.asarray(sorted(checkpoints), dtype=np.int64)
    return _anneal(np.asarray(a, dtype=np.int64), np.asarray(start_signs, dtype=np.int64),
                   int(steps), float(T0), float(T1), int(seed), cps)
