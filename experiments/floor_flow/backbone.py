"""
Part 8: the backbone. Which pieces are frozen near the wall?

A split is a sign vector s (piece 0 fixed upright, so each split is counted
once). Its gap is |sum s_i a_i|. The K lowest corners of an instance are its K
splits with the smallest gaps, found exactly by meet in the middle: for each
left total l, the K right totals nearest to -l are the only ones that can
enter the global top K.

Measured per instance:
  frozen_opt  fraction of pieces 1..n-1 with the same side in every optimal
              split (gap = floor). 1 when there is a single optimal split.
              Exact when there are at most K optimal splits.
  frozen_K    fraction of pieces 1..n-1 with the same side in all of the K
              lowest corners (K = 8 and 16)
  dist_2nd    flips between the best and the second-best split, as a fraction
              of n (mirror-invariant: min(d, n - d) / n, at most 0.5)
  dist_near   flips from the best split to the nearest of the other K - 1
              lowest corners, as a fraction of n
If the lowest corners were unrelated random splits, frozen_K would be about
2^-(K-1) and the distances would be close to 0.5.
"""

import numpy as np


def _signed_sums(a):
    sums = np.zeros(1, dtype=np.int64)
    for x in a:
        x = np.int64(x)
        sums = np.concatenate([sums + x, sums - x])
    return sums


def _signs(idx, m):
    """Signs for the pieces behind index idx of _signed_sums over m pieces:
    bit j of idx set means piece j is flipped."""
    bits = (idx[:, None] >> np.arange(m)[None, :]) & 1
    return (1 - 2 * bits).astype(np.int8)


def lowest_corners(a, K):
    """The K splits with the smallest gaps: (gaps, signs[K, n]), sorted by gap."""
    a = np.asarray(a, dtype=np.int64)
    n = len(a)
    h = n // 2
    left = a[0] + _signed_sums(a[1:h])          # pieces 1..h-1
    right = _signed_sums(a[h:])                 # pieces h..n-1
    order = np.argsort(right, kind="stable")
    rs = right[order]
    idx = np.searchsorted(rs, -left)
    offs = np.arange(-K, K)
    cand_r = idx[:, None] + offs[None, :]
    ok = (cand_r >= 0) & (cand_r < len(rs))     # each (l, r) pair appears once
    cand_l = np.broadcast_to(np.arange(len(left))[:, None], cand_r.shape)[ok]
    cand_r = cand_r[ok]
    gaps = np.abs(left[cand_l] + rs[cand_r])
    pick = np.argpartition(gaps, K - 1)[:K]
    pick = pick[np.argsort(gaps[pick], kind="stable")]
    pairs = np.stack([cand_l[pick], cand_r[pick]], axis=1)
    gaps = gaps[pick]
    sl = _signs(pairs[:, 0], h - 1)
    sr = _signs(order[pairs[:, 1]], n - h)
    signs = np.concatenate([np.ones((len(pairs), 1), np.int8), sl, sr], axis=1)
    assert np.array_equal(np.abs(signs.astype(np.int64) @ a), gaps)
    return gaps, signs


def frozen(signs):
    """Fraction of pieces 1..n-1 whose side is the same in every row."""
    s = signs[:, 1:]
    return float(np.mean(np.all(s == s[0], axis=0)))


def flips(s, t):
    """Mirror-invariant flip distance between two splits, as a fraction of n."""
    n = len(s)
    d = int(np.sum(s != t))
    return min(d, n - d) / n


def measure(a, K=16):
    gaps, signs = lowest_corners(a, K)
    floor = gaps[0]
    opt = signs[gaps == floor]
    best = signs[0]
    others = [flips(best, signs[j]) for j in range(1, len(signs))]
    return {
        "floor": int(floor),
        "n_opt_in_top": int(len(opt)),
        "frozen_opt": frozen(opt) if len(opt) < K else None,   # None: more optimal splits than K
        "frozen_8": frozen(signs[:8]),
        "frozen_16": frozen(signs[:16]),
        "dist_2nd": others[0],
        "dist_near": min(others),
        "gap_2nd": int(gaps[1]),
    }
