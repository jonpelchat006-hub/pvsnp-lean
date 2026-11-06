"""
Floor experiment: how close do different methods get to the void wall?

Pieces a_1..a_n (positive integers). An orientation gives each piece a sign.
The gap of an orientation is |sum of signed pieces|. The floor is the smallest
gap any orientation reaches (0 means the pieces can be balanced exactly).

Phase language (Shovelcat closure + inversion): each branch has a phase
theta in [0, pi]; its contribution is a * cos(theta). A branch counts only
when it has closed: theta = 0 (upright, e^{i0} = +1) or theta = pi (flipped,
e^{i pi} = -1). In between it is open.

Methods
  exact_floor        meet in the middle, exact (the true floor)
  greedy             largest piece first, each turned toward 0
  karmarkar_karp     repeatedly let the two largest branches cancel into the
                     void, keeping their difference (largest differencing)
  core_flow          start every branch at the core (theta = pi/2, on the
                     wall), push outward while staying on the wall; a branch
                     locks when it reaches 0 or pi. When one branch is left
                     it is stranded at a partial angle and must be forced to
                     the nearer closure; that forced step is the gap.
                     pressure="even": every open branch pushed alike
                     pressure="sized": push grows with the branch's size, so
                     big branches close first and small ones are left last

Every method returns a sign vector; gaps are recomputed exactly from the signs.
"""

from __future__ import annotations

import heapq
import math

import numpy as np


def gap_of(a: np.ndarray, signs: np.ndarray) -> int:
    """Exact gap from integer pieces and a +/-1 sign vector."""
    assert signs.shape == a.shape
    assert set(np.unique(signs)).issubset({-1, 1})
    return abs(int(sum(int(x) * int(s) for x, s in zip(a, signs))))


# ---------------------------------------------------------------- exact floor

def _all_signed_sums(a: np.ndarray) -> np.ndarray:
    sums = np.zeros(1, dtype=np.int64)
    for x in a:
        x = np.int64(x)
        sums = np.concatenate([sums + x, sums - x])
    return sums


def exact_floor(a: np.ndarray) -> int:
    """Meet in the middle. The first piece is fixed upright (mirror symmetry)."""
    n = len(a)
    if n == 1:
        return int(a[0])
    h = n // 2
    left = int(a[0]) + _all_signed_sums(a[1:h])     # first piece fixed upright
    right = np.sort(_all_signed_sums(a[h:]))
    idx = np.searchsorted(right, -left)
    best = None
    for shift in (0, -1):
        j = np.clip(idx + shift, 0, len(right) - 1)
        g = np.abs(left + right[j]).min()
        best = g if best is None else min(best, g)
    return int(best)


def brute_floor(a: np.ndarray) -> int:
    """Independent check for small n: every orientation."""
    return int(np.abs(_all_signed_sums(a)).min())


# ---------------------------------------------------------------- greedy

def greedy(a: np.ndarray) -> np.ndarray:
    order = np.argsort(-a, kind="stable")
    signs = np.zeros(len(a), dtype=np.int64)
    t = 0
    for i in order:
        s = -1 if t > 0 else 1
        signs[i] = s
        t += s * int(a[i])
    return signs


# ---------------------------------------------------------------- Karmarkar–Karp

def karmarkar_karp(a: np.ndarray) -> np.ndarray:
    """Largest differencing. Each step puts the two largest on opposite sides."""
    n = len(a)
    heap = [(-int(x), i) for i, x in enumerate(a)]
    heapq.heapify(heap)
    adj = [[] for _ in range(n)]
    while len(heap) > 1:
        x1, i1 = heapq.heappop(heap)
        x2, i2 = heapq.heappop(heap)
        adj[i1].append(i2)
        adj[i2].append(i1)
        heapq.heappush(heap, (x1 - x2, i1))      # -(|x1| - |x2|), kept under i1
    # two-colour the difference tree
    signs = np.zeros(n, dtype=np.int64)
    root = heap[0][1]
    signs[root] = 1
    stack = [root]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if signs[v] == 0:
                signs[v] = -signs[u]
                stack.append(v)
    assert np.all(signs != 0)
    return signs


# ---------------------------------------------------------------- core flow

def core_flow(a: np.ndarray, rng: np.random.Generator, pressure: str = "even"):
    """
    Start at the core (all x = cos(theta) = 0, which is on the wall), push in a
    random direction that keeps sum(a * x) = 0, and move until an open branch
    reaches closure (x = +1 or -1, theta = 0 or pi); lock it. Repeat until one
    branch is left. Its x is fixed by the wall; force it to the nearer closure.

    Returns (signs, info) where info has the stranded branch, its angle, and
    how far that angle was from closure.
    """
    n = len(a)
    af = a.astype(np.float64)
    x = np.zeros(n)
    open_ = np.ones(n, dtype=bool)
    locked_sum = 0                                   # exact, integer
    while open_.sum() >= 2:
        idx = np.flatnonzero(open_)
        w = af[idx]
        g = rng.standard_normal(len(idx))
        if pressure == "sized":
            g = g * w / w.max()
        # stay on the wall: remove the component along the pieces
        d = g - w * (w @ g) / (w @ w)
        if rng.random() < 0.5:
            d = -d
        xi = x[idx]
        with np.errstate(divide="ignore", invalid="ignore"):
            t_up = np.where(d > 0, (1.0 - xi) / d, np.inf)
            t_dn = np.where(d < 0, (-1.0 - xi) / d, np.inf)
        t = np.minimum(t_up, t_dn)
        k = int(np.argmin(t))
        x[idx] = xi + t[k] * d
        i = idx[k]
        s = 1 if d[k] > 0 else -1
        x[i] = float(s)
        open_[i] = False
        locked_sum += s * int(a[i])
    last = int(np.flatnonzero(open_)[0])
    # the wall fixes the last branch exactly: a_last * x_last = -locked_sum
    x_last = -locked_sum / int(a[last])
    x_last = max(-1.0, min(1.0, x_last))
    theta = math.acos(x_last)
    s_last = 1 if x_last >= 0 else -1
    signs = np.where(x > 0, 1, -1).astype(np.int64)
    signs[last] = s_last
    info = {
        "last_piece": int(a[last]),
        "last_piece_rank": int((a > a[last]).sum()) + 1,   # 1 = largest
        "theta_last": theta,
        "angle_to_closure": min(theta, math.pi - theta),
    }
    return signs, info


def best_core_flow(a, rng, pressure, runs):
    best = None
    for _ in range(runs):
        s, info = core_flow(a, rng, pressure)
        g = gap_of(a, s)
        if best is None or g < best[0]:
            best = (g, s, info)
    return best


# ---------------------------------------------------------------- nested flow

def flow_until(a: np.ndarray, rng: np.random.Generator, open_left: int, pressure: str = "sized"):
    """The core flow, stopped while `open_left` branches are still open.
    Returns (locked signs as a +/-1 vector, mask of open branches, exact locked sum)."""
    n = len(a)
    af = a.astype(np.float64)
    x = np.zeros(n)
    open_ = np.ones(n, dtype=bool)
    locked_sum = 0
    while open_.sum() > max(open_left, 1):
        idx = np.flatnonzero(open_)
        w = af[idx]
        g = rng.standard_normal(len(idx))
        if pressure == "sized":
            g = g * w / w.max()
        d = g - w * (w @ g) / (w @ w)
        if rng.random() < 0.5:
            d = -d
        xi = x[idx]
        with np.errstate(divide="ignore", invalid="ignore"):
            t_up = np.where(d > 0, (1.0 - xi) / d, np.inf)
            t_dn = np.where(d < 0, (-1.0 - xi) / d, np.inf)
        t = np.minimum(t_up, t_dn)
        k = int(np.argmin(t))
        x[idx] = xi + t[k] * d
        i = idx[k]
        s = 1 if d[k] > 0 else -1
        x[i] = float(s)
        open_[i] = False
        locked_sum += s * int(a[i])
    locked_signs = np.where(x > 0, 1, -1).astype(np.int64)
    return locked_signs, open_, locked_sum


def nested_flow(a: np.ndarray, rng: np.random.Generator, lock_fraction: float,
                pressure: str = "sized") -> np.ndarray:
    """
    Let the flow lock a fraction of the branches. The locked group becomes one
    unit on the next level (its size is the size of its total), and then pairs
    close level by level (largest differencing) over that unit and the branches
    still open. The unit's own orientation is decided by the pairing.
    """
    n = len(a)
    m = int(round(lock_fraction * n))
    m = max(0, min(m, n - 1))
    locked_signs, open_, L = flow_until(a, rng, open_left=n - m, pressure=pressure)
    open_idx = np.flatnonzero(open_)
    items = np.concatenate([[abs(L)], a[open_idx]]).astype(np.int64)
    s_items = karmarkar_karp(items)
    unit_sign = int(s_items[0]) * (1 if L >= 0 else -1)
    signs = np.empty(n, dtype=np.int64)
    locked_mask = ~open_
    signs[locked_mask] = unit_sign * locked_signs[locked_mask]
    signs[open_idx] = s_items[1:]
    return signs
