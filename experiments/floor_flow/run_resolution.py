"""
Part 4: the observer's resolution.

An observer with step size delta sees each piece only as whole steps:
q_i = a_i // delta. The rest, r_i = a_i % delta, is below its resolution.
It solves its coarse problem exactly with the grid of reachable totals, and
the grid has one cell per coarse total, so its work is n * (sum q_i + 1).

The relative resolution h is set so the guarantee in PvsNP/Resolution.lean
gives a true gap within h * total of the floor:
    delta = max(1, floor(h * total / (2 n)))
    true gap  <=  floor + 2 * sum r_i  <=  floor + 2 n (delta - 1)  <  floor + h * total

h runs from the framework's information quantum h_info = (sqrt(pi) - sqrt(phi)) / pi
~ 0.159 down to 2^-44.

For each (instance, h):
  * the coarse-optimal orientation (exact, by meet in the middle on q), its true
    gap, and a check of the guarantee;
  * the grid's work, n * (sum q + 1), and, when the grid has at most 2^24
    cells per layer, an actual grid run (timed) whose coarse optimum must match;
  * whether the observer "sees the wire on the wall": delta * coarse floor <= sum r.

Instances: the part-2 density-1 instances (seed 20261030), n = 16..40, 30 each.
Usage:  python run_resolution.py
"""

import csv
import json
import math
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).parent
SIZES = [16, 20, 24, 28, 32, 36, 40]
INSTANCES = 30
INSTANCE_SEED = 20261030
H_INFO = (math.sqrt(math.pi) - math.sqrt((1 + math.sqrt(5)) / 2)) / math.pi
RESOLUTIONS = [("h_info", H_INFO)] + [(f"2^-{k}", 2.0 ** -k) for k in range(4, 45, 4)]
GRID_RUN_MAX_WIDTH = 2 ** 24


def signed_sums(a):
    s = np.zeros(1, dtype=np.int64)
    for x in a:
        s = np.concatenate([s + np.int64(x), s - np.int64(x)])
    return s


def mitm_best(a):
    """Exact optimal orientation and gap, by meet in the middle.
    Returns (gap, signs) with signs as a list of +-1."""
    a = [int(x) for x in a]
    n = len(a)
    h = n // 2
    left, right = a[:h], a[h:]
    L = signed_sums(left)
    R = signed_sums(right)
    order = np.argsort(R, kind="stable")
    Rs = R[order]
    idx = np.searchsorted(Rs, -L)
    best = None
    for shift in (0, -1):
        j = np.clip(idx + shift, 0, len(Rs) - 1)
        g = np.abs(L + Rs[j])
        k = int(np.argmin(g))
        if best is None or g[k] < best[0]:
            best = (int(g[k]), k, int(order[j[k]]))
    gap, li, ri = best

    def decode(index, m):
        # signed_sums doubles the list for each piece in turn (first half +x,
        # second half -x), so piece i's sign is bit i of the index (1 = minus).
        return [1 if (index >> i) & 1 == 0 else -1 for i in range(m)]

    signs = decode(li, len(left)) + decode(ri, len(right))
    assert abs(sum(s * x for s, x in zip(signs, a))) == gap
    return gap, signs


def grid_best(q):
    """The grid of reachable totals on the coarse pieces, run for real.
    Returns (coarse gap, signs)."""
    total = sum(q)
    layers = [1]
    for x in q:
        layers.append(layers[-1] | (layers[-1] << x))
    half = total // 2
    below = layers[-1] & ((1 << (half + 1)) - 1)
    T = below.bit_length() - 1                  # the largest reachable total <= half
    picked = [False] * len(q)
    for i in range(len(q) - 1, -1, -1):
        if (layers[i] >> T) & 1:
            continue
        picked[i] = True
        T -= q[i]
    assert T == 0
    signs = [1 if p else -1 for p in picked]
    return abs(sum(s * x for s, x in zip(signs, q))), signs


def main():
    inst_rng = np.random.default_rng(INSTANCE_SEED)
    rows = []
    t0 = time.time()
    for n in SIZES:
        for k in range(INSTANCES):
            a = [int(x) for x in inst_rng.integers(1, 2 ** n, size=n, dtype=np.int64)]
            total = sum(a)
            floor, _ = mitm_best(a)
            for name, h in RESOLUTIONS:
                delta = max(1, int(h * total / (2 * n)))
                q = [x // delta for x in a]
                r = [x % delta for x in a]
                width = sum(q) + 1
                coarse_gap, signs = mitm_best(q)
                true_gap = abs(sum(s * x for s, x in zip(signs, a)))
                assert true_gap >= floor
                assert true_gap <= floor + 2 * sum(r) <= floor + 2 * n * (delta - 1)
                assert true_gap < floor + h * total or delta == 1
                grid_seconds = ""
                if width <= GRID_RUN_MAX_WIDTH:
                    t = time.perf_counter()
                    g_gap, g_signs = grid_best(q)
                    grid_seconds = round(time.perf_counter() - t, 5)
                    assert g_gap == coarse_gap
                rows.append({
                    "n": n, "instance": k, "total": total, "floor": floor,
                    "resolution": name, "h": h, "delta": delta,
                    "grid_cells": n * width, "grid_seconds": grid_seconds,
                    "coarse_gap": coarse_gap, "invisible_sum": sum(r),
                    "true_gap": true_gap,
                    "sees_on_wall": int(delta * coarse_gap <= sum(r)),
                })
        print(f"n={n} done ({time.time() - t0:.0f}s)", flush=True)

    with open(HERE / "results_resolution.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    summary = {}
    for n in SIZES:
        entry = {}
        for name, h in RESOLUTIONS:
            rs = [r for r in rows if r["n"] == n and r["resolution"] == name]
            run = [r for r in rs if r["grid_seconds"] != ""]
            entry[name] = {
                "median_delta": float(np.median([r["delta"] for r in rs])),
                "median_log2_grid_cells": float(np.median(np.log2([r["grid_cells"] for r in rs]))),
                "median_true_gap_bits": float(np.median(np.log2(np.array([r["true_gap"] for r in rs], float) + 1))),
                "reaches_floor": int(sum(r["true_gap"] == r["floor"] for r in rs)),
                "sees_on_wall": int(sum(r["sees_on_wall"] for r in rs)),
                "grid_runs": len(run),
                "median_grid_seconds": float(np.median([r["grid_seconds"] for r in run])) if run else None,
            }
        entry["floor_bits"] = float(np.median(np.log2(np.array(
            [r["floor"] for r in rows if r["n"] == n and r["resolution"] == "h_info"], float) + 1)))
        summary[n] = entry
    with open(HERE / "summary_resolution.json", "w") as f:
        json.dump({"instance_seed": INSTANCE_SEED, "h_info": H_INFO,
                   "resolutions": RESOLUTIONS, "summary": summary}, f, indent=2)
    print("done")


if __name__ == "__main__":
    main()
