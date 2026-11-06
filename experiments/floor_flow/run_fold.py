"""
Part 3: folding (lattice reduction, LLL and BKZ with growing block size).

A. Planted answers. n pieces of n/density bits, with a planted half-subset
   whose total is the target. Does folding bring the answer out? Success is
   an exact subset with the target total, read from the folded basis.
B. The part-2 density-1 PARTITION instances (same generator, same seed).
   How close do the orientations read from the folded basis get to the wall?

For each folded basis the shortest vector is also classified branch by
branch: closed (turned exactly once, coefficient +-1), open (coefficient 0,
left at the core), or over-turned (|coefficient| >= 2).

Usage:  FPLLL_STRATEGIES=/path/to/fplll/strategies/default.json python run_fold.py
"""

import csv
import json
import time
from pathlib import Path

import numpy as np

from floor_flow import exact_floor, gap_of, karmarkar_karp
from lattice import STRATEGIES, best_partition, embed, fold, orientations, solves_subset

HERE = Path(__file__).parent
A_SIZES = [30, 40, 50, 60, 70, 80]
A_DENSITIES = [0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1]
A_TRIALS = 10
A_SEED = 31337
B_SIZES = [16, 20, 24, 28, 32, 36, 40]
B_INSTANCES = 30
B_INSTANCE_SEED = 20261030           # the part-2 instances
METHODS = ["lll", 10, 20, 30, 40, 50]
W_PLANTED = None                     # None means W = n
W_PARTITION = 8                      # chosen on tuning instances (seed 777)


def methods_for(dim):
    out, seen = [], set()
    for m in METHODS:
        key = "lll" if m == "lll" else min(m, dim)
        if key not in seen:
            seen.add(key)
            out.append(key)
    return out


def shortest_structure(A, n):
    """Branch-by-branch reading of the shortest folded vector. Vectors whose
    branch coordinates are all 0 are skipped: when the target is exactly half
    the total the basis is linearly dependent and folding produces a zero
    vector (and, for an odd total, the trivial vector (0, ..., 0, +-W))."""
    rows = [[A[i, j] for j in range(n + 1)] for i in range(A.nrows)]
    rows = [r for r in rows if any(x != 0 for x in r[:n])]
    v = min(rows, key=lambda r: sum(x * x for x in r))
    first = v[:n]
    if all(x % 2 == 0 for x in first):
        c = [x // 2 for x in first]
        opened = sum(1 for x in c if x == 0)
        closed = sum(1 for x in c if abs(x) == 1)
        over = n - opened - closed
    else:                              # uses the target row: entries are odd
        opened = 0
        closed = sum(1 for x in first if abs(x) == 1)
        over = n - closed
    return opened, closed, over


def big_pieces(rng, n, bits):
    return [int.from_bytes(rng.bytes(32), "big") % (2 ** bits - 1) + 1 for _ in range(n)]


def part_a():
    rng = np.random.default_rng(A_SEED)
    rows, t0 = [], time.time()
    for n in A_SIZES:
        for d in A_DENSITIES:
            bits = round(n / d)
            for k in range(A_TRIALS):
                a = big_pieces(rng, n, bits)
                x = np.zeros(n, dtype=int)
                x[rng.permutation(n)[: n // 2]] = 1
                s = sum(ai for ai, xi in zip(a, x) if xi)
                W = W_PLANTED or n
                for m in methods_for(n + 1):
                    A = embed(a, s, W)
                    t = fold(A, m)
                    sig = orientations(A, n)
                    o, c, ov = shortest_structure(A, n)
                    rows.append({"n": n, "density": d, "bits": bits, "trial": k,
                                 "method": "LLL" if m == "lll" else f"BKZ-{m}",
                                 "seconds": round(t, 4), "solved": int(solves_subset(a, s, sig)),
                                 "short_open": o, "short_closed": c, "short_over": ov})
            print(f"A n={n} d={d} done ({time.time() - t0:.0f}s)", flush=True)
    return rows


def part_b():
    inst_rng = np.random.default_rng(B_INSTANCE_SEED)
    rows, t0 = [], time.time()
    for n in B_SIZES:
        for k in range(B_INSTANCES):
            a = inst_rng.integers(1, 2 ** n, size=n, dtype=np.int64)
            total = int(a.sum())
            floor = exact_floor(a)
            kk = gap_of(a, karmarkar_karp(a))
            for m in methods_for(n + 1):
                A = embed(a, total // 2, W_PARTITION)
                t = fold(A, m)
                sig = orientations(A, n)
                best = best_partition(a, sig)
                gap = best[0] if best else None
                if best:
                    assert gap == gap_of(a, best[1].astype(np.int64)) and gap >= floor
                o, c, ov = shortest_structure(A, n)
                rows.append({"n": n, "instance": k, "total": total, "floor": floor,
                             "karmarkar_karp": kk,
                             "method": "LLL" if m == "lll" else f"BKZ-{m}",
                             "seconds": round(t, 4), "orientations_read": len(sig),
                             "gap": gap if gap is not None else "",
                             "short_open": o, "short_closed": c, "short_over": ov})
        print(f"B n={n} done ({time.time() - t0:.0f}s)", flush=True)
    return rows


def write(rows, name):
    with open(HERE / name, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def read(name):
    with open(HERE / name) as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        for k, v in r.items():
            if k in ("method",):
                continue
            if v == "":
                continue
            r[k] = float(v) if k in ("density", "seconds") else int(v)
    return rows


def main(parts="AB"):
    print("BKZ pruning strategies:", STRATEGIES, flush=True)
    if "B" in parts:
        write(part_b(), "results_fold_partition.csv")
    if "A" in parts:
        write(part_a(), "results_fold_planted.csv")
    rows_a = read("results_fold_planted.csv")
    rows_b = read("results_fold_partition.csv")

    summary = {"planted": {}, "partition": {}}
    for n in A_SIZES:
        for m in sorted({r["method"] for r in rows_a if r["n"] == n},
                        key=lambda s: (s != "LLL", int(s[4:]) if s != "LLL" else 0)):
            rs = [r for r in rows_a if r["n"] == n and r["method"] == m]
            by_d = {d: float(np.mean([r["solved"] for r in rs if r["density"] == d]))
                    for d in A_DENSITIES}
            reach = max([d for d, p in by_d.items() if p >= 0.5], default=None)
            summary["planted"][f"{n}/{m}"] = {
                "success_by_density": by_d,
                "highest_density_solved_half_the_time": reach,
                "median_seconds": float(np.median([r["seconds"] for r in rs])),
            }
    for n in B_SIZES:
        rs_n = [r for r in rows_b if r["n"] == n]
        entry = {"floor_bits": float(np.median(np.log2(np.array([r["floor"] for r in rs_n
                                                                 if r["method"] == "LLL"], float) + 1))),
                 "kk_bits": float(np.median(np.log2(np.array([r["karmarkar_karp"] for r in rs_n
                                                              if r["method"] == "LLL"], float) + 1)))}
        for m in sorted({r["method"] for r in rs_n},
                        key=lambda s: (s != "LLL", int(s[4:]) if s != "LLL" else 0)):
            rs = [r for r in rs_n if r["method"] == m]
            gaps = np.array([r["gap"] if r["gap"] != "" else r["total"] for r in rs], float)
            entry[m] = {
                "median_bits": float(np.median(np.log2(gaps + 1))),
                "nothing_read": int(sum(r["gap"] == "" for r in rs)),
                "beats_kk": int(sum(r["gap"] != "" and r["gap"] < r["karmarkar_karp"] for r in rs)),
                "reaches_floor": int(sum(r["gap"] != "" and r["gap"] == r["floor"] for r in rs)),
                "median_seconds": float(np.median([r["seconds"] for r in rs])),
                "shortest_open_mean": float(np.mean([r["short_open"] for r in rs])),
                "shortest_closed_mean": float(np.mean([r["short_closed"] for r in rs])),
                "shortest_over_mean": float(np.mean([r["short_over"] for r in rs])),
            }
        summary["partition"][n] = entry
    with open(HERE / "summary_fold.json", "w") as f:
        json.dump({"A": {"sizes": A_SIZES, "densities": A_DENSITIES, "trials": A_TRIALS,
                         "seed": A_SEED, "W": "n"},
                   "B": {"sizes": B_SIZES, "instances": B_INSTANCES,
                         "instance_seed": B_INSTANCE_SEED, "W": W_PARTITION},
                   "summary": summary}, f, indent=2)
    print("done")


if __name__ == "__main__":
    import sys
    main(sys.argv[1] if len(sys.argv) > 1 else "AB")
