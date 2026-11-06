"""
Part 9: random 3-SAT across its threshold (alpha_c ~ 4.27).

  structure: n = 12, 16, 20, 24; alpha = 2.0 .. 6.0 in steps of 0.25;
             100 instances each; every assignment checked (sat3.structure),
             plus DPLL work on the same instance
  search:    n = 25, 50, 75, 100; alpha = 2.0 .. 7.0 in steps of 0.25;
             100 instances each; DPLL work and satisfiability

Instance (n, alpha, k) is drawn from default_rng([20261103, 3, n, 100 alpha, k]).

Usage:  python run_sat.py      (writes results_sat_structure.csv, results_sat_search.csv)
"""

import csv
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

from sat3 import dpll, random_3sat, structure

HERE = Path(__file__).parent
SEED = 20261103


def alphas(lo, hi):
    return [round(a, 2) for a in np.arange(lo, hi + 1e-9, 0.25)]


def jobs():
    js = []
    for n in (12, 16, 20, 24):
        js += [("structure", n, a, k) for a in alphas(2.0, 6.0) for k in range(100)]
    for n in (25, 50, 75, 100):
        js += [("search", n, a, k) for a in alphas(2.0, 7.0) for k in range(100)]
    return js


def run(job):
    kind, n, alpha, k = job
    rng = np.random.default_rng([SEED, 3, n, int(round(alpha * 100)), k])
    m = int(round(alpha * n))
    var, neg = random_3sat(rng, n, m)
    t = time.perf_counter()
    sat, nodes = dpll(var, neg, n)
    row = {"kind": kind, "n": n, "alpha": alpha, "instance": k, "m": m,
           "sat": int(sat), "nodes": nodes, "seconds": round(time.perf_counter() - t, 4)}
    if kind == "structure":
        s = structure(var, neg, n, rng)
        assert (s["energy"] == 0) == sat
        row.update(s)
    return row


def main():
    js = sorted(jobs(), key=lambda j: (j[0] != "search", -j[1], j[2], j[3]))
    rows, t0 = {"structure": [], "search": []}, time.time()
    with Pool(2) as pool:
        for i, row in enumerate(pool.imap_unordered(run, js, chunksize=4)):
            rows[row["kind"]].append(row)
            if (i + 1) % 2000 == 0:
                print(f"{i + 1}/{len(js)} ({time.time() - t0:.0f}s)", flush=True)
    for kind, rs in rows.items():
        rs.sort(key=lambda r: (r["n"], r["alpha"], r["instance"]))
        with open(HERE / f"results_sat_{kind}.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rs[0].keys()))
            w.writeheader()
            w.writerows(rs)
    print(f"done {len(js)} instances in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
