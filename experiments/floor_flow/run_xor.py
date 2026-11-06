"""
Part 10: random 3-XORSAT next to random 3-SAT (part 9).

  structure: n = 12, 16, 20, 24; alpha = 0.3 .. 1.5 in steps of 0.1;
             100 instances each; every assignment checked (sat3.structure on
             the clause encoding), plus Gaussian elimination
  search:    the same clause search as part 9 (DPLL, 100,000-node limit)
             against Gaussian elimination
             - growth: alpha = 0.95, n = 50, 100, 150, 200; 30 instances each
             - sweep:  n = 150, alpha = 0.5 .. 1.5 in steps of 0.1; 30 each
  scale:     Gaussian elimination alone, alpha = 0.95, n = 10^3, 10^4, 10^5

Instance (n, alpha, k) is drawn from default_rng([20261103, 10, n, 100 alpha, k]).

Usage:  python run_xor.py      (writes results_xor_structure.csv,
                                 results_xor_search.csv, results_xor_scale.csv)
"""

import csv
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

from sat3 import dpll, structure
from xorsat import gauss, random_3xor, to_cnf

HERE = Path(__file__).parent
SEED = 20261103
LIMIT = 100_000


def grid(lo, hi, step):
    return [round(a, 2) for a in np.arange(lo, hi + 1e-9, step)]


def jobs():
    js = []
    for n in (12, 16, 20, 24):
        js += [("structure", n, a, k) for a in grid(0.3, 1.5, 0.1) for k in range(100)]
    js += [("search", n, 0.95, k) for n in (50, 100, 150, 200) for k in range(30)]
    js += [("search", 150, a, k) for a in grid(0.5, 1.5, 0.1) for k in range(30)]
    js = list(dict.fromkeys(js))            # n = 150, alpha 0.95 is not in the sweep grid
    js += [("scale", n, 0.95, k) for n in (1000, 10000, 100000) for k in range(3)]
    return js


def run(job):
    kind, n, alpha, k = job
    rng = np.random.default_rng([SEED, 10, n, int(round(alpha * 100)), k])
    m = int(round(alpha * n))
    var, rhs = random_3xor(rng, n, m)
    t = time.perf_counter()
    sat, ops = gauss(var, rhs, n)
    row = {"kind": kind, "n": n, "alpha": alpha, "instance": k, "m": m, "sat": int(sat),
           "gauss_ops": ops, "gauss_seconds": round(time.perf_counter() - t, 5),
           "dpll_nodes": "", "dpll_finished": "", "dpll_seconds": ""}
    if kind in ("structure", "search"):
        cv, cn = to_cnf(var, rhs)
        t = time.perf_counter()
        try:
            s, nodes = dpll(cv, cn, n, limit=LIMIT)
            assert s == sat
            row.update(dpll_nodes=nodes, dpll_finished=1)
        except RuntimeError:
            row.update(dpll_nodes=LIMIT, dpll_finished=0)
        row["dpll_seconds"] = round(time.perf_counter() - t, 4)
        if kind == "structure":
            st = structure(cv, cn, n, rng)
            assert (st["energy"] == 0) == sat
            row.update(st)
    return row


def main():
    order = {"scale": 0, "search": 1, "structure": 2}
    js = sorted(jobs(), key=lambda j: (order[j[0]], -j[1], j[2], j[3]))
    rows, t0 = {"structure": [], "search": [], "scale": []}, time.time()
    with Pool(2) as pool:
        for i, row in enumerate(pool.imap_unordered(run, js, chunksize=1)):
            rows[row["kind"]].append(row)
            if (i + 1) % 500 == 0:
                print(f"{i + 1}/{len(js)} ({time.time() - t0:.0f}s)", flush=True)
    for kind, rs in rows.items():
        rs.sort(key=lambda r: (r["n"], r["alpha"], r["instance"]))
        keys = list(dict.fromkeys(k for r in rs for k in r))
        with open(HERE / f"results_xor_{kind}.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=keys)
            w.writeheader()
            w.writerows(rs)
    print(f"done {len(js)} instances in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
