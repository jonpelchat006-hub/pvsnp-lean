"""
Part 7b: sweep the tape's reserve c (average surviving copies of the answer).

For each n and each reserve c, the layer modulus is M = round(reps / c) and the
actual reserve is reps / M. Every instance is tried a fixed number of times at
every c (c in shuffled order per instance), each try with a fresh random R.
Per try we record success, seconds, probes, pairs and pins.

  n = 32, 40: 60 instances x 40 tries per c
  n = 48:     40 instances x 25 tries per c
  n = 56:     16 instances x 10 tries per c

Planted instances from sheets.planted_instance (seed 20261104); tries use
seed 20261105.

Usage:  python run_reserve.py [n ...]   (writes results_reserve_<n>.csv)
"""

import csv
import sys
import time
from pathlib import Path

import numpy as np

from reserve import Layer, TryCost, one_try, reps_of
from sheets import planted_instance

HERE = Path(__file__).parent
PI3 = np.pi - 3
GRID = [0.25, 0.35, 0.5, 0.7, 0.85, 1.0, 2 ** PI3, 1 + PI3, 1.2, 1.3, 1.5, 1.75,
        2.0, 2.5, 3.0, 4.0, 6.0]
PLAN = {32: (60, 40), 40: (60, 40), 48: (40, 25), 56: (16, 10)}


def run(n):
    instances, tries = PLAN[n]
    inst_rng = np.random.default_rng([20261104, n])
    rng = np.random.default_rng([20261105, n])
    reps = reps_of(n)
    rows, t0 = [], time.time()
    for k in range(instances):
        a, T, a64, _ = planted_instance(inst_rng, n)
        assert max(a) < 2 ** 56 and T < 2 ** 61
        for gi in rng.permutation(len(GRID)):
            c_target = GRID[gi]
            M = max(1, round(reps / c_target))
            layer = Layer(a64, n, M)
            for t in range(tries):
                cost = TryCost()
                s = time.perf_counter()
                x = one_try(layer, a, T, rng, cost)
                dt = time.perf_counter() - s
                if x is not None:
                    assert sum(a[i] for i in range(n) if (x >> i) & 1) == T
                rows.append({"n": n, "c_target": round(c_target, 4), "M": M,
                             "c": reps / M, "instance": k, "try": t,
                             "found": int(x is not None), "seconds": dt,
                             "probes": cost.probes, "pairs": cost.pairs, "pins": cost.pins})
        print(f"n={n} instance {k + 1}/{instances} ({time.time() - t0:.0f}s)", flush=True)
    with open(HERE / f"results_reserve_{n}.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


if __name__ == "__main__":
    for n in (map(int, sys.argv[1:]) if len(sys.argv) > 1 else PLAN):
        run(n)
