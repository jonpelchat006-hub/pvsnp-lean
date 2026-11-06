"""
Part 7a: where does the problem get hard?

For n pieces of b bits (load kappa = b / n) record, per instance, the exact
number of perfect splits (meet in the middle) and, for n <= 32, the work of a
complete search (complete Karmarkar-Karp nodes). Every complete-search floor
is checked against meet in the middle.

  n = 16 .. 32: b from 0.5 n to 1.5 n, 200 instances each (100 at n = 32),
                counts and complete search
  n = 36, 40:   b from 0.6 n to 1.25 n, counts only (100 instances)
  n = 44:       b from 0.8 n to 1.1 n, counts only (60 instances)

Instance (n, b, k) is drawn from default_rng([20261103, n, b, k]).

Usage:  python run_threshold.py      (writes results_threshold.csv)
"""

import csv
import math
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

from threshold import ckk, mitm_count

HERE = Path(__file__).parent
SEED = 20261103
NODE_LIMIT = 4_000_000_000


def plan():
    jobs = []
    for n in (16, 20, 24, 28, 32):
        reps = 100 if n == 32 else 200
        for b in range(math.ceil(0.5 * n), math.floor(1.5 * n) + 1):
            jobs += [(n, b, k, True) for k in range(reps)]
    for n, lo, hi, reps in ((36, 0.6, 1.25, 100), (40, 0.6, 1.25, 100), (44, 0.8, 1.1, 60)):
        bmax = min(math.floor(hi * n), 62 - math.ceil(math.log2(n)))
        for b in range(math.ceil(lo * n), bmax + 1):
            jobs += [(n, b, k, False) for k in range(reps)]
    return jobs


def run(job):
    n, b, k, search = job
    rng = np.random.default_rng([SEED, n, b, k])
    a = rng.integers(1, 2 ** b, size=n, dtype=np.int64)
    parity = int(a.sum()) & 1
    floor, count = mitm_count(a)
    row = {"n": n, "b": b, "kappa": b / n, "instance": k, "parity": parity,
           "floor": floor, "count": count, "perfect": int(floor == parity),
           "nodes": "", "finished": "", "seconds": ""}
    if search:
        t = time.perf_counter()
        g, nodes, fin = ckk(np.sort(a)[::-1].copy(), NODE_LIMIT)
        row.update(nodes=int(nodes), finished=int(fin), seconds=round(time.perf_counter() - t, 4))
        if fin:
            assert g == floor, (n, b, k, g, floor)
    return row


def main():
    jobs = plan()
    # spread the expensive jobs: biggest n first
    jobs.sort(key=lambda j: (-j[0], j[1], j[2]))
    rows, t0 = [], time.time()
    with Pool(2) as pool:
        for i, row in enumerate(pool.imap_unordered(run, jobs, chunksize=8)):
            rows.append(row)
            if (i + 1) % 2000 == 0:
                print(f"{i + 1}/{len(jobs)} ({time.time() - t0:.0f}s)", flush=True)
    rows.sort(key=lambda r: (r["n"], r["b"], r["instance"]))
    with open(HERE / "results_threshold.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print(f"done {len(rows)} instances in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
