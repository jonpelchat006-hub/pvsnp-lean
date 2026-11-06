"""
Part 8: backbone and isolation of the lowest corners around the wall.

Same instances as part 7a (default_rng([20261103, n, b, k])), so the search
work recorded there (n <= 32) can be joined per instance.

  n = 20, 24, 28, 32, 36, 40;  b from 0.75 n to 1.25 n;  100 instances per b

Usage:  python run_backbone.py      (writes results_backbone.csv)
"""

import csv
import math
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

from backbone import measure

HERE = Path(__file__).parent
SEED = 20261103
K = 16


def plan():
    jobs = []
    for n in (20, 24, 28, 32, 36, 40):
        for b in range(math.ceil(0.75 * n), math.floor(1.25 * n) + 1):
            jobs += [(n, b, k) for k in range(100)]
    return jobs


def run(job):
    n, b, k = job
    a = np.random.default_rng([SEED, n, b, k]).integers(1, 2 ** b, size=n, dtype=np.int64)
    parity = int(a.sum()) & 1
    m = measure(a, K)
    return {"n": n, "b": b, "kappa": b / n, "instance": k, "parity": parity,
            "perfect": int(m["floor"] == parity), **m}


def main():
    jobs = sorted(plan(), key=lambda j: (-j[0], j[1], j[2]))
    rows, t0 = [], time.time()
    with Pool(2) as pool:
        for i, row in enumerate(pool.imap_unordered(run, jobs, chunksize=4)):
            rows.append(row)
            if (i + 1) % 1000 == 0:
                print(f"{i + 1}/{len(jobs)} ({time.time() - t0:.0f}s)", flush=True)
    rows.sort(key=lambda r: (r["n"], r["b"], r["instance"]))
    with open(HERE / "results_backbone.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print(f"done {len(rows)} instances in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
