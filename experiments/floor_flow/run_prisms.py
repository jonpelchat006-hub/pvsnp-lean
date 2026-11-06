"""
Part 12: prisms meeting at the wall.

A. Double Speck32 with two k-bit keys, 3 random trials per k:
   brute force for k = 6, 8, 10, 12; meet in the middle for k = 6 .. 24.
B. Even-Mansour on n-bit blocks with a public 4-round Feistel scramble,
   5 random trials per n: key search for n = 16, 20, 24; Daemen's attack for
   n = 16 .. 32.
Every recovered key is checked against the true one.

Seed 20261104. Usage: python run_prisms.py  (writes results_prisms.csv)
"""

import csv
import time
from pathlib import Path

import numpy as np

from prisms import (EvenMansour, Feistel, brute_force, check_speck, daemen, double_enc,
                    key_search, meet_in_middle)

HERE = Path(__file__).parent
SEED = 20261104


def main():
    assert check_speck()
    rng = np.random.default_rng(SEED)
    rows = []
    for k in range(6, 25, 2):
        for trial in range(3):
            k1, k2 = (int(v) for v in rng.integers(0, 1 << k, size=2))
            P = [int(v) for v in rng.integers(0, 2 ** 32, size=2)]
            pairs = [(p, double_enc(p, k1, k2)) for p in P]
            methods = [("meet in the middle", meet_in_middle)]
            if k <= 12:
                methods.insert(0, ("brute force", brute_force))
            for name, f in methods:
                t = time.perf_counter()
                res = f(k, pairs)
                dt = time.perf_counter() - t
                found, calls = res[0], res[1]
                assert found == [(k1, k2)], (k, name, found, (k1, k2))
                rows.append({"part": "double", "size": k, "method": name, "trial": trial,
                             "work": calls, "extra": res[2] if len(res) > 2 else "",
                             "seconds": round(dt, 4)})
        print(f"double k={k} done", flush=True)
    for n in (16, 20, 24, 28, 32):
        for trial in range(5):
            P = Feistel(n, rng)
            k1, k2 = (int(v) for v in rng.integers(0, 1 << n, size=2))
            E = EvenMansour(P, k1, k2)
            methods = [("Daemen", daemen)]
            if n <= 24:
                methods.insert(0, ("key search", key_search))
            for name, f in methods:
                P.calls, E.queries = 0, 0
                t = time.perf_counter()
                got = f(E, P, n, rng)
                dt = time.perf_counter() - t
                assert got == (k1, k2), (n, name, got, (k1, k2))
                rows.append({"part": "even-mansour", "size": n, "method": name, "trial": trial,
                             "work": P.calls + E.queries, "extra": E.queries,
                             "seconds": round(dt, 4)})
        print(f"even-mansour n={n} done", flush=True)
    with open(HERE / "results_prisms.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    # summary
    for part in ("double", "even-mansour"):
        for size in sorted({r["size"] for r in rows if r["part"] == part}):
            for m in sorted({r["method"] for r in rows if r["part"] == part and r["size"] == size}):
                rs = [r for r in rows if r["part"] == part and r["size"] == size and r["method"] == m]
                print(f"{part:13s} size {size:2d} {m:18s} median work 2^{np.log2(np.median([r['work'] for r in rs])):.1f}"
                      f"  median {np.median([r['seconds'] for r in rs]):.3f}s")


if __name__ == "__main__":
    main()
