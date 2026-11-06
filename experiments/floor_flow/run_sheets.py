"""
Part 6: sheets of pins (2, 4 and 8 sheets).

Planted subset-sum instances at density 1: n pieces of n bits, a hidden answer
with n/4 ones in each half. The same 10 instances per size are given to every
method that runs at that size.

  2 sheets: meet in the middle                         n = 32, 40, 48, 52
  4 sheets: one layer of tape (representations)        n = 32, 40, 48, 56, 64
  8 sheets: two layers of tape (Howgrave-Graham-Joux)  n = 32, 48, 64

Tape slack 0 (each layer keeps about one copy of the answer), chosen on
separate tuning instances (tune_sheets.py, seed 99). A try that loses every
copy is repeated with fresh layers, up to 40 times.

Usage:  python run_sheets.py      (writes results_sheets.csv, summary_sheets.json)
"""

import csv
import json
import math
import time
from pathlib import Path

import numpy as np

from sheets import eight_sheets, four_sheets, planted_instance, two_sheets

HERE = Path(__file__).parent
SEED = 20261103
TRIALS = 10
PLAN = {
    "2 sheets": (two_sheets, [32, 40, 48, 52]),
    "4 sheets": (four_sheets, [32, 40, 48, 56, 64]),
    "8 sheets": (eight_sheets, [32, 48, 64]),
}
THEORY = {"2 sheets": 0.5, "4 sheets": 0.5 * 0.8113, "8 sheets": 0.337}


def main():
    sizes = sorted({n for _, ns in PLAN.values() for n in ns})
    inst_rng = np.random.default_rng(SEED)
    instances = {n: [planted_instance(inst_rng, n) for _ in range(TRIALS)] for n in sizes}
    rng = np.random.default_rng(SEED + 1)
    rows, t0 = [], time.time()
    for n in sizes:
        for name, (f, ns) in PLAN.items():
            if n not in ns:
                continue
            for k, (a, T, a64, T64) in enumerate(instances[n]):
                t = time.perf_counter()
                x, w, tries = f(a, T, a64, T64, rng)
                dt = time.perf_counter() - t
                if x is not None:
                    assert sum(a[i] for i in range(n) if (x >> i) & 1) == T
                rows.append({"n": n, "method": name, "instance": k,
                             "found": int(x is not None), "tries": tries,
                             "largest_sheet": w.largest, "pins": w.pins, "pairs": w.pairs,
                             "work": w.pins + w.pairs, "seconds": round(dt, 4)})
            print(f"n={n} {name} done ({time.time() - t0:.0f}s)", flush=True)

    with open(HERE / "results_sheets.csv", "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        wr.writeheader()
        wr.writerows(rows)

    summary = {}
    for name, (_, ns) in PLAN.items():
        per_n = {}
        for n in ns:
            rs = [r for r in rows if r["n"] == n and r["method"] == name]
            per_n[n] = {
                "found": int(sum(r["found"] for r in rs)),
                "median_tries": float(np.median([r["tries"] for r in rs])),
                "log2_largest_sheet": float(np.median(np.log2([r["largest_sheet"] for r in rs]))),
                "log2_work": float(np.median(np.log2([r["work"] for r in rs]))),
                "median_seconds": float(np.median([r["seconds"] for r in rs])),
            }
        xs = np.array(ns, float)
        fit = {}
        for key in ("log2_largest_sheet", "log2_work"):
            ys = np.array([per_n[n][key] for n in ns])
            fit[key + "_per_n"] = float(np.polyfit(xs, ys, 1)[0])
        summary[name] = {"per_n": per_n, "fitted_exponent": fit, "theory_exponent": THEORY[name]}
    with open(HERE / "summary_sheets.json", "w") as fh:
        json.dump({"seed": SEED, "trials": TRIALS, "summary": summary}, fh, indent=2)
    print(json.dumps({k: v["fitted_exponent"] for k, v in summary.items()}, indent=1))


if __name__ == "__main__":
    main()
