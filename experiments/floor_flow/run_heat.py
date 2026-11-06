"""
Part 2: nesting and heat.

Fresh instances at the hardest point (n pieces, n bits each), drawn from their
own generator so every method sees exactly the same instances. Schedules were
chosen beforehand on separate tuning instances (tune_heat.py, seed 777).

Usage:  python run_heat.py      (writes results_heat.csv, summary_heat.json)
"""

import csv
import json
import time
from pathlib import Path

import numpy as np

from floor_flow import (best_core_flow, exact_floor, gap_of, karmarkar_karp,
                        nested_flow)
from heat import anneal

HERE = Path(__file__).parent
SIZES = [16, 20, 24, 28, 32, 36, 40]
INSTANCES = 30
INSTANCE_SEED = 20261030
METHOD_SEED = 4242
CHECKPOINTS = [10**3, 10**4, 10**5, 10**6, 10**7]
STEPS = CHECKPOINTS[-1]
HEAT = {                       # name: (start, T0, T1); T0 = 0 means never cools
    "hot_walk": ("random", 0.0, 0.0),
    "anneal": ("random", 16.0, 0.5),
    "anneal_from_kk": ("kk", 2.0, 1.0),
}
NEST = [0.1, 0.25, 0.5]


def main():
    inst_rng = np.random.default_rng(INSTANCE_SEED)
    rng = np.random.default_rng(METHOD_SEED)
    rows = []
    t0 = time.time()
    seed = 0
    for n in SIZES:
        for k in range(INSTANCES):
            a = inst_rng.integers(1, 2 ** n, size=n, dtype=np.int64)
            total = int(a.sum())
            floor = exact_floor(a)
            s_kk = karmarkar_karp(a)
            row = {"n": n, "instance": k, "total": total, "floor": floor,
                   "karmarkar_karp": gap_of(a, s_kk),
                   "flow_best_of_n": best_core_flow(a, rng, "sized", runs=n)[0]}
            for f in NEST:
                row[f"nested_{f}"] = gap_of(a, nested_flow(a, rng, f))
            for name, (start, T0, T1) in HEAT.items():
                s0 = s_kk if start == "kk" else rng.choice(np.array([-1, 1]), n)
                seed += 1
                best, best_s, rec = anneal(a, s0, STEPS, T0, T1, seed, CHECKPOINTS)
                assert gap_of(a, best_s) == best
                for c, g in zip(CHECKPOINTS, rec):
                    row[f"{name}@{c}"] = int(g)
            for key, val in row.items():
                if key in ("n", "instance", "total", "floor"):
                    continue
                assert val >= floor, f"{key} beat the exact floor: impossible"
                assert val % 2 == total % 2, f"{key} broke the parity rule"
            rows.append(row)
        print(f"n={n} done ({time.time() - t0:.0f}s)", flush=True)

    with open(HERE / "results_heat.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    def mbits(vals):
        return float(np.median(np.log2(np.asarray(vals, dtype=float) + 1)))

    summary = {}
    for n in SIZES:
        rs = [r for r in rows if r["n"] == n]
        e = {key: mbits([r[key] for r in rs]) for key in rs[0]
             if key not in ("n", "instance", "total")}
        e["total"] = mbits([r["total"] for r in rs])
        # cost of heat: bits gained per doubling of work, 10^5 -> 10^7 flips
        for name in HEAT:
            hi, lo = e[f"{name}@{10**5}"], e[f"{name}@{10**7}"]
            e[f"{name}_bits_per_doubling"] = (hi - lo) / np.log2(100)
        summary[n] = e
    with open(HERE / "summary_heat.json", "w") as f:
        json.dump({"instance_seed": INSTANCE_SEED, "method_seed": METHOD_SEED,
                   "instances_per_size": INSTANCES, "checkpoints": CHECKPOINTS,
                   "heat": HEAT, "nest_fractions": NEST, "summary": summary}, f, indent=2)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
