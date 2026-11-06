"""
Run the floor experiment at the hardest point: numbers with as many bits as
there are pieces (Mertens' kappa = 1, just past the transition).

Usage:  python run.py            (writes results.csv and summary.json here)
"""

import csv
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

from floor_flow import (best_core_flow, brute_floor, core_flow, exact_floor, gap_of,
                        greedy, karmarkar_karp)

HERE = Path(__file__).parent
SIZES = [16, 20, 24, 28, 32, 36, 40]
INSTANCES = 30
SEED = 20261029


def instance(rng, n, bits):
    return rng.integers(1, 2 ** bits, size=n, dtype=np.int64)


def main():
    rng = np.random.default_rng(SEED)
    rows = []
    t0 = time.time()

    # independent check of the exact floor on small sizes
    for n in (8, 12, 16, 20):
        for _ in range(10):
            a = instance(rng, n, n)
            assert exact_floor(a) == brute_floor(a), "meet-in-the-middle disagrees with brute force"
    print("exact floor matches brute force on 40 small instances", flush=True)

    for n in SIZES:
        for k in range(INSTANCES):
            a = instance(rng, n, n)
            total = int(a.sum())
            floor = exact_floor(a)

            s_g = greedy(a)
            s_kk = karmarkar_karp(a)
            s_fe, info_fe = core_flow(a, rng, "even")
            s_fs, info_fs = core_flow(a, rng, "sized")
            g_fs_best, _, info_best = best_core_flow(a, rng, "sized", runs=n)

            g = {
                "greedy": gap_of(a, s_g),
                "karmarkar_karp": gap_of(a, s_kk),
                "flow_even": gap_of(a, s_fe),
                "flow_sized": gap_of(a, s_fs),
                "flow_sized_best_of_n": g_fs_best,
            }
            for name, val in g.items():
                assert val >= floor, f"{name} beat the exact floor: impossible"
                assert val % 2 == total % 2, f"{name} broke the parity rule"
            assert floor % 2 == total % 2

            # the stranded branch accounts for the whole forced step
            for info, val in ((info_fe, g["flow_even"]), (info_fs, g["flow_sized"])):
                forced = info["last_piece"] * (1 - abs(math.cos(info["theta_last"])))
                assert abs(forced - val) <= 1e-6 * max(1.0, val) + 1e-3, (forced, val)

            rows.append({
                "n": n, "bits": n, "instance": k, "total": total,
                "smallest_piece": int(a.min()), "largest_piece": int(a.max()),
                "floor": floor, **g,
                "even_last_rank": info_fe["last_piece_rank"],
                "even_angle_to_closure": info_fe["angle_to_closure"],
                "sized_last_rank": info_fs["last_piece_rank"],
                "sized_angle_to_closure": info_fs["angle_to_closure"],
            })
        print(f"n={n} done ({time.time() - t0:.0f}s)", flush=True)

    with open(HERE / "results.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    methods = ["floor", "karmarkar_karp", "greedy", "flow_even", "flow_sized",
               "flow_sized_best_of_n"]
    summary = {}
    for n in SIZES:
        rs = [r for r in rows if r["n"] == n]
        entry = {}
        for m in methods:
            vals = np.array([r[m] for r in rs], dtype=float)
            entry[m] = {
                "median": float(np.median(vals)),
                "median_bits_above_wall": float(np.median(np.log2(vals + 1))),
            }
        entry["perfect_partitions"] = int(sum(r["floor"] == 0 for r in rs))
        entry["median_total"] = float(np.median([r["total"] for r in rs]))
        entry["median_smallest_piece"] = float(np.median([r["smallest_piece"] for r in rs]))
        entry["even_last_is_smallest"] = int(sum(r["even_last_rank"] == n for r in rs))
        entry["sized_last_is_smallest"] = int(sum(r["sized_last_rank"] == n for r in rs))
        entry["sized_median_last_rank"] = float(np.median([r["sized_last_rank"] for r in rs]))
        entry["median_angle_to_closure_deg"] = {
            "even": float(np.degrees(np.median([r["even_angle_to_closure"] for r in rs]))),
            "sized": float(np.degrees(np.median([r["sized_angle_to_closure"] for r in rs]))),
        }
        summary[n] = entry
    with open(HERE / "summary.json", "w") as f:
        json.dump({"seed": SEED, "instances_per_size": INSTANCES, "sizes": SIZES,
                   "summary": summary}, f, indent=2)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    sys.exit(main())
