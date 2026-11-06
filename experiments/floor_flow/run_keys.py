"""
Part 5: plugging keys.

Plug the pieces in one at a time, largest first. For each piece, try both
keys (upright, flipped), read how the rest of the structure would settle
with that key in place, and keep the key with the better reading. After n
plugs every branch is set.

The reading of a partial state (fixed total F, remaining pieces R):
  exact  - the true best gap of the rest, min |F + sum(+-r)| (meet in the middle)
  kk     - the gap Karmarkar-Karp reaches on [|F|] + R
  flow   - the best gap of 8 core flows on [|F|] + R
(By mirror symmetry, solving [|F|] + R with any orientation gives a gap that
F's orientation can reach.)

With the exact reading this is self-reducibility: n plugs with a perfect
reading always reach the floor. With a cheap reading it is a polynomial-time
heuristic (2n readings).

Instances: the part-2 density-1 instances (seed 20261030), n = 16..40, 30 each.
"""

import csv
import json
import time
from pathlib import Path

import numpy as np

from floor_flow import best_core_flow, exact_floor, gap_of, greedy, karmarkar_karp

HERE = Path(__file__).parent
SIZES = [16, 20, 24, 28, 32, 36, 40]
INSTANCES = 30
INSTANCE_SEED = 20261030
FLOW_RUNS = 8


def _expand(F, R, items_signs, used_F):
    """Turn signs for [|F|] + R (or R alone when F == 0) into signs for R that
    give the same gap together with the fixed total F."""
    t = list(items_signs)
    if not used_F:
        return t, abs(F + sum(si * r for si, r in zip(t, R)))
    t0, rest = t[0], t[1:]
    sF = 1 if F >= 0 else -1
    if t0 != sF:                 # mirror the rest so that F keeps its own sign
        rest = [-x for x in rest]
    return rest, abs(F + sum(si * r for si, r in zip(rest, R)))


def read_exact(F, R, rng):
    if len(R) == 0:
        return abs(F), []
    return exact_floor(np.array([abs(F)] + list(R), dtype=np.int64)), None


def read_kk(F, R, rng):
    if len(R) == 0:
        return abs(F), []
    used_F = F != 0
    items = np.array(([abs(F)] if used_F else []) + list(R), dtype=np.int64)
    if len(items) == 1:
        rest, g = _expand(F, R, [1], used_F)
        return g, rest
    rest, g = _expand(F, R, karmarkar_karp(items), used_F)
    return g, rest


def read_flow(F, R, rng):
    if len(R) == 0:
        return abs(F), []
    used_F = F != 0
    items = ([abs(F)] if used_F else []) + list(R)
    if len(items) == 1:
        rest, g = _expand(F, R, [1], used_F)
        return g, rest
    _, signs, _ = best_core_flow(np.array(items, dtype=np.int64), rng, "sized", runs=FLOW_RUNS)
    rest, g = _expand(F, R, signs, used_F)
    return g, rest


def plug_keys(a, read, rng):
    """Plug keys largest first, choosing each key by the reading. Every reading
    of a cheap kind is also a complete orientation; the best one seen is kept
    (the incumbent), so the result is never worse than the first reading."""
    order = np.argsort(-a, kind="stable")
    F = 0
    signs = np.zeros(len(a), dtype=np.int64)
    best = None
    for step, i in enumerate(order):
        rest_idx = list(order[step + 1:])
        rest = [int(a[j]) for j in rest_idx]
        choices = []
        for s in (1, -1):
            g, rest_signs = read(F + s * int(a[i]), rest, rng)
            choices.append((g, s))
            if rest_signs is not None:
                full = signs.copy()
                full[i] = s
                for j, sj in zip(rest_idx, rest_signs):
                    full[j] = sj
                assert gap_of(a, full) == g
                if best is None or g < best[0]:
                    best = (g, full)
        g, s = min(choices, key=lambda c: (c[0], -c[1]))
        signs[i] = s
        F += s * int(a[i])
    final = gap_of(a, signs)
    if best is not None and best[0] < final:
        return best[1]
    return signs


def main():
    inst_rng = np.random.default_rng(INSTANCE_SEED)
    rng = np.random.default_rng(5150)
    rows, t0 = [], time.time()
    for n in SIZES:
        for k in range(INSTANCES):
            a = inst_rng.integers(1, 2 ** n, size=n, dtype=np.int64)
            floor = exact_floor(a)
            row = {"n": n, "instance": k, "floor": floor,
                   "greedy": gap_of(a, greedy(a)),
                   "karmarkar_karp": gap_of(a, karmarkar_karp(a))}
            for name, read in (("keys_exact", read_exact), ("keys_kk", read_kk),
                               ("keys_flow", read_flow)):
                g = gap_of(a, plug_keys(a, read, rng))
                assert g >= floor
                row[name] = g
            assert row["keys_exact"] == floor, "self-reducibility must reach the floor"
            rows.append(row)
        print(f"n={n} done ({time.time() - t0:.0f}s)", flush=True)

    with open(HERE / "results_keys.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    summary = {}
    for n in SIZES:
        rs = [r for r in rows if r["n"] == n]
        e = {m: float(np.median(np.log2(np.array([r[m] for r in rs], float) + 1)))
             for m in ("floor", "greedy", "karmarkar_karp", "keys_exact", "keys_kk", "keys_flow")}
        e["keys_kk_beats_kk"] = int(sum(r["keys_kk"] < r["karmarkar_karp"] for r in rs))
        e["keys_kk_ties_kk"] = int(sum(r["keys_kk"] == r["karmarkar_karp"] for r in rs))
        e["keys_flow_beats_kk"] = int(sum(r["keys_flow"] < r["karmarkar_karp"] for r in rs))
        e["keys_kk_reaches_floor"] = int(sum(r["keys_kk"] == r["floor"] for r in rs))
        summary[n] = e
    with open(HERE / "summary_keys.json", "w") as f:
        json.dump({"instance_seed": INSTANCE_SEED, "flow_runs": FLOW_RUNS,
                   "summary": summary}, f, indent=2)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
