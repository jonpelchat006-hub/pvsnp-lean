"""
Part 7b analysis: summary_reserve.json from results_reserve_<n>.csv.

Per n and reserve c: chance a try keeps a copy (p), mean cost of a try (seconds
and work = probes + pairs + pins) and the cost per success (mean cost / p).

Model: p = 1 - exp(-beta c) (beta = 1 is the Poisson guess) and a try costs
A + B c. The cost per success is then smallest at c* with
    e^u - 1 - u = A beta / B,   c* = u / beta.
c* is reported for seconds and for work, with a 95% bootstrap interval over
instances.
"""

import csv
import json
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, minimize_scalar

HERE = Path(__file__).parent
SPECIAL = {"2^(pi-3)": round(2 ** (np.pi - 3), 4), "1+(pi-3)": round(1 + (np.pi - 3), 4)}


def fit_beta(c, succ, tries):
    def nll(beta):
        p = np.clip(1 - np.exp(-beta * c), 1e-12, 1 - 1e-12)
        return -np.sum(succ * np.log(p) + (tries - succ) * np.log(1 - p))
    return minimize_scalar(nll, bounds=(0.05, 5), method="bounded").x


def best_c(A, B, beta):
    r = A * beta / B
    u = brentq(lambda u: np.exp(u) - 1 - u - r, 1e-9, 50)
    return u / beta


def tables(rows):
    """Per c_target: c, tries, successes, mean seconds, mean work."""
    g = defaultdict(lambda: [0, 0, 0.0, 0.0, 0.0])
    for r in rows:
        e = g[r["c_target"]]
        e[0] += 1
        e[1] += r["found"]
        e[2] += r["seconds"]
        e[3] += r["work"]
        e[4] = r["c"]
    keys = sorted(g)
    c = np.array([g[k][4] for k in keys])
    tries = np.array([g[k][0] for k in keys], float)
    succ = np.array([g[k][1] for k in keys], float)
    sec = np.array([g[k][2] for k in keys]) / tries
    work = np.array([g[k][3] for k in keys]) / tries
    return keys, c, tries, succ, sec, work


def model(c, tries, succ, cost):
    B, A = np.polyfit(c, cost, 1)
    beta = fit_beta(c, succ, tries)
    return A, B, beta, best_c(A, B, beta)


def main():
    out = {}
    rng = np.random.default_rng(1)
    for path in sorted(HERE.glob("results_reserve_*.csv")):
        rows = []
        for r in csv.DictReader(open(path)):
            rows.append({"c_target": float(r["c_target"]), "c": float(r["c"]),
                         "instance": int(r["instance"]), "found": int(r["found"]),
                         "seconds": float(r["seconds"]),
                         "work": int(r["probes"]) + int(r["pairs"]) + int(r["pins"])})
        n = int(path.stem.split("_")[-1])
        keys, c, tries, succ, sec, work = tables(rows)
        p = succ / tries
        res = {"per_c": {}, "fits": {}}
        for i, k in enumerate(keys):
            res["per_c"][k] = {"c": c[i], "tries": int(tries[i]), "p": p[i],
                               "poisson_p": 1 - np.exp(-c[i]),
                               "seconds_per_try": sec[i], "work_per_try": work[i],
                               "seconds_per_success": sec[i] / p[i] if p[i] else None,
                               "work_per_success": work[i] / p[i] if p[i] else None}
        by_inst = defaultdict(list)
        for r in rows:
            by_inst[r["instance"]].append(r)
        insts = sorted(by_inst)
        for name, cost in (("seconds", sec), ("work", work)):
            A, B, beta, cstar = model(c, tries, succ, cost)
            boots = []
            for _ in range(400):
                pick = rng.choice(insts, size=len(insts), replace=True)
                sample = [r for j in pick for r in by_inst[j]]
                _, cb, tb, sb, secb, workb = tables(sample)
                try:
                    boots.append(model(cb, tb, sb, secb if name == "seconds" else workb)[3])
                except ValueError:
                    pass
            per_success = cost / np.where(p > 0, p, np.nan)
            grid_best = keys[int(np.nanargmin(per_success))]
            opt = np.nanmin(per_success)
            res["fits"][name] = {
                "A": A, "B": B, "A_over_B": A / B, "beta": beta, "c_star": cstar,
                "c_star_95": [float(np.percentile(boots, 2.5)), float(np.percentile(boots, 97.5))],
                "grid_best_c": grid_best,
                "cost_vs_grid_best": {lab: float(per_success[keys.index(v)] / opt)
                                      for lab, v in SPECIAL.items()},
            }
        out[n] = res
        f = res["fits"]
        print(f"n={n}: beta={f['seconds']['beta']:.3f}  "
              f"seconds: A/B={f['seconds']['A_over_B']:.2f} c*={f['seconds']['c_star']:.2f} "
              f"[{f['seconds']['c_star_95'][0]:.2f}, {f['seconds']['c_star_95'][1]:.2f}] "
              f"grid best {f['seconds']['grid_best_c']}   "
              f"work: A/B={f['work']['A_over_B']:.2f} c*={f['work']['c_star']:.2f} "
              f"[{f['work']['c_star_95'][0]:.2f}, {f['work']['c_star_95'][1]:.2f}] "
              f"grid best {f['work']['grid_best_c']}")
        for k in keys:
            e = res["per_c"][k]
            print(f"   c={e['c']:.4f} p={e['p']:.3f} (poisson {e['poisson_p']:.3f}) "
                  f"s/try={e['seconds_per_try']:.5f} s/success={e['seconds_per_success'] or float('nan'):.5f} "
                  f"work/success={e['work_per_success'] or float('nan'):.0f}")
    with open(HERE / "summary_reserve.json", "w") as fh:
        json.dump({"note": "cost per success = mean cost per try / chance a try keeps a copy",
                   "summary": out}, fh, indent=1, default=float)


if __name__ == "__main__":
    main()
