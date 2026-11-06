"""
Part 8 analysis: summary_backbone.json from results_backbone.csv
(and results_threshold.csv for the search work, n <= 32).

Per n and b: chance of a perfect split, the mean frozen fraction over the
optimal splits (when more than K = 16 splits are optimal it is bounded by the
frozen fraction over the 16 lowest corners, which is about 0), the mean frozen
fraction over the 8 and 16 lowest corners, and the median flip distances from
the best split to the second best and to the nearest of the 16 lowest.

Baseline: the same quantities for 16 uniformly random splits (simulated).

Per n: where the optimal-split frozen fraction crosses 1/2, its 10% -> 90%
width, and where perfect splits cross 1/2 (part 7a).

Per n <= 32, near the wall (0.9 <= kappa <= 1.1): Spearman correlation,
within each b and then averaged, between search work and the frozen fraction
of the 8 lowest corners, and between work and the distance to the nearest
low corner, over instances with no perfect split.
"""

import csv
import json
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

from backbone import flips, frozen

HERE = Path(__file__).parent


def crossing(ks, ys, level):
    for i in range(1, len(ks)):
        if (ys[i - 1] - level) * (ys[i] - level) <= 0 and ys[i] != ys[i - 1]:
            return ks[i - 1] + (level - ys[i - 1]) / (ys[i] - ys[i - 1]) * (ks[i] - ks[i - 1])
    return float("nan")


def null(n, trials=4000, seed=7):
    rng = np.random.default_rng([seed, n])
    f8, f16, d2, dn = [], [], [], []
    for _ in range(trials):
        s = np.where(rng.random((16, n)) < 0.5, 1, -1).astype(np.int8)
        s[:, 0] = 1
        f8.append(frozen(s[:8]))
        f16.append(frozen(s))
        d = [flips(s[0], s[j]) for j in range(1, 16)]
        d2.append(d[0])
        dn.append(min(d))
    return {"frozen_8": float(np.mean(f8)), "frozen_16": float(np.mean(f16)),
            "dist_2nd_median": float(np.median(d2)), "dist_near_median": float(np.median(dn))}


def main():
    rows = list(csv.DictReader(open(HERE / "results_backbone.csv")))
    work = {}
    for r in csv.DictReader(open(HERE / "results_threshold.csv")):
        if r["nodes"] != "":
            work[(r["n"], r["b"], r["instance"])] = (np.log2(int(r["nodes"])), int(r["perfect"]))
    by_n = defaultdict(list)
    for r in rows:
        by_n[int(r["n"])].append(r)
    out, mismatch = {}, 0
    for n, rs in sorted(by_n.items()):
        base = null(n)
        per_b = {}
        for b in sorted({int(r["b"]) for r in rs}):
            sub = [r for r in rs if int(r["b"]) == b]
            fo = [float(r["frozen_opt"]) if r["frozen_opt"] != "" else float(r["frozen_16"]) for r in sub]
            per_b[b] = {
                "kappa": b / n, "instances": len(sub),
                "perfect": float(np.mean([int(r["perfect"]) for r in sub])),
                "frozen_opt": float(np.mean(fo)),
                "single_best": float(np.mean([int(r["n_opt_in_top"]) == 1 for r in sub])),
                "frozen_8": float(np.mean([float(r["frozen_8"]) for r in sub])),
                "frozen_16": float(np.mean([float(r["frozen_16"]) for r in sub])),
                "dist_2nd_median": float(np.median([float(r["dist_2nd"]) for r in sub])),
                "dist_near_median": float(np.median([float(r["dist_near"]) for r in sub])),
            }
            for r in sub:                       # same instance as part 7a: same answer
                key = (r["n"], r["b"], r["instance"])
                if key in work and work[key][1] != int(r["perfect"]):
                    mismatch += 1
        bs = sorted(per_b)
        ks = [per_b[b]["kappa"] for b in bs]
        fo = [per_b[b]["frozen_opt"] for b in bs]
        pf = [per_b[b]["perfect"] for b in bs]
        res = {"null": base, "per_b": per_b,
               "frozen_opt_50": crossing(ks, fo, 0.5),
               "frozen_opt_width_10_90": crossing(ks, fo, 0.9) - crossing(ks, fo, 0.1),
               "perfect_50": crossing(ks, pf, 0.5),
               "frozen_8_max": max(per_b[b]["frozen_8"] for b in bs),
               "dist_near_min_median": min(per_b[b]["dist_near_median"] for b in bs)}
        if n <= 32:
            rho_f, rho_d, cnt = [], [], 0
            for b in bs:
                if not 0.9 <= b / n <= 1.1:
                    continue
                sub = [r for r in rs if int(r["b"]) == b and int(r["perfect"]) == 0]
                if len(sub) < 20:
                    continue
                w = [work[(r["n"], r["b"], r["instance"])][0] for r in sub]
                rho_f.append((spearmanr(w, [float(r["frozen_8"]) for r in sub])[0], len(sub)))
                rho_d.append((spearmanr(w, [float(r["dist_near"]) for r in sub])[0], len(sub)))
                cnt += len(sub)
            avg = lambda xs: float(np.average([x for x, _ in xs], weights=[m for _, m in xs]))
            res.update(rho_work_frozen8=avg(rho_f), rho_work_dist_near=avg(rho_d),
                       rho_instances=cnt)
        out[n] = res
        print(f"n={n}: frozen_opt crosses 1/2 at kappa {res['frozen_opt_50']:.3f} "
              f"(perfect splits cross 1/2 at {res['perfect_50']:.3f}), width {res['frozen_opt_width_10_90']:.3f}; "
              f"frozen_8 max {res['frozen_8_max']:.4f} (random {base['frozen_8']:.4f}); "
              f"dist_near median >= {res['dist_near_min_median']:.3f} (random {base['dist_near_median']:.3f})"
              + (f"; work vs frozen_8 rho {res['rho_work_frozen8']:+.3f}, vs dist_near rho "
                 f"{res['rho_work_dist_near']:+.3f} ({res['rho_instances']} sliver-only instances)"
                 if "rho_work_frozen8" in res else ""))
    print("perfect-split mismatches with part 7a:", mismatch)
    with open(HERE / "summary_backbone.json", "w") as fh:
        json.dump({"K": 16, "summary": out, "perfect_mismatches_with_7a": mismatch}, fh, indent=1)


if __name__ == "__main__":
    main()
