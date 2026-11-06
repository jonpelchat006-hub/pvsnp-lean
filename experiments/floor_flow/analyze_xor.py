"""
Part 10 analysis: summary_xor.json from results_xor_*.csv, side by side with
part 9 (summary_sat.json) where the measures match.
"""

import csv
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).parent


def crossing(xs, ys, level):
    for i in range(1, len(xs)):
        if (ys[i - 1] - level) * (ys[i] - level) <= 0 and ys[i] != ys[i - 1]:
            return xs[i - 1] + (level - ys[i - 1]) / (ys[i] - ys[i - 1]) * (xs[i] - xs[i - 1])
    return float("nan")


def load(kind):
    return list(csv.DictReader(open(HERE / f"results_xor_{kind}.csv")))


def main():
    out = {"structure": {}, "search_growth": {}, "search_sweep": {}, "scale": {}}
    by = defaultdict(list)
    for r in load("structure"):
        by[(int(r["n"]), float(r["alpha"]))].append(r)
    for n in sorted({k[0] for k in by}):
        per = {}
        for a in sorted(k[1] for k in by if k[0] == n):
            rs = by[(n, a)]
            btw = [float(r["between_median"]) for r in rs if r["between_median"] != ""]
            per[a] = {
                "sat": float(np.mean([int(r["sat"]) for r in rs])),
                "ground_median": float(np.median([int(r["ground"]) for r in rs])),
                "backbone": float(np.mean([float(r["backbone"]) for r in rs])),
                "clusters_mean": float(np.mean([int(r["clusters"]) for r in rs])),
                "multi_cluster_share": float(np.mean([int(r["clusters"]) > 1 for r in rs])),
                "frozen_inside": float(np.mean([float(r["frozen_inside"]) for r in rs])),
                "partly_frozen": float(np.mean([float(r["partly_frozen"]) for r in rs])),
                "between_median": float(np.median(btw)) if btw else None,
            }
        xs = sorted(per)
        out["structure"][n] = {"per_alpha": per,
                               "sat_50": crossing(xs, [per[a]["sat"] for a in xs], 0.5)}
        print(f"structure n={n}: satisfiable crosses 1/2 at alpha {out['structure'][n]['sat_50']:.2f}")
        for a in xs:
            e = per[a]
            print(f"   a={a:.1f} sat={e['sat']:.2f} ground={e['ground_median']:.0f} backbone={e['backbone']:.2f} "
                  f"clusters={e['clusters_mean']:.2f} (multi {e['multi_cluster_share']:.2f}) "
                  f"frozen_inside={e['frozen_inside']:.2f} partly={e['partly_frozen']:.2f} between={e['between_median']}")

    se = load("search")
    for n in (50, 100, 150, 200):
        rs = [r for r in se if int(r["n"]) == n and float(r["alpha"]) == 0.95]
        ln = np.log2(np.array([int(r["dpll_nodes"]) for r in rs]) + 1)
        out["search_growth"][n] = {
            "instances": len(rs), "sat": float(np.mean([int(r["sat"]) for r in rs])),
            "dpll_log2_median": float(np.median(ln)),
            "dpll_unfinished": int(sum(r["dpll_finished"] == "0" for r in rs)),
            "dpll_seconds_median": float(np.median([float(r["dpll_seconds"]) for r in rs])),
            "gauss_ops_median": float(np.median([int(r["gauss_ops"]) for r in rs])),
            "gauss_seconds_median": float(np.median([float(r["gauss_seconds"]) for r in rs]))}
    ns = sorted(out["search_growth"])
    slope = np.polyfit(ns, [out["search_growth"][n]["dpll_log2_median"] for n in ns], 1)[0]
    out["dpll_bits_per_variable"] = float(slope)
    print(f"growth at alpha 0.95 (clause search: {slope:.3f} bits of work per extra variable)")
    for n in ns:
        e = out["search_growth"][n]
        print(f"   n={n}: sat {e['sat']:.2f}  DPLL median 2^{e['dpll_log2_median']:.1f} nodes "
              f"({e['dpll_unfinished']} hit the limit, median {e['dpll_seconds_median']:.2f}s)  "
              f"Gauss median {e['gauss_ops_median']:.0f} row ops ({e['gauss_seconds_median'] * 1000:.2f} ms)")
    for a in sorted({float(r["alpha"]) for r in se if int(r["n"]) == 150}):
        rs = [r for r in se if int(r["n"]) == 150 and float(r["alpha"]) == a]
        ln = np.log2(np.array([int(r["dpll_nodes"]) for r in rs]) + 1)
        out["search_sweep"][a] = {"sat": float(np.mean([int(r["sat"]) for r in rs])),
                                  "dpll_log2_median": float(np.median(ln)),
                                  "dpll_unfinished": int(sum(r["dpll_finished"] == "0" for r in rs)),
                                  "gauss_ops_median": float(np.median([int(r["gauss_ops"]) for r in rs]))}
    print("sweep at n = 150")
    for a, e in out["search_sweep"].items():
        print(f"   a={a:.2f} sat {e['sat']:.2f}  DPLL median 2^{e['dpll_log2_median']:.1f} "
              f"({e['dpll_unfinished']} at limit)  Gauss {e['gauss_ops_median']:.0f} ops")
    for r in load("scale"):
        out["scale"].setdefault(int(r["n"]), []).append(
            {"sat": int(r["sat"]), "gauss_ops": int(r["gauss_ops"]), "seconds": float(r["gauss_seconds"])})
    print("Gaussian elimination at scale (alpha 0.95)")
    for n, es in sorted(out["scale"].items()):
        print(f"   n={n}: ops {[e['gauss_ops'] for e in es]}  seconds {[round(e['seconds'], 2) for e in es]}")
    with open(HERE / "summary_xor.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
