"""
Part 9 analysis: summary_sat.json from results_sat_structure.csv and
results_sat_search.csv.

structure (n = 12..24), per alpha: chance of a solution, mean backbone over
ground states, mean number of clusters, mean share of ground states in the
largest cluster, mean frozen fraction inside clusters, mean share of ground
states sitting in partly frozen clusters (some variables frozen, some free),
median flips between ground states of different clusters.

search (n = 25..100), per alpha: chance of a solution and median / mean log2
DPLL nodes; per n: where the chance crosses 1/2, where the median work peaks,
and how far the work falls from the peak by alpha = 7.
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


def num(x):
    return None if x == "" else float(x)


def main():
    out = {"structure": {}, "search": {}}
    st = list(csv.DictReader(open(HERE / "results_sat_structure.csv")))
    by = defaultdict(list)
    for r in st:
        by[(int(r["n"]), float(r["alpha"]))].append(r)
    for n in sorted({k[0] for k in by}):
        per = {}
        for a in sorted(k[1] for k in by if k[0] == n):
            rs = by[(n, a)]
            btw = [num(r["between_median"]) for r in rs if r["between_median"] != ""]
            per[a] = {
                "sat": float(np.mean([int(r["sat"]) for r in rs])),
                "ground_median": float(np.median([int(r["ground"]) for r in rs])),
                "backbone": float(np.mean([float(r["backbone"]) for r in rs])),
                "clusters_mean": float(np.mean([int(r["clusters"]) for r in rs])),
                "multi_cluster_share": float(np.mean([int(r["clusters"]) > 1 for r in rs])),
                "largest_share": float(np.mean([float(r["largest_share"]) for r in rs])),
                "frozen_inside": float(np.mean([float(r["frozen_inside"]) for r in rs])),
                "partly_frozen": float(np.mean([float(r["partly_frozen"]) for r in rs])),
                "between_median": float(np.median(btw)) if btw else None,
                "log2_nodes_median": float(np.median(np.log2(np.array([int(r["nodes"]) for r in rs]) + 1))),
            }
        xs = sorted(per)
        res = {"per_alpha": per,
               "sat_50": crossing(xs, [per[a]["sat"] for a in xs], 0.5),
               "backbone_50": crossing(xs, [per[a]["backbone"] for a in xs], 0.5),
               "backbone_width_10_90": crossing(xs, [per[a]["backbone"] for a in xs], 0.9)
               - crossing(xs, [per[a]["backbone"] for a in xs], 0.1)}
        out["structure"][n] = res
        print(f"structure n={n}: sat crosses 1/2 at alpha {res['sat_50']:.2f}; backbone crosses 1/2 at "
              f"{res['backbone_50']:.2f} (10->90 width {res['backbone_width_10_90']:.2f})")
        for a in xs:
            e = per[a]
            print(f"   a={a:.2f} sat={e['sat']:.2f} ground={e['ground_median']:.0f} backbone={e['backbone']:.2f} "
                  f"clusters={e['clusters_mean']:.2f} (multi {e['multi_cluster_share']:.2f}) frozen_inside={e['frozen_inside']:.2f} "
                  f"partly_frozen={e['partly_frozen']:.2f} between={e['between_median']}")

    se = list(csv.DictReader(open(HERE / "results_sat_search.csv")))
    by = defaultdict(list)
    for r in se:
        by[(int(r["n"]), float(r["alpha"]))].append(r)
    for n in sorted({k[0] for k in by}):
        per = {}
        for a in sorted(k[1] for k in by if k[0] == n):
            rs = by[(n, a)]
            ln = np.log2(np.array([int(r["nodes"]) for r in rs]) + 1)
            sat = np.array([int(r["sat"]) for r in rs])
            per[a] = {"sat": float(sat.mean()), "log2_nodes_median": float(np.median(ln)),
                      "log2_nodes_mean": float(ln.mean()),
                      "log2_nodes_median_sat": float(np.median(ln[sat == 1])) if sat.any() else None,
                      "log2_nodes_median_unsat": float(np.median(ln[sat == 0])) if (sat == 0).any() else None}
        xs = sorted(per)
        med = [per[a]["log2_nodes_median"] for a in xs]
        peak = xs[int(np.argmax(med))]
        res = {"per_alpha": per, "sat_50": crossing(xs, [per[a]["sat"] for a in xs], 0.5),
               "peak_alpha": peak, "peak_log2_nodes": max(med),
               "log2_nodes_at_7": per[xs[-1]]["log2_nodes_median"],
               "log2_nodes_at_2": per[xs[0]]["log2_nodes_median"]}
        out["search"][n] = res
        print(f"search n={n}: sat crosses 1/2 at alpha {res['sat_50']:.2f}; median work peaks at alpha {peak} "
              f"(2^{max(med):.1f} nodes); at alpha 2: 2^{res['log2_nodes_at_2']:.1f}, at alpha 7: 2^{res['log2_nodes_at_7']:.1f}")
        for a in xs:
            e = per[a]
            print(f"   a={a:.2f} sat={e['sat']:.2f} median 2^{e['log2_nodes_median']:.1f} mean 2^{e['log2_nodes_mean']:.1f}"
                  f" (sat {e['log2_nodes_median_sat']}, unsat {e['log2_nodes_median_unsat']})")
    with open(HERE / "summary_sat.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
