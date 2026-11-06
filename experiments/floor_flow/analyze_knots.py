"""
Part 13 analysis: summary_knots.json from results_knots.csv.

Rounds ladder: for each version, method and number of unknown bits, per round
count how many of the 3 trials were solved within 30 s and the median time of
the solved ones, and the deepest round count at which all 3 were solved.

Bits ladder: for each version, method and round count, the same per number of
unknown bits, and the most unknown bits at which all 3 were solved.
"""

import csv
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).parent


def summarize(rows, step):
    per = {}
    for x in sorted({int(r[step]) for r in rows}):
        rs = [r for r in rows if int(r[step]) == x]
        solved = [float(r["seconds"]) for r in rs if r["status"] == "solved"]
        per[x] = {"solved": len(solved), "trials": len(rs),
                  "median_seconds_solved": float(np.median(solved)) if solved else None,
                  "and_gates": int(rs[0]["and_gates"]) if rs[0]["and_gates"] not in ("", None) else None}
    best = max([x for x, e in per.items() if e["solved"] == e["trials"]], default=0)
    return per, best


def cells(per):
    return "  ".join(f"{x}:{e['solved']}/{e['trials']}"
                     + (f"({e['median_seconds_solved']:.2f}s)" if e["median_seconds_solved"] is not None else "")
                     for x, e in per.items())


def main():
    rows = list(csv.DictReader(open(HERE / "results_knots.csv")))
    out = {"rounds_ladder": {}, "bits_ladder": {}}
    groups = defaultdict(list)
    for r in rows:
        if r["ladder"] == "rounds":
            groups[("rounds", r["variant"], r["method"], int(r["unknown_bits"]))].append(r)
        else:
            groups[("bits", r["variant"], r["method"], int(r["rounds"]))].append(r)
    print("rounds ladder: deepest round count with all 3 trials solved")
    for key in sorted(k for k in groups if k[0] == "rounds"):
        per, best = summarize(groups[key], "rounds")
        name = f"{key[1]} | {key[2]} | {key[3]} bits"
        out["rounds_ladder"][name] = {"per_round": per, "deepest_all_solved": best}
        print(f"  {name:45s} r={best:2d} | {cells(per)}")
    print("bits ladder: most unknown bits with all 3 trials solved")
    for key in sorted((k for k in groups if k[0] == "bits"), key=lambda k: (k[3], k[1], k[2])):
        per, best = summarize(groups[key], "unknown_bits")
        name = f"{key[1]} | {key[2]} | r={key[3]}"
        out["bits_ladder"][name] = {"per_bits": per, "most_bits_all_solved": best}
        print(f"  {name:45s} k={best:2d} | {cells(per)}")
    with open(HERE / "summary_knots.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
