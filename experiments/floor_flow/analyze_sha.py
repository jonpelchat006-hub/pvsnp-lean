"""
Part 11 analysis: summary_sha.json from results_sha_cone.csv and
results_sha_integral.csv.

Per constants and flip: the first round where all 256 state bits are reached
(the triangle closes) and where all 256 flip at a rate within 0.45..0.55 (the
prism starts), plus the reach per round.
Per constants and k: zero-sum bits per round and the last round with any.
"""

import csv
import json
from pathlib import Path

HERE = Path(__file__).parent


def main():
    cone = list(csv.DictReader(open(HERE / "results_sha_cone.csv")))
    out = {"cone": {}, "integral": {}}
    for r in cone:
        key = f"{r['constants']} | {r['flip']}"
        e = out["cone"].setdefault(key, {"reach": [], "balanced": [], "mean": []})
        e["reach"].append(int(r["reach"]))
        e["balanced"].append(int(r["balanced"]))
        e["mean"].append(float(r["mean"]))
    for key, e in out["cone"].items():
        e["first_reached"] = next((i + 1 for i, v in enumerate(e["reach"]) if v == 256), None)
        e["first_balanced"] = next((i + 1 for i, v in enumerate(e["balanced"]) if v == 256), None)
        e["first_touched"] = next((i + 1 for i, v in enumerate(e["reach"]) if v > 0), None)
        print(f"{key:28s} enters {e['first_touched']:>2}  all reached {e['first_reached']:>2}  "
              f"all balanced {e['first_balanced']:>2}")
    for r in csv.DictReader(open(HERE / "results_sha_integral.csv")):
        key = f"{r['constants']} | k={r['k']}"
        out["integral"].setdefault(key, {"zero_bits": []})["zero_bits"].append(int(r["zero_bits"]))
    for key, e in out["integral"].items():
        z = e["zero_bits"]
        e["last_round_with_zeros"] = max((i + 1 for i, v in enumerate(z) if v), default=0)
        print(f"{key:20s} zero bits r1-6 {z[:6]}  last round with zeros {e['last_round_with_zeros']}")
    with open(HERE / "summary_sha.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
