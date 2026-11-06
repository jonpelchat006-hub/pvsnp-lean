"""
Part 14 analysis: summary_crossings.json from results_crossings.csv and
results_blind.csv.

A. For each version, k and round count (medians over 3 trials):
   - front (s = r) and back (s = 0): crossings, crossings left open after
     closing, and d' (unknown bits the eye could not pin down);
   - fewest crossings over all splits, and where;
   - best split: smallest d', then fewest open crossings;
   - most k with d' = 0 in all trials, at the front, the back and the best split.
B. For each blind eye, with rotations on and off: seen bits per round, the
   last round with any bit seen, and the bits still seen at round 64.
"""

import csv
import json
from collections import defaultdict
from pathlib import Path
from statistics import median

HERE = Path(__file__).parent


def main():
    rows = list(csv.DictReader(open(HERE / "results_crossings.csv")))
    for r in rows:
        for c in ("k", "rounds", "split", "trial", "crossings", "open", "d_prime", "closed", "equations"):
            r[c] = int(r[c])
    trials = defaultdict(lambda: defaultdict(list))
    for r in rows:
        trials[(r["variant"], r["k"], r["rounds"])][r["trial"]].append(r)
    out = {"by_case": {}, "most_k_seen_through": {}}
    print("A. median over trials: front / back / fewest crossings over splits; d' front / back / best")
    for key in sorted(trials):
        v, k, rr = key
        per = []
        for t, rs in trials[key].items():
            rs.sort(key=lambda x: x["split"])
            front = next(x for x in rs if x["split"] == rr)
            back = next(x for x in rs if x["split"] == 0)
            fewest = min(rs, key=lambda x: (x["crossings"], x["split"]))
            best = min(rs, key=lambda x: (x["d_prime"], x["open"], x["split"]))
            per.append((front, back, fewest, best))
        m = lambda f: median(f(p) for p in per)
        case = {
            "front": {"crossings": m(lambda p: p[0]["crossings"]), "open": m(lambda p: p[0]["open"]),
                      "d_prime": m(lambda p: p[0]["d_prime"])},
            "back": {"crossings": m(lambda p: p[1]["crossings"]), "open": m(lambda p: p[1]["open"]),
                     "d_prime": m(lambda p: p[1]["d_prime"])},
            "fewest": {"crossings": m(lambda p: p[2]["crossings"]),
                       "splits": sorted({p[2]["split"] for p in per})},
            "best": {"d_prime": m(lambda p: p[3]["d_prime"]), "open": m(lambda p: p[3]["open"]),
                     "crossings": m(lambda p: p[3]["crossings"]),
                     "splits": sorted({p[3]["split"] for p in per})},
            "all_solved": {"front": all(p[0]["d_prime"] == 0 for p in per),
                           "back": all(p[1]["d_prime"] == 0 for p in per),
                           "best": all(p[3]["d_prime"] == 0 for p in per)},
        }
        out["by_case"][f"{v} | k={k} | r={rr}"] = case
        print(f"  {v:8s} k={k:2d} r={rr:2d} | crossings {case['front']['crossings']:6.0f} / "
              f"{case['back']['crossings']:6.0f} / {case['fewest']['crossings']:6.0f} at s={case['fewest']['splits']}"
              f" | open {case['front']['open']:6.0f} / {case['back']['open']:6.0f} / {case['best']['open']:6.0f}"
              f" | d' {case['front']['d_prime']:4.0f} / {case['back']['d_prime']:4.0f} / {case['best']['d_prime']:4.0f}"
              f" at s={case['best']['splits']}")
    print("most k (of 4, 8, 12, 16, 24, 32) with d' = 0 in every trial: front / back / best split")
    for v in ("salt", "chmaj", "carries", "full"):
        for rr in sorted({k[2] for k in trials}):
            res = {}
            for where in ("front", "back", "best"):
                ks = [k for (vv, k, r2) in trials if vv == v and r2 == rr
                      and out["by_case"][f"{v} | k={k} | r={rr}"]["all_solved"][where]]
                res[where] = max(ks, default=0)
            out["most_k_seen_through"][f"{v} | r={rr}"] = res
            print(f"  {v:8s} r={rr:2d}: {res['front']:2d} / {res['back']:2d} / {res['best']:2d}")

    blind = list(csv.DictReader(open(HERE / "results_blind.csv")))
    out["blind"] = {}
    print("B. blind eyes: seen bits of a_i, e_i (of 64) by round")
    for eye in ("chmaj", "carries", "salt"):
        for rot in ("1", "0"):
            rs = sorted((x for x in blind if x["eye"] == eye and x["rotations"] == rot), key=lambda x: int(x["round"]))
            seen = [int(x["seen_bits"]) for x in rs]
            last = max([int(x["round"]) for x in rs if int(x["seen_bits"]) > 0], default=0)
            first_zero = next((int(x["round"]) for x in rs if int(x["seen_bits"]) == 0), None)
            entry = {"seen_by_round": seen, "first_round_none_seen": first_zero,
                     "last_round_any_seen": last, "seen_at_64": seen[-1],
                     "seen_bit0_at_64": int(rs[-1]["seen_bit0"]),
                     "exact_at_64": int(rs[-1]["exact_bits"])}
            out["blind"][f"{eye} | rotations {'on' if rot == '1' else 'off'}"] = entry
            print(f"  {eye:8s} rotations {'on ' if rot == '1' else 'off'}: rounds 1-8 {seen[:8]}, "
                  f"first none {first_zero}, last any {last}, at 64: {seen[-1]} "
                  f"(bit 0: {entry['seen_bit0_at_64']}, exact {entry['exact_at_64']})")
    with open(HERE / "summary_crossings.json", "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
