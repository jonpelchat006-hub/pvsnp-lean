"""
Part 14: crossings by view, and blind eyes.

A. For each version (salt, chmaj, carries, full), k = 4, 8, 12, 16, 24, 32
   unknown low bits of word 0, r = 4, 8, 12, 16, 17, 18, 19, 20, 24, 32, 48,
   64 rounds, and every split s = 0..r (for r >= 32: s = 0-3, every 4th, and
   r-3..r), 3 trials: read the circuit with the lifted elimination eye
   (crossings.view) and record crossings, closed crossings, equations and d'.
   Every equation is checked against the true answer as it is added, and
   whenever d' = 0 the bits read off the equations are checked against the
   planted ones.

B. 65,536 random messages: for each round 1..64, how many bits of that
   round's two new words (a_i and e_i, 64 bits; the other six state words are
   copies of earlier ones) does each blind eye still predict? Bit position p is
   "seen" when the eye agrees with real SHA-256 on it with probability at
   least 0.02 away from 1/2 (about 10 standard errors). Rotations on (real SHA-256) and off (all
   rotation and shift amounts 0, for the reference and the eyes alike).

Seed 20261105. Usage: python run_crossings.py
"""

import csv
import random
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

from crossings import bits, states_by_round, view

HERE = Path(__file__).parent
SEED = 20261105
VERSIONS = ("salt", "chmaj", "carries", "full")
KS = (4, 8, 12, 16, 24, 32)
ROUNDS = (4, 8, 12, 16, 17, 18, 19, 20, 24, 32, 48, 64)
TRIALS = 3
N_BLIND = 1 << 16
SEEN = 0.02


def splits(r):
    if r <= 24:
        return list(range(r + 1))
    return sorted(set(range(4)) | set(range(0, r + 1, 4)) | set(range(r - 3, r + 1)))


def job(args):
    variant, k, r, trial = args
    rng = random.Random(f"{SEED}-{variant}-{k}-{r}-{trial}")
    W = [rng.getrandbits(32) for _ in range(16)]
    rows = []
    for s in splits(r):
        x = view(W, k, r, variant, s)
        rows.append({"variant": variant, "k": k, "rounds": r, "split": s, "trial": trial,
                     "view": "front" if s == r else "back" if s == 0 else "split",
                     "crossings": x["crossings"], "schedule_crossings": x["schedule_crossings"],
                     "forward_crossings": x["forward_crossings"],
                     "backward_crossings": x["backward_crossings"], "closed": x["closed"],
                     "open": x["crossings"] - x["closed"], "equations": x["equations"],
                     "pinned": x["pinned"], "d_prime": x["d_prime"], "solved": x["solved"]})
    return rows


def blind():
    rng = np.random.default_rng(SEED)
    W = [rng.integers(0, 1 << 32, N_BLIND, dtype=np.uint64).astype(np.uint32) for _ in range(16)]
    rows = []
    low = np.array([p % 32 for p in range(64)])
    new = lambda st: bits([st[0], st[4]])                    # a_i and e_i
    eyes = ("chmaj", "carries", "salt")
    for rotations in (True, False):
        gens = {v: states_by_round(W, v, rotations) for v in ("full",) + eyes}
        for r in range(1, 65):
            R = new(next(gens["full"])[1]).astype(np.uint8)
            for eye in eyes:
                rr, st = next(gens[eye])
                assert rr == r
                agree = (new(st).astype(np.uint8) == R).mean(axis=0)    # per bit position
                seen = np.abs(agree - 0.5) >= SEEN
                rows.append({"eye": eye, "rotations": int(rotations), "round": r,
                             "agreement": round(float(agree.mean()), 4),
                             "seen_bits": int(seen.sum()),
                             "exact_bits": int((agree == 1.0).sum()),
                             "seen_bit0": int(seen[low == 0].sum()),
                             "seen_bits1to3": int(seen[(low >= 1) & (low <= 3)].sum()),
                             "seen_bits4up": int(seen[low >= 4].sum()),
                             "max_bias": round(float(np.abs(agree - 0.5).max()), 4)})
    return rows


def write(name, rows):
    with open(HERE / name, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def main():
    t0 = time.time()
    rows_b = blind()
    write("results_blind.csv", rows_b)
    print(f"blind eyes done ({time.time() - t0:.0f}s)", flush=True)
    jobs = [(v, k, r, t) for v in VERSIONS for k in KS for r in ROUNDS for t in range(TRIALS)]
    jobs.sort(key=lambda j: -j[2])                         # long ones first
    rows = []
    with Pool(2) as pool:
        for n, rs in enumerate(pool.imap_unordered(job, jobs), 1):
            rows += rs
            if n % 24 == 0:
                print(f"{n}/{len(jobs)} ({time.time() - t0:.0f}s)", flush=True)
    rows.sort(key=lambda x: (x["variant"], x["k"], x["rounds"], x["trial"], x["split"]))
    write("results_crossings.csv", rows)
    print(f"done in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
