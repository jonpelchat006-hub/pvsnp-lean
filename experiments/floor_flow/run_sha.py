"""
Part 11: the triangle, the prism and the zeros in SHA-256.

A. The cone (triangle -> prism). 4096 random one-block messages, starting
   from the standard initial state. Flip one input bit and compare the working
   state after every round 1..64. Per round:
     reach     state bits (of 256) that differ in at least one message
     mean      average fraction of state bits that differ
     balanced  state bits whose flip rate is within 0.45..0.55
               (4096 samples: one standard error is about 0.008)
   Flips: message word 0 bits 0, 7, 15, 23, 31; message word 15 bit 0 (enters
   at round 16); state word a bit 0 and state word e bit 0 (the chaining input).

B. The zeros (integrals). Vary the k lowest bits of message word 0 over all 2^k
   values, the rest random, and XOR the working state over the 2^k messages
   after every round. A bit whose sum is 0 in every one of T trials is a
   structural zero (a random sum would be 0 in all trials with chance 2^-T).
   k = 1, 2, 4, 8, 12, 16, 20; T = 32 (16 at k = 20); rounds 1..24.
   (k = 1 is a single flip: its zeros are the bits outside the cone.)

C. The constants. A and B again (word-0 bit flips; k = 8, 16, 20) with the
   round constants all zero and with a golden-ratio sequence.

Seed 20261104. Usage: python run_sha.py  (writes results_sha_cone.csv,
results_sha_integral.csv)
"""

import csv
import time
from pathlib import Path

import numpy as np

from sha_rounds import CONSTANTS, IV, bits, check_against_hashlib, rounds_states, xor_sums

HERE = Path(__file__).parent
SEED = 20261104
N = 4096


def cone(K_name, flips, rng):
    rows = []
    K = CONSTANTS[K_name]
    W = rng.integers(0, 2 ** 32, size=(N, 16), dtype=np.uint64).astype(np.uint32)
    base = bits(rounds_states(W, 64, K))                         # (64, N, 256)
    for label, kind, word, bit in flips:
        if kind == "message":
            W2 = W.copy()
            W2[:, word] ^= np.uint32(1 << bit)
            other = bits(rounds_states(W2, 64, K))
        else:
            st = np.broadcast_to(IV, (N, 8)).copy()
            st[:, word] ^= np.uint32(1 << bit)
            other = bits(rounds_states(W, 64, K, state=st))
        diff = base ^ other                                     # (64, N, 256)
        rate = diff.mean(axis=1)                                # (64, 256)
        for r in range(64):
            rows.append({"constants": K_name, "flip": label, "round": r + 1,
                         "reach": int((rate[r] > 0).sum()),
                         "mean": round(float(rate[r].mean()), 5),
                         "balanced": int(((rate[r] >= 0.45) & (rate[r] <= 0.55)).sum())})
    return rows


def integral(K_name, ks, rng, rounds=24):
    rows = []
    K = CONSTANTS[K_name]
    for k in ks:
        T = 16 if k >= 20 else 32
        zero_all = np.ones((rounds, 256), dtype=bool)
        for _ in range(T):
            W = np.broadcast_to(rng.integers(0, 2 ** 32, size=16, dtype=np.uint64).astype(np.uint32),
                                (1 << k, 16)).copy()
            low = np.arange(1 << k, dtype=np.uint32)
            W[:, 0] = (W[:, 0] & ~np.uint32((1 << k) - 1 if k < 32 else 0xFFFFFFFF)) | low
            s = bits(xor_sums(W, rounds, K))                    # (rounds, 256)
            zero_all &= (s == 0)
        for r in range(rounds):
            rows.append({"constants": K_name, "k": k, "trials": T, "round": r + 1,
                         "zero_bits": int(zero_all[r].sum())})
        last = max([r + 1 for r in range(rounds) if zero_all[r].any()], default=0)
        print(f"  integral {K_name} k={k}: zeros survive through round {last}", flush=True)
    return rows


def main():
    assert check_against_hashlib()
    rng = np.random.default_rng(SEED)
    flips = [(f"word0 bit{b}", "message", 0, b) for b in (0, 7, 15, 23, 31)]
    flips += [("word15 bit0", "message", 15, 0), ("state a bit0", "state", 0, 0),
              ("state e bit0", "state", 4, 0)]
    t0 = time.time()
    cone_rows = cone("sha256", flips, rng)
    word0 = [f for f in flips if f[0].startswith("word0")]
    for name in ("zero", "golden"):
        cone_rows += cone(name, word0, rng)
    print(f"cone done ({time.time() - t0:.0f}s)", flush=True)
    int_rows = integral("sha256", [1, 2, 4, 8, 12, 16, 20], rng)
    for name in ("zero", "golden"):
        int_rows += integral(name, [8, 16, 20], rng)
    print(f"integral done ({time.time() - t0:.0f}s)", flush=True)
    for fname, rows in (("results_sha_cone.csv", cone_rows), ("results_sha_integral.csv", int_rows)):
        with open(HERE / fname, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)


if __name__ == "__main__":
    main()
