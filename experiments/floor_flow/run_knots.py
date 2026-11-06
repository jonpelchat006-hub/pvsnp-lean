"""
Part 13: the knot ladder. How far can a SAT solver run each version of SHA-256
backwards?

Versions (knots.py): salt (no carries, no Ch/Maj: every operation is XOR),
chmaj (Ch and Maj kept, carries removed), carries (carries kept, Ch and Maj
replaced by XOR), full (the real compression rounds).
Solvers: CryptoMiniSat with native XOR constraints, and CaDiCaL with clauses
only. Every solve runs in a child process killed after 30 s.

Rounds ladder: unknown message words u = 2 (64 bits) or 4 (128 bits); rounds
r = 4, 8, 12, 16, 17, 18, 19, 20, 24, 32, 48, 64; 3 trials each. Once all 3
trials at some r time out, larger r are skipped for that line.

Bits ladder: only the lowest k bits of word 0 unknown, k = 8, 12, ..., 32;
r = 17, 18, 20, 24, 32, 64; 3 trials each. Once all 3 trials at some k time
out, larger k are skipped for that line. Two extra methods on this ladder:
CryptoMiniSat given plain clauses only (r = 64), and brute force, trying the
k bits in order with numpy (r = 17, 24, 64), under the same 30 s limit.

Gaussian elimination on the salt version alone: u = 1, 2, 4, 8 words; all
rounds of the rounds ladder; 3 trials.

Every answer found is checked by recomputing the state (the recovered words
may differ from the planted ones if several fit). Seed 20261104.
Usage: python run_knots.py  (writes results_knots.csv)
"""

import csv
import random
import time
from multiprocessing import Pool
from pathlib import Path

from knots import brute_force, build, evaluate, gauss_salt, pin_output, read_words, solve

HERE = Path(__file__).parent
SEED = 20261104
ROUNDS = [4, 8, 12, 16, 17, 18, 19, 20, 24, 32, 48, 64]
BIT_ROUNDS = [17, 18, 20, 24, 32, 64]
BITS = [8, 12, 16, 20, 24, 28, 32]
LIMIT = 30
TRIALS = 3
VERSIONS = ("full", "carries", "chmaj", "salt")
SOLVERS = ("cryptominisat", "cadical")
# method -> (solver, native XOR)
METHODS = {"cryptominisat": ("cryptominisat", True), "cadical": ("cadical", False),
           "cms clauses only": ("cryptominisat", False)}
BRUTE_ROUNDS = [17, 24, 64]


def one(ladder, variant, method, u, bits, r, trial):
    rng = random.Random(f"{SEED}-{ladder}-{variant}-{u}-{bits}-{r}-{trial}")
    W = [rng.getrandbits(32) for _ in range(16)]
    target = evaluate(W, r, variant)
    row = {"ladder": ladder, "variant": variant, "method": method,
           "unknown_bits": bits if bits is not None else 32 * u, "rounds": r, "trial": trial}
    if method == "brute force":
        status, w0, dt, tried = brute_force(W, bits, r, variant, target, LIMIT)
        assert status != "unsat"
        ok = "" if w0 is None else int(evaluate([w0] + W[1:], r, variant) == target)
        assert ok in ("", 1)
        row.update(status=status, seconds=round(dt, 3), vars="", clauses="", xors="",
                   and_gates="", verified=ok, tried=tried)
        return row
    solver, native = METHODS[method]
    C, unk, st = build(W, u, r, variant, native, bits=bits)
    assert pin_output(C, st, target)
    status, model, dt = solve(C, solver, LIMIT)
    ok = ""
    if model is not None:
        ok = int(evaluate(read_words(model, unk) + W[len(unk):], r, variant) == target)
        assert ok == 1
    assert status != "unsat", (ladder, variant, method, u, bits, r)
    row.update(status=status, seconds=round(dt, 3), vars=C.n, clauses=len(C.clauses),
               xors=len(C.xors), and_gates=C.ands, verified=ok, tried="")
    return row


def line(job):
    ladder, variant, solver, fixed = job
    rows = []
    steps = ROUNDS if ladder == "rounds" else BITS
    for x in steps:
        u, bits, r = (fixed, None, x) if ladder == "rounds" else (1, x, fixed)
        results = [one(ladder, variant, solver, u, bits, r, t) for t in range(TRIALS)]
        rows += results
        if all(e["status"] == "timeout" for e in results):
            break
    return rows


def gauss_rows():
    rows = []
    for u in (1, 2, 4, 8):
        for r in ROUNDS:
            for trial in range(TRIALS):
                rng = random.Random(f"{SEED}-gauss-{u}-{r}-{trial}")
                W = [rng.getrandbits(32) for _ in range(16)]
                target = evaluate(W, r, "salt")
                words, dt = gauss_salt(W, u, r, target)
                ok = words is not None and evaluate(words + W[u:], r, "salt") == target
                assert ok
                rows.append({"ladder": "rounds", "variant": "salt", "method": "gaussian elimination",
                             "unknown_bits": 32 * u, "rounds": r, "trial": trial, "status": "solved",
                             "seconds": round(dt, 3), "vars": "", "clauses": "", "xors": "",
                             "and_gates": 0, "verified": 1, "tried": ""})
    return rows


def write(rows):
    rows = sorted(rows, key=lambda r: (r["ladder"], r["variant"], r["method"], r["unknown_bits"],
                                       r["rounds"], r["trial"]))
    with open(HERE / "results_knots.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def main():
    t0 = time.time()
    jobs = [("rounds", v, s, u) for v in VERSIONS for s in SOLVERS for u in (4, 2)]
    jobs += [("bits", v, s, r) for r in BIT_ROUNDS for v in VERSIONS for s in SOLVERS]
    jobs += [("bits", v, "cms clauses only", 64) for v in VERSIONS]
    jobs += [("bits", v, "brute force", r) for r in BRUTE_ROUNDS for v in VERSIONS]
    rows = gauss_rows()
    print(f"gauss done ({time.time() - t0:.0f}s)", flush=True)
    write(rows)
    with Pool(2) as pool:
        for rs in pool.imap_unordered(line, jobs):
            rows += rs
            last = rs[-1]
            print(f"{last['ladder']:6s} {last['variant']:8s} {last['method']:13s} "
                  f"bits={last['unknown_bits']:3d} r={last['rounds']:2d}: stopped "
                  f"({time.time() - t0:.0f}s)", flush=True)
            write(rows)                            # after every line, so a cut-off run keeps what it has
    print(f"done in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
