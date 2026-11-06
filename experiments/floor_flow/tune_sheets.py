"""Pick the tape slack for the 4- and 8-sheet versions on separate tuning
instances (seed 99), by median total time to find the answer."""
import time
import numpy as np
from sheets import eight_sheets, four_sheets, planted_instance

rng = np.random.default_rng(99)
for n, fs in [(48, (four_sheets, eight_sheets)), (56, (four_sheets,)), (64, (eight_sheets,))]:
    insts = [planted_instance(rng, n) for _ in range(6)]
    for f in fs:
        for slack in (0, 1, 2):
            ts, tries = [], []
            try:
                for a, T, a64, T64 in insts:
                    t = time.perf_counter()
                    x, w, k = f(a, T, a64, T64, rng, slack=slack)
                    ts.append(time.perf_counter() - t)
                    tries.append(k if x is not None else 99)
            except MemoryError as e:
                print(n, f.__name__, "slack", slack, "too large:", e, flush=True)
                continue
            print(n, f.__name__, "slack", slack, "median s %.3f" % np.median(ts), "tries", tries, flush=True)
