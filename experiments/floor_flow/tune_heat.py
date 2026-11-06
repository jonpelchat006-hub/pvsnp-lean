"""Tune the cooling schedule and the nesting fraction on separate tuning
instances (seed 777), so the reported run is not tuned on its own test set."""
import numpy as np
from floor_flow import exact_floor, gap_of, karmarkar_karp, nested_flow
from heat import anneal

rng = np.random.default_rng(777)
n, K, steps = 32, 12, 10**6
inst = [rng.integers(1, 2**n, size=n, dtype=np.int64) for _ in range(K)]
bits = lambda g: np.log2(np.asarray(g, float) + 1)

print("KK", np.median(bits([gap_of(a, karmarkar_karp(a)) for a in inst])))
for f in (0.1, 0.25, 0.4, 0.5, 0.6, 0.75):
    print("nested", f, np.median(bits([gap_of(a, nested_flow(a, rng, f)) for a in inst])))

print("hot walk", np.median(bits([anneal(a, rng.choice([-1, 1], n), steps, 0, 0, k, [steps])[0]
                                  for k, a in enumerate(inst)])))
for T0, T1 in [(16, 0.5), (8, 0.05), (4, 0.02), (2, 0.01), (1, 0.01), (0.5, 0.01), (4, 1.0), (2, 1.0), (1, 0.5)]:
    g = [anneal(a, rng.choice([-1, 1], n), steps, T0, T1, k, [steps])[0] for k, a in enumerate(inst)]
    print("anneal random start", T0, T1, np.median(bits(g)))
for T0, T1 in [(2, 0.05), (1, 0.01), (0.5, 0.01), (2, 1.0), (1, 0.5)]:
    g = [anneal(a, karmarkar_karp(a), steps, T0, T1, k, [steps])[0] for k, a in enumerate(inst)]
    print("anneal KK start", T0, T1, np.median(bits(g)))
print("floor", np.median(bits([exact_floor(a) for a in inst])))
