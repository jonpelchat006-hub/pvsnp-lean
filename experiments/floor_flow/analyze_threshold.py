"""
Part 7a analysis: summary_threshold.json from results_threshold.csv.

Per n:
  kappa_50       where half the instances have a perfect split (logistic fit,
                 maximum likelihood over all instances)
  width_90_10    kappa distance from 90% to 10% perfect
  poisson_50     where 1 - exp(-E) = 1/2 with E from the bell-curve count
  mertens        kappa_c(n) = 1 - log2(pi n / 6) / (2n)  (expected count 1)
  theta_50       pi * kappa_50   (the theta scaling: kappa = 1 <-> theta = pi,
                 kappa = 3/pi <-> theta = 3)
  kappa_50_interp  the same point read off by straight-line interpolation
                 between the two b values around 50%
  shift_bits     the offset (in bits per piece) that best fits
                 P(perfect) = 1 - exp(-E(b + shift)) to the data
                 (maximum likelihood; 0 means the bell-curve count needs no
                 correction), with a 95% interval from the likelihood
Per n <= 32, complete-search work (log2 nodes, median per b):
  plateau        median work over kappa >= 1.1 (where almost no instance
                 has a perfect split)
  knee           kappa where the median work first comes within half a bit
                 (a factor 1.41) of the plateau
  climb          bits of work gained per extra bit per piece below the
                 threshold (fit over 0.6 <= kappa <= kappa_50 - 0.1)
"""

import csv
import json
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, minimize

from threshold import kappa_c, mertens_expected

HERE = Path(__file__).parent


def logistic_fit(kap, y):
    kap, y = np.asarray(kap, float), np.asarray(y, float)

    def nll(p):
        k50, logw = p
        z = np.clip((kap - k50) / np.exp(logw), -50, 50)
        q = 1 / (1 + np.exp(z))                   # chance of a perfect split
        q = np.clip(q, 1e-12, 1 - 1e-12)
        return -np.sum(y * np.log(q) + (1 - y) * np.log(1 - q))

    r = minimize(nll, [np.median(kap), np.log(0.03)], method="Nelder-Mead",
                 options={"xatol": 1e-7, "fatol": 1e-9, "maxiter": 4000})
    return r.x[0], np.exp(r.x[1])


def shift_fit(n, rs):
    """Maximum-likelihood shift s (bits) in P = 1 - exp(-E(n, b + s))."""
    b = np.array([int(r["b"]) for r in rs], float)
    par = np.array([int(r["parity"]) for r in rs])
    y = np.array([int(r["perfect"]) for r in rs])

    def nll(s):
        _, even, odd = mertens_expected(n, b + s)
        E = np.where(par == 1, odd, even)
        p = np.clip(1 - np.exp(-E), 1e-12, 1 - 1e-12)
        return -np.sum(y * np.log(p) + (1 - y) * np.log(1 - p))

    grid = np.linspace(-2, 2, 801)
    ll = np.array([nll(s) for s in grid])
    best = grid[int(np.argmin(ll))]
    inside = grid[ll <= ll.min() + 1.92]          # likelihood-ratio 95% interval
    return float(best), [float(inside.min()), float(inside.max())]


def interp_half(ks, ps):
    for i in range(1, len(ks)):
        if ps[i - 1] >= 0.5 > ps[i]:
            return ks[i - 1] + (ps[i - 1] - 0.5) / (ps[i - 1] - ps[i]) * (ks[i] - ks[i - 1])
    return float("nan")


def poisson_half(n):
    def f(b):
        _, even, odd = mertens_expected(n, b)
        return 0.5 * (1 - np.exp(-even)) + 0.5 * (1 - np.exp(-odd)) - 0.5
    return brentq(f, 0.3 * n, 1.6 * n) / n


def main():
    rows = list(csv.DictReader(open(HERE / "results_threshold.csv")))
    by_n = defaultdict(list)
    for r in rows:
        by_n[int(r["n"])].append(r)
    out = {}
    for n, rs in sorted(by_n.items()):
        kap = np.array([float(r["kappa"]) for r in rs])
        y = np.array([int(r["perfect"]) for r in rs])
        k50, w = logistic_fit(kap, y)
        per_b = {}
        for b in sorted({int(r["b"]) for r in rs}):
            sub = [r for r in rs if int(r["b"]) == b]
            counts = np.array([int(r["count"]) for r in sub], float)
            E, even, odd = mertens_expected(n, b)
            pred = np.mean([1 - np.exp(-(odd if int(r["parity"]) else even)) for r in sub])
            entry = {"kappa": b / n, "instances": len(sub),
                     "perfect": float(np.mean([int(r["perfect"]) for r in sub])),
                     "predicted_perfect": float(pred),
                     "mean_count": float(counts.mean()), "expected_count": float(E)}
            if sub[0]["nodes"] != "":
                nodes = np.array([int(r["nodes"]) for r in sub], float)
                entry["log2_nodes_median"] = float(np.median(np.log2(nodes)))
                entry["log2_nodes_mean"] = float(np.mean(np.log2(nodes)))
                entry["unfinished"] = int(sum(r["finished"] == "0" for r in sub))
            per_b[b] = entry
        bs = sorted(per_b)
        ks = np.array([per_b[b]["kappa"] for b in bs])
        ps = np.array([per_b[b]["perfect"] for b in bs])
        k50i = interp_half(ks, ps)
        shift, shift_ci = shift_fit(n, rs)
        res = {"kappa_50": float(k50), "kappa_50_interp": float(k50i),
               "width_90_10": float(2 * np.log(9) * w), "width_predicted": 4.45 / n,
               "poisson_50": float(poisson_half(n)), "mertens": float(kappa_c(n)),
               "shift_bits": shift, "shift_bits_95": shift_ci,
               "theta_50": float(np.pi * k50i), "theta_mertens": float(np.pi * kappa_c(n)),
               "theta_width": float(np.pi * 2 * np.log(9) * w), "per_b": per_b}
        if "log2_nodes_median" in per_b[bs[0]]:
            ln = np.array([per_b[b]["log2_nodes_median"] for b in bs])
            plateau = float(np.median(ln[ks >= 1.1]))
            i = int(np.argmax(ln >= plateau - 0.5))
            knee = ks[i - 1] + (plateau - 0.5 - ln[i - 1]) / (ln[i] - ln[i - 1]) * (ks[i] - ks[i - 1])
            sel = (ks >= 0.6) & (ks <= k50i - 0.1)
            climb = np.polyfit(ks[sel] * n, ln[sel], 1)[0]
            at50 = float(np.interp(k50i, ks, ln))
            res.update(plateau=plateau, knee=float(knee), theta_knee=float(np.pi * knee),
                       climb_bits_per_bit=float(climb), work_at_kappa_50=at50,
                       log2_nodes_at_half_kappa=float(ln[0]))
        out[n] = res
        print(f"n={n:2d} kappa_50={k50i:.4f} (logistic {k50:.4f}; poisson {res['poisson_50']:.4f}, "
              f"mertens {res['mertens']:.4f}) shift={shift:+.2f} bits [{shift_ci[0]:+.2f},{shift_ci[1]:+.2f}]"
              f"  width={res['width_90_10']:.3f} (4.45/n={4.45 / n:.3f})  theta_50={res['theta_50']:.3f}"
              + (f"  work: plateau 2^{res['plateau']:.1f}, at kappa_50 2^{at50:.1f}, knee={knee:.3f}"
                 f" (theta {np.pi * knee:.3f}), climb {climb:.2f} bits/bit"
                 if "plateau" in res else ""))
    with open(HERE / "summary_threshold.json", "w") as fh:
        json.dump({"seed": 20261103, "summary": out}, fh, indent=1)


if __name__ == "__main__":
    main()
