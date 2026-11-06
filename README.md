# pvsnp-lean

A growing, kernel-checked collection of Lean 4 results around the P vs NP
problem. The core library is plain Lean (no Mathlib), so it builds in seconds
anywhere; entries that need Mathlib live in the separate `mathlib/` package.

**Status: P vs NP is open, and nothing here claims to resolve it.** The
collection proves what *can* be proven today — the structure surrounding the
question, a barrier result, and a real lower bound in a restricted model — so
that any future attempt has a sound, audited base to stand on.

Pinned: Lean `v4.35.0` and Mathlib `v4.35.0`. Latest validation (Nov 3):
the core library, including `Resolution.lean` and `Table.lean`, builds from
clean with `--wfail` and passes the axiom audit (179 declarations, only
propext / Classical.choice / Quot.sound) on the pinned Lean `v4.35.0`
(`validation/core-build-4.35.0.txt`, `validation/core-audit-4.35.0.txt`). The
recovered modules were also validated earlier on Lean `v4.33.1`. One change was
needed for 4.35.0: `RepresentationRefinement.lean` used the deprecated
`dif_pos`, now written `simp only [decode, hx, ↓reduceDIte]`, which works on
both versions. The Mathlib package (`Void.lean`) was last built on Oct 28. No
`sorry` or custom axioms.

## Layout

- `PvsNP/`, `PvsNP.lean`: the core library (plain Lean, no Mathlib).
- `mathlib/`: entries that need Mathlib (a separate Lake package).
- `Audit.lean`: prints the axioms each headline theorem uses.
- `validation/`: build and axiom-audit logs for the pinned Lean versions.
- `experiments/floor_flow/`: numerical experiments (Python) that test the
  framework's pictures against known complexity theory and cryptography, in
  14 parts. They range from number partitioning (flows, heat, lattice
  folding, the θ threshold, the backbone) and random 3-SAT, through XOR-SAT
  and SHA-256 round by round, to meet-in-the-middle, the knot ladder and
  crossings. Its `README.md` has the setup, results and honest limits of
  each part. These are measurements, not proofs.
- `RESEARCH_LIBRARY.md`: a source map of older ideas being recovered for
  formalization. Paths in it refer to the author's own machine. The file
  inventory it mentions (`RESEARCH_INVENTORY.csv`) is not published.

## What is proven

| File | Headline theorems | What it says |
|---|---|---|
| `PvsNP/Poly.lean` | `poly_comp_le`, `PolyBound.add/mul/comp` | Polynomial bounds `(n+c)^k` are closed under +, ×, and composition, with explicit constants. |
| `PvsNP/Classes.lean` | `P_subset_NP`, `reduces_trans`, `InNP.of_reduces`, `NPComplete.inP_iff_PeqNP`, `NPeqCoNP_of_PeqNP`, `NPComplete_of_PeqNP` | The theory of NP-completeness over an abstract machine model: an NP-complete problem is in P iff P = NP; P = NP ⇒ NP = coNP; if P = NP then *every* nontrivial problem in P is NP-complete. |
| `PvsNP/Barrier.lean` | `closure_axioms_do_not_decide_PvsNP` | Two models satisfy every closure axiom; one has P = NP, the other P ≠ NP. Arguments using only those properties cannot settle the question (a toy relative of Baker–Gill–Solovay relativization). |
| `PvsNP/SAT.lean` | `sat_iff_certificate`, `sat_iff_bruteForce` | SAT has certificates no longer than the formula; SAT is decidable by exhaustive search (exponential time). |
| `PvsNP/DecisionTree.lean` | `or_complexity_exact` | A genuine lower bound: any decision tree computing OR of n bits has depth ≥ n, and n is achievable. |
| `PvsNP/Representation.lean` | `collision_obstructs_recovery`, `recoverable_of_refines`, `up_pass_not_recoverable` | Tasks using only a representation cannot recover distinctions it erased. Refinements preserve recoverable tasks. An exact directional-cancellation example recovers an idea from the cube-memory work. No runtime claim. |
| `PvsNP/Crossings.lean` | `net_eq_end_sub_start`, `net_bound`, `net_zero_iff_same_side` | Signed changes along a finite sequence of two-sided observations telescope to final side minus starting side, hence lie between −1 and 1. Zero net means the same endpoint side; it does not establish geometric closure. |
| `PvsNP/Reciprocal.lean` | `partial_iff_inverse_multiple`, `positive_fixed_point` | Over exact rationals, reciprocal exchanges the positive domains below and above one; one is its unique positive fixed point. Formalizes the partials/multiples picture. |
| `PvsNP/CayleyDickson.lean` | `nonzero_zero_product`, `left_cancellation_fails`, `nonzero_not_recoverable_from_product` | Exact integer Cayley–Dickson arithmetic checks the recorded sedenion witness `(e1+e10)(e5+e14)=0`. Connects the lost operand distinction to the representation lemmas; retaining the operand preserves recovery. |
| `PvsNP/ClosureUnit.lean` | `natural_root_iff_pronic`, `square_discriminant_iff_pronic` | For natural k, `x²=x+k` has a natural root iff k is a product of consecutive naturals, iff `1+4k` is a square. In particular k=1 has no natural root. Rational irrationality is a separate step. |
| `PvsNP/CountingWaves.lean` | `certified_enumeration` | A duplicate-free list of exactly the triples `a+2b+3c=n` has length `((n+3)²+6)/12`. Core-Lean extraction of the exact-count part of the older waves work; no asymptotic runtime claim. |
| `PvsNP/RationalClosure.lean` | `rational_root_iff_pronic`, `rational_square_discriminant_iff_pronic`, `unit_one_no_rational_root` | Completes the natural-parameter classification over rationals, including negative roots: rational roots exist iff k is a product of consecutive naturals. Unit one has no rational root. |
| `PvsNP/CutFraction.lean` | `ratio_fraction`, `fraction_ratio`, `recovered_closure_fraction` | The positive rational ratio x and cut fraction f=x/(1+x) determine each other exactly. Recovers k=f(2f−1)/(1−f)² and preserves order. |
| `PvsNP/ClosureCutBridge.lean` | `rational_cut_iff_pronic`, `no_rational_golden_cut` | Joins the classification and cut-fraction map. Natural parameters admit rational cuts iff pronic; the golden-cut polynomial has no rational root. |
| `PvsNP/RepresentationRefinement.lean` | `recoverable_iff_fiber_constant`, `equal_future_answers`, `equal_totals_same_future` | Characterizes task-sufficient representations. Compatible transitions preserve equal codes through every future action sequence; equal signed totals preserve future sum-based acceptance. |
| `PvsNP/BinaryRefinement.lean` | `regions_eq_cuts_add_one`, `regions_of_perfect`, `regions_le_pow_depth` | Every full binary refinement tree has one more final region than cut. Perfect depth-d trees have 2^d regions; uneven trees have an upper bound. These counts do not define an algebra. |
| `PvsNP/FutureQuotient.lean` | `code_eq_iff_futureEq`, `safe_encoding_refines_future` | Canonical merging by agreement on all future answers. Task and transitions are well-defined on the quotient; every sufficient compatible encoding retains its distinctions. Abstract, without a minimization algorithm. |
| `PvsNP/FiniteState.lean` | `finite_state_capacity_bound`, `no_finite_exact_counter`, `equality_bits_lower_bound` | Future-distinguishable states require distinct codes. A sharp exact deterministic one-way EQUALITY bound requires at least as many message bits as input bits. An exact counter over all integers cannot use finitely many transition-compatible codes. |
| `PvsNP/GraphBoundary.lean` | `graph_boundary_nonempty_of_separated_walk`, `boundary_map_of_factor`, `opposite_sign_edge_without_zero` | Different labels at walk endpoints force a crossing edge. Boundaries commute with encoding when labels can be decoded. An opposite-sign edge need not contain a zero-valued vertex. No spectral claims. |
| `PvsNP/Orientations.lean` | `balanced_iff_bruteForce`, `balanced_cons_iff`, `balanced_iff_search`, `table_length`, `balanced_iff_grid`, `balanced_iff_meet` | **The saw blade.** Can pieces, each upright or flipped, be oriented to total exactly 0? (PARTITION, NP-complete — Karp 1972, cited not proved.) Proves correct the four tools used on it: brute force over the 2ⁿ branches; mirror symmetry (fix the first piece upright); pruning branches too far from 0 to come back, without losing any solution; the grid of reachable totals, exactly as wide as the total + 1 (n + 1 cells for n pieces of size 1, but as big as the whole tree for 1, 2, 4, …); and meet in the middle. Correctness only: running times are stated in words, not formalized. |
| `PvsNP/Resolution.lean` | `signedSum_split`, `exact_seen_near`, `near_seen_close`, `rounding_gap_le`, `coarse_grid_length` | **The observer's resolution.** An observer with step δ sees each piece as whole steps (a / δ) and misses the rest (a % δ). If the pieces balance exactly, it sees an orientation within its blur; if it sees one within its blur, the real gap is at most 2n(δ − 1); and an orientation best for the coarse pieces is within 2n(δ − 1) of the floor. Its grid has at most total/δ + 1 cells. So getting within h·total of the floor costs a grid of about 2n/h cells, and each halving of h doubles the work (the subset-sum approximation scheme, Ibarra–Kim 1975, cited). Experiment: `experiments/floor_flow`, part 4. |
| `PvsNP/Table.lean` | `parity_keeps_minority`, `width_two_keeps_majority`, `nae3_breaks_all`, `table` | **The table: which rule combines answers.** A rule combines three answers variable by variable. Every system of parity equations keeps `minority` (x ⊕ y ⊕ z), the rule Gaussian elimination works with. Every clause of width ≤ 2 keeps `majority` (the 2-SAT leg). "x0, x1, x2 not all equal" (two 3-literal clauses) breaks all six of Schaefer's rules (constant false, constant true, AND, OR, majority, minority), each with three explicit answers whose combination is not an answer. Schaefer's dichotomy (1978, cited not proved): constraint problems whose kinds share one of the six rules are in P, and all others are NP-complete. Experiment: `experiments/floor_flow`, part 10. |
| `mathlib/PvsNPM/Void.lean` | `absorbed_eq`, `absorbed_eq_of_nonneg`, `card_upright_eq_card_flipped`, `absorbed_ones`, `absorbed_rotating` | **The void.** What cancellation absorbs from a sum (size of the terms minus size of the result) is never negative. For the determinant, exactly half the n! terms are flipped, and what the void absorbs is the permanent of the entry sizes minus ‖det‖ (for a non-negative matrix: permanent − \|det\|). The all-ones matrix absorbs all n!; the identity absorbs nothing; a 2×2 rotating phase absorbs 2 − 2\|sin(θ/2)\|. Since det is easy and the permanent is #P-complete (Valiant 1979, cited not proved), measuring exactly what the void absorbs is the hard part. |

## Build and audit

```bash
# install elan once: https://github.com/leanprover/elan
lake build --wfail
lake env lean Audit.lean   # prints the axioms each headline theorem uses

# the Mathlib entries (first run downloads ~450 MB of prebuilt Mathlib, ~7 GB unpacked)
cd mathlib
lake exe cache get
lake build --wfail
lake env lean Audit.lean
```

Every headline theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), several on none at all.

## Rules of the collection

1. **No `sorry`, no `axiom`, no `native_decide`.** `Audit.lean` must show only
   the three standard axioms. A "proof" that assumes a lemma as an axiom
   proves nothing about that lemma.
2. **Definitions are the attack surface.** The kernel checks proofs, not
   whether a definition means what we say. Keep definitions short, commented
   and separate from proof machinery, and check them by hand.
3. **Any claim about the real P vs NP must be stated against a standard
   machine model** (e.g. Complexitylib's Turing machines below), never a
   home-made one, or it may be a true theorem about the wrong question.
4. **Run new ideas past the barrier.** If an argument would also work in
   both models of `Barrier.lean`, it cannot separate P from NP.

## Landscape (what already exists in Lean)

- **Complexitylib** (Lean 4 + Mathlib) — multi-tape Turing machines, P, NP,
  BPP, PSPACE, Cook–Levin, the time hierarchy theorem, circuits. The natural
  concrete model to plug into `Model`.
- **HardnessReductionsLean** — a Garey–Johnson-style catalog of verified
  NP-hardness reductions (SAT → 3SAT, CLIQUE, VERTEX COVER, …).
- **descriptive-complexity** — machine-free NP-completeness via first-order
  reductions.
- Several public repos claim Lean proofs of P ≠ NP or P = NP. The ones
  examined so far rest on stated axioms or unformalized steps; the
  `#print axioms` check is exactly how to tell.

## Roadmap (next rungs)

0. **The void, continued**: the core lemma behind every monotone lower bound
   (with no subtraction, nothing ever cancels), then a small lower bound
   when cancellation is forbidden next to a case where it provably helps.

1. **Extend the one-way EQUALITY bound to interactive protocols** using a
   fooling-set argument. `FiniteState.lean` now proves the sharp exact
   deterministic one-way capacity bound, including the fixed-bit form.
2. **Decision-tree complexity of PARITY and of sorting (≥ log₂ n!)** — more
   restricted-model lower bounds.
3. **Instantiate `Model` with Complexitylib's Turing machines** (needs
   Mathlib; build on the PC with `lake exe cache get`). Every theorem in
   `Classes.lean` then transfers to the real P and NP.
4. **Real relativization**: oracle machines and the Baker–Gill–Solovay
   theorem.
5. **Bigger lower bounds**, in rough order of difficulty: monotone circuit
   lower bound for CLIQUE (Razborov), PARITY ∉ AC⁰ (Håstad's switching lemma).

## License

MIT (see `LICENSE`). This covers the Lean code, the experiment code and
data, and the write-ups.
