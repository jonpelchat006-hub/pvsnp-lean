# Theory proof library: first source map

Started 2026-10-29. Purpose: recover mathematical ideas from our older files
and chats, state them precisely, and accumulate reusable proofs. Relevance to
P vs NP is one possible application; a useful result need not settle it.
This is a sampled inventory, not a completed review or a proof audit.

## Broader computer inventory

The first broader pass recorded 8,112 candidate document/code paths across
16 selected roots on C: and D: in RESEARCH_INVENTORY.csv. This is a file
discovery count, not a count of theory results. It includes application code,
external material, archives, and duplicates. The pass uses rg's default
ignore/hidden-file behavior, skips common dependency/build directories, and
does not read cloud recall-on-access files. It is not an exhaustive disk scan.
SHA-256 comparison of .md/.tex/.lean files under 2 MB found 858 subsequent
identical copies. Other formats have metadata only, not duplicate checks.
The first occurrence in the inventory is not necessarily the authoritative
version; identical_to is a content match, not a provenance decision.

High-value source locations discovered:

| Location | Material and next action |
| --- | --- |
| D:/RESEARCH_MAP.md | Existing August 2026 map; useful starting point, paths and claims need current verification. |
| C:/Users/GamerTech/structural-reasoning/theory/INDEX.md | Index reports 74 Markdown documents and 15 PDFs; folding, closure units, signed crossings, observer frames, coarse-graining, and framework. Extract candidate statements from the actual documents. |
| D:/shovelcat-colony/erdos-incidence-geometry/ | Abstract incidence versus geometric realizability. Inspect constructions and verifiers. |
| D:/shovelcat-colony/Shovelcat/erdos-Fk/ | Orchard constructions, field extensions, and void-anchor notes. Preserve exact coordinate certificates. |
| D:/shovelcat-colony/arc-proposer/ | Sphere generator, sparse vesica expansion, representation/search experiments. Separate closure equations from claimed empirical effects. |
| D:/shovelcat-colony/navier_stokes_theta/INDEX.md | Detailed positive/negative experiment ledger; extract algebraic or discrete conservation statements before attempting continuum claims. |
| D:/shovelcat-colony/app/src/core/ | Spiral-drive addressing and related implementations; look for precise coverage, collision, and reconstruction properties. |
| D:/planet/ | Experiment records, observations, node kit, archives; identify generating code and fixed datasets for each result. |
| D:/shovelcat-network/ | L0-L7 structure and source copies; determine what is original and what is deployed/archive data. |
| C:/Users/GamerTech/Shovelcat-DNA/ | Observer-network theory and protein code. Formalize graph/path or weight identities independently of biological interpretation. |
| C:/Users/GamerTech/Shovelcat-AI/ and Shovelcat-Club/ | Earlier theory and implementations; compare versions with Desktop sources. |
| C:/Users/GamerTech/Downloads/ and OneDrive/{Documents,Desktop}/ | Additional papers, notebooks, and project copies discovered by filename; content review pending. |
| D:/shovelcat-colony/companion/library/ | Large collected corpus with _sources and repeated exports. Useful retrieval index; trace results back to originals. |

Additional candidate families from the structural-reasoning index: telescoping
signed crossings; recurrence x^2=x+k and its positive root; properties of
finite binary cut trees; preservation and loss under coarse-graining;
normalized observer weights. These are candidate extractions from an index,
not established new results. Formalizing an abstract binary-tree identity
does not establish that an empirical folding process realizes an algebra.

## Record for each result

Keep the original source, an informal statement, exact definitions and
assumptions, a Lean statement, proof status, dependencies, examples or
counterexamples, and the proposed application. Distinguish a new theorem
from our formalization of known mathematics. An application needs its own
bridge theorem or empirical evidence.

Statuses: candidate; statement fixed; informal proof reviewed; Lean proof
written; kernel checked; application established. Do not promote a status
on the strength of a chat's wording or a benchmark alone.

## Candidates recovered so far

### 1. Reciprocal domains and the boundary at one

Source chat: "Conceptual Framework Assessment"
(`695f02dc-f858-8327-a80b-a1c27effbc02`, sampled recent material).

Candidate: on positive reals, reciprocal exchanges (0,1) and (1,infinity),
is an involution, and has exactly one fixed point, 1. Logarithm converts
reciprocal into negation. These give a precise version of the older
partials/multiples picture. They do not establish physical emergence or
instability of zero. Use positive-domain hypotheses explicitly; Lean's
totalized inverse and logarithm require care at zero.

### 2. Representation loss and retained distinctions

Source: ../AI Detector/planet/ALGEBRA_LINEAGE.md, especially the old
signature collisions and operand-preserving product records.

Candidate: if an encoding maps two states to the same code but a target
predicate distinguishes them, no decoder using only that code computes the
predicate on both states. A refined encoding can preserve that distinction.
This is a direct formal bridge from the older memory work to restricted
computation models. It becomes a general lower bound only if we prove that
every computation under consideration must suffer such a collision.

### 3. Algebraic zero products with nonzero operands

Source: ../AI Detector/planet/ALGEBRA_LINEAGE.md and its cayley.py reference.
Recorded convention: (a,b)(c,d) = (ac - conjugate(d)b, da + b conjugate(c)).
Recorded witness: (e1 + e10)(e5 + e14) = 0 in dimension 16.

Candidate: define the exact rational/integer algebra with that convention
and prove the witness plus nonzero operands. Numerical annihilator bases
and int64 searches are evidence to reconstruct, not Lean proofs. Do not
identify these zero products with spectral seams or additive cancellation
without a separately defined map and theorem.

### 4. Cancellation and absorption

Existing source: mathlib/PvsNPM/Void.lean.
Candidate extensions: absorption under regrouping; representation
dependence; cancellation-free sums; explicit recovery of permanent from
absorption and determinant on encoded integer matrices. Existing identities
are source-reviewed here but have not been rebuilt in this review.

### 5. Exact counts replacing enumeration

Source: ../lean-kernel-challenge/research/waves/README.md and Waves.lean.
The README reports a proved formula for partitions into parts at most three,
a periodic wave decomposition, and a kernel executable expression.

Next: inspect theorem dependencies and recover a compatible build before
importing. Keep integer partitions distinct from the PARTITION decision
problem. Fixed-family formulas and measured kernel costs do not imply a
polynomial-time algorithm for an unrestricted counting problem.

### 6. Certified compressed arithmetic

Source: ../lean-kernel-challenge/research/polydisc_v9/README.md and lean/.
Candidate reusable results include residue reconstruction, coefficient
bounds, and correctness bridges between compressed and full arithmetic.
Extract general lemmas independently of fixed challenge inputs and timings.

## Additional sources located

- ../Extra/shovelcat_theory_v2_paper.md: hierarchical interfaces, interpolation,
  quaternion operations. Mathematical properties need to be separated from
  the proposed consciousness interpretation.
- ../AI Detector/FOLDING_BALANCE_LAW.md: spatial/spectral consistency proposal
  with a documented failed measurement. Any Fourier theorem must specify
  its signal model; it would not by itself validate the detector.
- Chat "Overview of theory 10.1"
  (`6902d4a1-6cf4-8324-bb6f-d30d03aa6403`): conceptual and numerical claims
  to trace to original papers. Assistant summaries are not proof sources.
- Chat "Review lean-kernel challenge"
  (`01a0f868-0a27-74d2-9529-e72d20f2baae`): cross-project reuse of shared
  expressions and arithmetic simplifications; distinguish reported timings
  from correctness proofs and asymptotic claims.

## First proof batch

Start with representation-loss lemmas and reciprocal-domain lemmas: both
have small, explicit statements and directly recover older ideas. Then
recover existing waves proofs and formalize the exact zero-product witness.
Maintain links back to the sources and record counterexamples as useful
results too.

## Completed batch 1 — 2026-10-29

`PvsNP/Representation.lean`: 11 named theorems, kernel checked. Defines
recoverability as existence of a decoder and refinement as existence of a
projection to the older encoding. Proves collision obstruction, preservation
of collisions under postprocessing, preservation of recoverable tasks under
refinement, and injectivity required for full reconstruction. Includes an
exact integer example of opposing directional contributions cancelling.

Sources read: Desktop Vesica AI/AI Detector/planet/ALGEBRA_LINEAGE.md,
cube_memory.py (collision_audit and separate channels), and the directional
summary expressions in views.py. The example isolates the signed-sum
mechanism; it does not certify those Python implementations or float storage.
The mathematical content is elementary known factorization theory, now
formalized here for reuse. No novelty or general runtime lower bound claimed.

`PvsNP/Crossings.lean`: 5 named theorems, kernel checked. Recovers the
signed-crossing claim from
C:/Users/GamerTech/structural-reasoning/theory/folding/FOLDING_CONTINUITY.md.
Net changes telescope to endpoint side difference. The bound is a discrete
identity for every Boolean sequence; no geometric continuity hypothesis is
required. Clarification to the old interpretation: net zero gives endpoints
on the same side, not necessarily a closed path, physical conservation law,
or validation of a seam detector. Bridging sampled signs/hysteresis in the
Python crossing detector to this model remains separate work.

Validation: the entire core package passed `lake build --wfail`; `lake env
lean Audit.lean` passed, including every new named theorem. All 11
representation theorems use no axioms; the 5 crossing theorems use only
propext and Quot.sound. Compiler: local Lean 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, from the sibling challenge's
.local-tools/lean-4.33.1-windows/bin. The project's lean-toolchain still pins
4.35.0; that version and the separate Mathlib package were not checked in
this batch. Existing source-map status notes above describe the earlier pass.

Next candidates at the end of batch 1 were reciprocal-domain lemmas, the exact
algebraic zero-product witness, and recovery of the waves proofs.

## Completed batch 2 — 2026-10-29

`PvsNP/Reciprocal.lean`: 10 named theorems over Lean's standard exact `Rat`
type. Reciprocal is an involution; it exchanges positive rationals below
one and above one; the positive domain splits at one; one is the unique
positive fixed point. Explicitly records that totalized inverse fixes zero
too, so the positivity hypothesis cannot be silently discarded. These are
standard mathematical facts formalizing the older partials/multiples picture,
not a derivation of physical emergence. The real/logarithmic version remains
pending. Uses only core Lean, without Mathlib.

`PvsNP/CayleyDickson.lean`: 9 named theorems. Read the actual recursive
multiplication/conjugation definitions in Desktop Vesica AI/AI Detector/
planet/cayley.py and the witness in ALGEBRA_LINEAGE.md. Implemented that
convention with recursively nested pairs of unbounded integers (first half
before second half). Kernel reduction checks `(e1+e10)(e5+e14)=0`, both
nonzero operands, and sum-of-squares norms of 2 each. This gives explicit
failure of left cancellation and norm multiplicativity at depth 4.

Bridge to batch 1: the fixed-left product representation cannot recover
whether the right operand is nonzero, while a record retaining that operand
can reconstruct it. This makes the older operand-preserving memory idea
precise. The definitions were reviewed against the Python recurrence; no
full Python/Lean equivalence theorem or finite-doublet census is claimed.
No associativity or division-algebra structure is assumed. Integer-based
certificates are also valid examples within the real-coordinate construction,
but that embedding has not been separately formalized here.

Validation: full core `lake build --wfail` and the expanded axiom audit passed
using the same local Lean 4.33.1 compiler. All 9 Cayley–Dickson theorems use
no axioms. Reciprocal theorems use only standard axioms. No `sorry`, custom
axioms, or `native_decide` were introduced. The 4.35.0 pin is unchanged and
still requires version-specific validation; Mathlib was not rebuilt.

There are now 35 named theorems across the four recovered-theory modules.
Next candidates: closure-unit arithmetic, exact counting/waves proof recovery,
and the real/logarithmic extension of reciprocal domains.

## Completed batch 3 — 2026-10-29

`PvsNP/ClosureUnit.lean`: 11 named theorems, kernel checked. Read
C:/Users/GamerTech/structural-reasoning/theory/folding/FOLDING_CLOSURE_UNIT.md.
For natural k, proves equivalence of a natural root of x*x=x+k, k=m*(m+1)
for some natural m, and a natural square discriminant r*r=1+4*k. Includes
k=0,2,6 witnesses and impossibility at k=1. This is the exact natural-number
part of the old closure-unit claim. Rational-root classification, the real
square-root formula, irrationality, and the measured-cut-fraction mapping
remain separate work. No empirical selection of k or special status for
the golden ratio is inferred. The older note's broader conclusions should
not be read as consequences of these natural-number theorems alone.

`PvsNP/CountingWaves.lean`: 9 named theorems, kernel checked. Read the full
older file at Desktop Vesica AI/lean-kernel-challenge/research/waves/Waves.lean.
Extracted the exact-count argument into core Lean with a new explicit list
enumeration: multiplicity triples for parts of size one, two, and three.
Proved completeness/soundness of membership, no duplicate triples, the
six-step recurrence, and length ((n+3)*(n+3)+6)/12 for every n. A bundled
certificate records all three enumeration properties. The example at one
million evaluates to 83,333,833,334 by kernel decision.

This extraction does not duplicate the old Mathlib partition-type bijection
or trigonometric Sylvester formula; those remain at the original source.
Triples specify multiplicities, so their combinatorial meaning is explicit,
but there is no new formal bridge here to Mathlib's `Nat.Partition` type.
The period-six recurrence mirrors the old proof; it is not a new counting
discovery. A fixed arithmetic expression does not mean constant bit cost:
operand sizes grow with n. Integer partition counting is distinct from the
PARTITION decision problem.

Validation: entire core package passed `lake build --wfail`; the expanded
Audit.lean passed. All new proofs depend only on the three allowed standard
axioms (some on fewer or none). No `sorry`, custom axioms, or `native_decide`.
Compiler remains local Lean 4.33.1; pinned 4.35.0 and the separate Mathlib
package remain unvalidated in these batches. Imports and README updated.

The six recovered-theory modules now contain 55 named theorems. Next useful
bridges are rational closure roots, exact cut-fraction inversion, and the
real/logarithmic domain results; Mathlib-dependent work needs its compatible
toolchain and dependencies restored before claiming checked proofs there.

## Completed batch 4 — 2026-10-29

Five new modules connect earlier results and recover another source family.
The 11 recovered-theory modules now contain 107 public named theorems.
Counts include supporting lemmas; they are not a measure of mathematical
novelty. The core build and complete headline axiom audit passed together.

### Rational closure and exact cut fractions

`PvsNP/RationalClosure.lean` (10 theorems) completes the rational part of
FOLDING_CLOSURE_UNIT.md for natural k. A rational root of x*x=x+k has
denominator one. Positive and negative integer roots are both handled.
Rational roots exist iff k is pronic. Also proves that a natural number
has a rational square root iff it is a natural square, and recovers the
square-discriminant classification even when the proposed root is rational.
In particular x*x=x+1 has no rational root.

`PvsNP/CutFraction.lean` (18 theorems) proves an exact correspondence between
positive rational ratios x and rational fractions 0<f<1:

- f=x/(1+x), with inverse x=f/(1-f).
- Order and the midpoint comparison are preserved.
- The closure parameter is k=f*(2*f-1)/(1-f)^2.
- The equation x*x=x+k becomes f*(2*f-1)=k*(1-f)^2.

`PvsNP/ClosureCutBridge.lean` (3 theorems) joins these proofs: a rational cut
in (0,1) realizes a natural k iff k is pronic; f*f+f=1 has no rational root;
the midpoint realizes k=0. Classification is restricted to natural k, not
arbitrary inferred rational/real parameters. These are standard algebraic
results formalizing the older theory; they do not select an empirical k or
prove that physical cuts are golden. Real-root existence and embeddings
are still separate work.

### Sufficient representations and safe merging

`PvsNP/RepresentationRefinement.lean` (8 theorems) extends the memory-work
results with a precise sufficiency criterion: a task can be recovered from
a code iff it is constant on equal-code states, assuming a nonempty answer
type supplies a default for unused codes. The converse decoder uses classical
choice and has no computability or efficiency claim. Refinements compose.

For repeated state merging, an additional condition is explicit: every
action must preserve equal codes. Then every finite continuation preserves
recoverable answers. A counterexample shows that equal current answers alone
are insufficient. The signed-history application proves equal running totals
preserve sum-based acceptance for every fixed continuation. This provides a
formal correctness ingredient for dynamic programming without a resource
bound, finite-state count, or certification of the original implementations.

Source trail: ALGEBRA_LINEAGE.md and its separate-channel memory work;
SPARSE_VESICA_EXPANSION.md's coarse representation/vocabulary ideas; and
the reachable-total merging already formalized in Orientations.lean.
The source's broad boundary-reconstruction claims are not assumed: an actual
reconstruction needs task sufficiency or an injectivity theorem.

### The binary refinement tower

`PvsNP/BinaryRefinement.lean` (13 theorems), from
C:/Users/GamerTech/structural-reasoning/theory/folding/FOLDING_TOWER.md,
defines an abstract full binary tree. Every such tree has regions=cuts+1.
Perfect depth-d trees have 2^d final regions and 2^d-1 cuts; general trees
have upper bounds in terms of maximum depth. Examples recover the 2/1,
4/3, 8/7, 16/15 sequence and give a depth-two uneven tree with three regions.
This sharpens the source's depth claim: uniform refinement is required for
the exact power-of-two count. Count agreement with algebra dimensions does
not supply algebra operations, geometric realizability, or a biological
identification. The source's reported ESM negatives remain negatives.

### Validation and review

The full core passed `lake build --wfail`; `lake env lean Audit.lean` checked
127 declarations, including every one of the 107 named theorems across the
recovered modules. A script checked audit dependencies against exactly
propext, Classical.choice, and Quot.sound. Saved outputs and source hashes:

- validation/core-build-4.33.1.txt
- validation/core-audit-4.33.1.txt
- validation/core-validation.json

Compiler: Lean 4.33.1 at the previously recorded path/commit. The 4.35.0 pin
is unchanged; that version and the Mathlib package were not validated.
README now states this distinction instead of repeating the earlier blanket
both-packages-build assertion. Independent review found no semantic defect
in the six previous recovered modules and identified this README mismatch.

Next source-driven work: real/logarithmic bridges after restoring the
compatible Mathlib environment; explicit graph/cut properties from the
folding work; finite-state/cardinality lower bounds built on task-sufficient
representations; exact interfaces to existing algorithm implementations.

## Completed batch 5 — 2026-10-29

Three new modules connect the memory and boundary ideas to canonical state
merging, finite capacity, and exact labelled-graph cuts. There are now 139
public named theorems across 14 recovered-theory modules, including supporting
lemmas and formalizations of standard results.

### Canonical future-answer merging

`PvsNP/FutureQuotient.lean` (11 theorems) defines two states as equivalent
when they give the same task answer after every finite action sequence.
Proves this is an equivalence relation preserved by each action; the task
and transitions therefore descend to its quotient. Quotient codes are equal
exactly for future-equivalent states. Every task-sufficient encoding with
compatible transitions refines this quotient when the state type is nonempty.
That hypothesis supplies a default class on unreachable encoding values.

This is a classical mathematical factorization: it does not provide an
effective way to decide future equivalence, build the quotient, or minimize
a machine. Independent review checked the equivalence, transition order,
projection direction, and empty-type condition. Source motivation remains
the earlier retained-distinction memory/coarse-graining work, with no new
discovery claim.

### Future distinctions force memory capacity

`PvsNP/FiniteState.lean` (9 theorems) proves that a representation must be
injective if each distinct pair of states can be distinguished by some
future task answer and the representation recovers the task and respects
transitions. An explicit finite pigeonhole argument gives n<=m for Fin n
states represented by Fin m codes under those conditions.

Applications:

- An exact zero-test counter over all integer states, accepting every integer
  increment as an action, cannot have finitely many compatible codes.
- An exact deterministic one-way EQUALITY protocol requires at least as many
  possible messages as possible inputs. This capacity bound is sharp, including
  empty alphabets. For fixed alphabets of sizes 2^inputBits and 2^messageBits,
  it yields inputBits<=messageBits.

The unbounded counter hypothesis is essential to the counter statement.
The communication theorem specifies one deterministic message and correctness
on every pair; it does not cover randomized or approximate protocols or claim
an interactive communication bound. Distinct-state/cardinality bounds by
themselves are not running-time lower bounds. Source trail: memory/collision
notes in ALGEBRA_LINEAGE.md and the prior representation modules; the proof
methods are standard distinguishability and finite pigeonhole arguments.

### Discrete boundaries and encoded labels

`PvsNP/GraphBoundary.lean` (12 theorems) follows
C:/Users/GamerTech/structural-reasoning/theory/folding/FOLDING_OUTLINE.md and
Desktop Vesica AI/AI Detector/planet/voidsearch.py (`cut`/`query`). Defines
boundary edges by different Boolean endpoint labels, retaining source-list
order and multiplicity. Adjacency is undirected. Proves reversal/complement
symmetries, endpoint-label equality when a path crosses no boundary, and a
nonempty graph boundary for a walk between different labels. Encoding
commutes with boundary extraction when labels can be decoded from the code.

An exact two-vertex (-1,+1) example has a sign-changing edge and no zero-valued
vertex. A zero-vertex set is therefore not the discrete cut boundary. Reading
the source's "nodal outline" as a continuous zero crossing requires a defined
interpolation and hypotheses beyond the graph data.

Other source interpretations remain unproved: eigenvector magnitude |f| is
not automatically geometric distance; near-zero entries do not by themselves
certify bridges or mixedness; reported correlations do not establish identity
of outline and trail. The Python second normalized-Laplacian eigenvector also
has sign/eigenspace choices that this discrete module does not certify. No
spectral theorem, geometric-distance claim, Python implementation equivalence,
or empirical re-analysis is included in the proofs.

### Validation and next work

Full core build with `--wfail` and all 159 audit declarations passed on local
Lean 4.33.1. Every one of the 139 recovered named theorems is included in the
audit; all dependencies are among propext, Classical.choice, and Quot.sound.
Updated outputs/source hashes are saved in validation/core-build-4.33.1.txt,
validation/core-audit-4.33.1.txt, and validation/core-validation.json.
Update (Oct 30): the whole core package, now including
`PvsNP/Resolution.lean`, passes `lake build --wfail` and the audit (167
declarations, standard axioms only) on the pinned Lean 4.35.0; outputs are in
validation/core-build-4.35.0.txt and validation/core-audit-4.35.0.txt. The only
change needed was replacing the deprecated `dif_pos` in
RepresentationRefinement.lean with `↓reduceDIte` (valid on 4.33.1 and 4.35.0).

Useful next directions: a formal finite-prefix/suffix interface for streaming
problems; interactive EQUALITY protocols; discrete graph energy identities;
connecting actual experiment representations to the abstract encodings.
