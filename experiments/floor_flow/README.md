# Floor experiment: can a flow from the core close the last branch?

**Question.** Pieces are oriented upright or flipped so their total lands on the
void wall (0). Start every branch at the core and let pressure push the
branches outward while the total stays on the wall. Does the last branch reach
closure (θ = 0 or π)? How close do the flow and the standard fast methods get
compared with the true floor?

**Phase language.** Each branch has a phase θ in [0, π] and contributes
`a·cos θ`. It counts only once it has closed, at θ = 0 (upright, e^{i0} = +1) or
θ = π (flipped, e^{iπ} = −1). This is the framework's closure-plus-inversion
reading of π (Shovelcat Theory 10, §3).

## Methods

| Method | What it does |
|---|---|
| true floor | exact, by meet in the middle (checked against brute force on 40 small instances) |
| Karmarkar–Karp | repeatedly lets the two largest branches cancel into the void and keeps their difference as one branch on the next level (largest differencing) |
| greedy | largest piece first, each turned toward 0 |
| core flow (even) | all branches start at θ = π/2 (the core, on the wall); random pressure that keeps the total on the wall; a branch locks when it reaches 0 or π; the one branch left is forced to its nearer closure |
| core flow (sized) | same, but the push grows with a branch's size, so big branches close first |
| core flow (best of n) | the sized flow run n times, keeping the best |

## Setup

Hardest point: n pieces, each a random integer with n bits (Mertens' κ = 1,
just past the easy/hard transition). n = 16 to 40, 30 instances per size,
seed 20261029. Every gap is recomputed exactly from the method's signs. The run
also checks that no method beats the exact floor and that every gap has the
total's parity. Runtime is about 11 s.

## Results (medians; bits above the wall = log₂(gap + 1))

| n | furthest corner | true floor | Karmarkar–Karp | greedy | flow, best of n | flow, sized | flow, even |
|---|---|---|---|---|---|---|---|
| 16 | 19.0 | 2.3 | 6.7 | 11.1 | 10.3 | 14.4 | 14.2 |
| 20 | 23.3 | 2.2 | 9.7 | 14.2 | 13.4 | 17.9 | 18.3 |
| 24 | 27.6 | 2.9 | 12.3 | 18.2 | 17.6 | 21.5 | 22.4 |
| 28 | 31.7 | 2.3 | 15.2 | 22.4 | 20.6 | 25.5 | 26.3 |
| 32 | 36.0 | 2.7 | 18.2 | 25.5 | 23.8 | 29.3 | 30.4 |
| 36 | 40.1 | 2.8 | 21.7 | 29.2 | 28.4 | 33.2 | 34.7 |
| 40 | 44.3 | 3.0 | 24.3 | 33.4 | 32.4 | 36.6 | 38.7 |

## What it shows

1. **The flow always strands exactly one branch, and that branch is the whole
   gap.** Every run checks that the gap equals `a_last·(1 − |cos θ_last|)`. The
   stranded branch sits a median 58–70° short of closure, so it is still mostly
   open. Forcing it to π (or 0) costs about half of that piece or more.
2. **Pushing big branches first leaves a smaller branch stranded** (median rank
   32 of 40 at n = 40). That saves about 2 bits, but it is almost never the very
   smallest piece (1–2 instances in 30).
3. **Rerunning helps, and nesting helps far more.** Best of n gains about 4–6 bits
   over a single flow, and beats Karmarkar–Karp on 9 of 210 instances.
   Karmarkar–Karp, where pairs close against each other and become one unit on
   the next level, lands 6–8 bits closer than the best flow and 9–14 bits closer
   than a single flow.
4. **The true floor stays about 3 bits above the wall at every size** (median
   gap 7 at n = 40), while every fast method drifts further from it as n grows.
   At n = 40, Karmarkar–Karp is about 21 bits (around two million times) further
   from the wall than the floor, and the best flow is about 29 bits further.

This matches the theory for random inputs. The true floor is about √n·2⁻ⁿ on the
scale of the pieces (Karmarkar–Karp–Lueker–Odlyzko). Largest differencing
reaches only about n^(−Θ(log n)). Stable and low-degree algorithms are proven
unable to get near the floor (Gamarnik–Kızıldağ 2021; low-degree hardness 2025).
None of this proves P ≠ NP. It covers random inputs and particular families of
algorithms.

## Part 2: nesting and heat

**Nested flow.** The flow locks a fraction of the branches (10%, 25% or 50%).
The locked group becomes one unit on the next level, sized by its total. Pairs
then close level by level (largest differencing) over that unit and the
branches still open.

**Heat.** A closed branch can reopen and swing through π to the other closure.
A move that brings the total closer to the wall is always taken. A move that
pushes it away is taken with probability e^(−cost/T), where the cost is
measured in bits: log₂(gap after + 1) − log₂(gap before + 1). T cools
geometrically. Three variants, each run for up to 10⁷ flips:
- **anneal**: random start, T from 16 to 0.5
- **anneal from KK**: start at the Karmarkar–Karp answer, T from 2 to 1
- **hot walk**: heat that never cools (every move taken), as the control

The cooling schedules and the nesting fractions were chosen first on separate
tuning instances (`tune_heat.py`, seed 777). The test instances are fresh:
same distribution, seed 20261030, 30 per size. Every gap is recomputed exactly
and checked against the floor and the parity rule. Runtime is about 5 minutes.

### Results (medians; bits above the wall)

| n | true floor | KK | nested 10% | nested 25% | nested 50% | flow, best of n | anneal, 10⁷ flips | hot walk, 10⁷ flips | anneal from KK, 10⁷ flips |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 1.6 | 6.2 | 6.8 | 7.6 | 9.7 | 10.0 | 1.6 | 1.6 | 1.6 |
| 20 | 2.0 | 9.8 | 9.9 | 10.5 | 12.3 | 13.8 | 2.0 | 2.0 | 2.0 |
| 24 | 3.0 | 12.2 | 12.9 | 13.6 | 15.1 | 16.8 | 3.5 | 3.2 | 3.5 |
| 28 | 2.7 | 15.6 | 15.7 | 17.2 | 18.4 | 20.7 | 6.8 | 6.7 | 6.7 |
| 32 | 3.1 | 18.3 | 19.3 | 20.5 | 21.8 | 24.5 | 10.6 | 10.8 | 11.1 |
| 36 | 3.1 | 21.8 | 22.7 | 23.4 | 25.0 | 28.5 | 14.0 | 14.6 | 14.7 |
| 40 | 3.2 | 24.8 | 25.0 | 26.5 | 28.3 | 32.0 | 18.0 | 18.2 | 18.9 |

**Heat over time at n = 40** (bits above the wall after each number of flips):

| flips | 10³ | 10⁴ | 10⁵ | 10⁶ | 10⁷ |
|---|---|---|---|---|---|
| anneal | 31.0 | 28.6 | 24.9 | 21.7 | 18.0 |
| hot walk (never cools) | 31.7 | 28.3 | 25.1 | 21.7 | 18.2 |
| anneal from KK | 24.8 | 24.8 | 24.2 | 20.9 | 18.9 |

### What part 2 shows

1. **Nesting after the flow doesn't beat plain pair closing.** The less the
   flow does first, the better: 10% is nearly Karmarkar–Karp, and 50% is 3–4
   bits worse. Per instance, the 10% version beats KK on 77 of 210 instances
   and loses on most of the rest.
2. **Heat does expand the search. With enough work it gets far closer than
   any of the fast methods** (18 bits at n = 40 against KK's 24.8). Up to
   n = 24 it usually reaches the floor itself, because 10⁷ flips is about as
   many as there are corners.
3. **Cooling adds nothing.** Annealing and heat that never cools end up in the
   same place: annealing is better on 66 instances and worse on 72. That is
   the signature Mertens described: nearby corners have unrelated heights, so
   there is no slope for cooling to follow.
4. **The cost of heat is one doubling of work per bit.** From 10⁵ to 10⁷ flips,
   every heat variant gains 0.8–1.05 bits per doubling at n ≥ 32, which is the
   rate of blind random sampling. At n = 40, heat needs about 10⁵–10⁶ flips just
   to match Karmarkar–Karp, which does about 200 operations. Reaching the
   floor from 18 bits would take about 15 more doublings, around 3×10¹¹
   flips. Meet in the middle gets the exact floor at n = 40 with about 2²⁰
   sums and a sort, because sorting uses structure that heat does not.

This matches Johnson, Aragon, McGeoch and Schevon (1991), who found that
annealing is not competitive with differencing on number partitioning except
on small instances. It also matches Mertens' finding that low-lying energies
behave like independent random numbers.

## Part 3: folding (lattice reduction)

**Folding.** Each piece becomes a vector, and the sheet is the lattice of all
whole-number combinations (the Coster–Joux–LaMacchia–Odlyzko–Schnorr–Stern
embedding, `lattice.py`). A fold cycle subtracts whole copies of shorter
vectors from longer ones, pulling them back toward the core, and swaps when a
later vector is shorter. **LLL** does this in polynomial time. **BKZ-β** folds
blocks of β vectors at a time: bigger blocks fold closer, and the cost of a
block grows exponentially with β.

In the folded basis, a vector whose branch coordinates are all ±1 is an
orientation: every branch closed. A coefficient of 0 means that branch is
left open at the core. Orientations are read from single vectors and from
sums and differences of two vectors, and every answer is checked exactly.

**A. Planted answers.** n pieces with n/density bits each, and a hidden
half-subset whose total is the target. Success means an exact subset with the
target total is found. n = 30–80, density 0.4–1.1, 10 trials per cell, seed
31337.

**B. The part-2 density-1 instances** (same generator and seed). The target
is half the total. When nothing readable comes out, the gap is counted as the
furthest corner (the total). The weight W = 8 was chosen on the tuning
instances. Runtime for both parts together is about 30 minutes, mostly BKZ-50
at n = 70–80.

### A. How far folding reaches: the highest density solved at least half the time

| n | LLL | BKZ-20 | BKZ-30 | BKZ-40 | BKZ-50 |
|---|---|---|---|---|---|
| 30 | 1.1 | 1.1 | 1.1 | (full) 1.1 | (full) 1.1 |
| 40 | 0.8 | 1.1 | 1.1 | 1.1 | (full) 1.1 |
| 50 | 0.6 | 0.7 | 0.9 | 1.1 | 1.1 |
| 60 | 0.5 | 0.7 | 0.8 | 0.9 | 1.1 |
| 70 | 0.4 | 0.6 | 0.7 | 0.8 | 0.9 |
| 80 | 0.4* | 0.5 | 0.6 | 0.7 | 0.8 |

\*LLL at n = 80 solves density 0.4 in only half the trials. "(full)" means the
block covers the whole lattice, which amounts to exact folding. At n = 80 the
median time per fold is 0.08 s for LLL, 0.33 s for BKZ-20, 0.49 s for BKZ-30,
1.2 s for BKZ-40 and 7.8 s for BKZ-50. At n = 60, BKZ-50 still solves
density 1.0 in 7 of 10 trials; at n = 80 nothing solves density 1.0.

### B. Folding the density-1 instances (medians, bits above the wall)

| n | true floor | KK | LLL | best BKZ | instances with nothing readable | open / closed branches in the shortest folded vector (best BKZ) |
|---|---|---|---|---|---|---|
| 16 | 1.6 | 6.2 | 10.1 | 10.7 | 11–12 of 30 | 10 / 6 |
| 20 | 2.0 | 9.8 | 14.5 | 14.3 | 7–9 of 30 | 14 / 6 |
| 24 | 3.0 | 12.2 | 19.4 | 19.4 | 12 of 30 | 17 / 7 |
| 28 | 2.7 | 15.6 | 21.8 | 21.8 | 10 of 30 | 19 / 9 |
| 32 | 3.1 | 18.3 | 26.9 | 25.1 | 13–14 of 30 | 26 / 6 |
| 36 | 3.1 | 21.8 | 39.9 | 39.9 | 17 of 30 | 27 / 9 |
| 40 | 3.2 | 24.8 | 25.9 | 24.3 | 12–14 of 30 | 26 / 14 |

Folding here takes under 0.1 s at every block size, and the block size barely
matters.

### What part 3 shows

1. **Folding reaches the core when the numbers are long, and the reach shrinks
   as n grows.** At a fixed block size, which means polynomial time, the
   highest density folding solves drops steadily with n: LLL goes from 1.1 at
   n = 30 to 0.4 at n = 80, and BKZ-30 from 1.1 to 0.6. Holding the reach
   needs bigger blocks, and each step up in block size costs 2–7 times
   more (at n = 80: 0.5 s, 1.2 s, then 7.8 s). It is the same exchange rate as
   heat: more reach costs exponentially more cycles.
2. **At density 1, folding returns branches to the core instead of closing
   them.** The shortest folded vectors are partial cancellations: at n = 40,
   about 26 of the 40 branches have coefficient 0 (left open at the core) and
   only about 14 are closed. Full orientations, with every branch at 0 or π,
   are rarely the short ones. For a third to a half of the instances none can
   be read at all, and a bigger block does not change that. When one can be
   read, it is worse than Karmarkar–Karp for most sizes; at n = 40 the best
   BKZ is about level with KK (it beats KK on 13 of 30 instances and reaches
   the floor on 2).
3. **This is the known threshold.** With a perfect shortest-vector finder,
   folding solves almost all planted instances below density 0.9408
   (Coster et al. 1992). Real folding falls short of that, and further short
   as n grows. Vafa and Vaikuntanathan (2025) turn the hardness of folding
   into a cap on number partitioning: assuming lattice folding is hard, no
   polynomial-time method gets gaps below about 2^(−log³ n).

## Part 4: the observer's resolution

**Setup.** An observer with step size δ sees each piece only as whole steps,
q = a // δ, and misses the rest, a % δ. It solves its own coarse problem
exactly with the grid of reachable totals. The grid has one cell per coarse
total, so its work is n × (Σq + 1) cells. The step is set from a relative
resolution h, δ = h·total / (2n), so the guarantee proven in
`PvsNP/Resolution.lean` puts the real gap within h·total of the floor. h runs
from the framework's information quantum, h_info = (√π − √φ)/π ≈ 0.1593, down
to 2⁻⁴⁴.

The instances are the part-2 density-1 set (seed 20261030), 30 per size. Each
run checks the guarantee and that the gap is never below the floor. Whenever
a layer of the grid has at most 2²⁴ cells, the grid is actually run and must
agree with an exact meet-in-the-middle solve of the coarse problem. The
solvers were first checked against brute force on 300 small cases. Runtime is
about 2 minutes.

### n = 40 (medians; floor = 3.2 bits above the wall)

| resolution h | grid cells (work) | bits above the wall | reaches the floor | "sees it on the wall" |
|---|---|---|---|---|
| h_info ≈ 0.159 | 2^14.2 | 36.7 | 0 / 30 | 30 / 30 |
| 2⁻⁸ | 2^19.6 | 31.4 | 0 / 30 | 30 / 30 |
| 2⁻¹⁶ | 2^27.6 | 23.4 | 0 / 30 | 30 / 30 |
| 2⁻²⁴ | 2^35.6 | 15.4 | 0 / 30 | 30 / 30 |
| 2⁻³² | 2^43.7 | 6.7 | 2 / 30 | 30 / 30 |
| 2⁻³⁶ | 2^47.7 | 3.6 | 18 / 30 | 30 / 30 |
| 2⁻⁴⁰ (δ = 1, exact) | 2^49.7 | 3.2 | 30 / 30 | 2 / 30 |

**Work needed before half the instances reach the floor:** 2^21 cells at
n = 16, 2^30 at n = 24, 2^39 at n = 32 and 2^48 at n = 40. That is about
n + 8 doublings, roughly 2ⁿ times n.

### What part 4 shows

1. **A coarse observer is fast and sees the wire on the wall.** At h_info the
   grid has about 19,000 cells at n = 40 and solves its coarse problem
   instantly. To it, every one of the 30 instances looks balanced (δ × coarse
   gap ≤ the part it can't see), even though the real gaps are around 2^36.7.
   A wire smaller than the observer's step can sit on either side of the wall
   without the observer being able to tell.
2. **The wire only appears at the very finest resolution.** "Sees it on the
   wall" stays at 30 of 30 all the way down to 2⁻³⁶. It drops to the 2
   instances that really are balanced only at δ = 1, where nothing is hidden.
3. **One doubling of work per bit, exactly.** From 2⁻⁴ to 2⁻²⁸, each doubling
   of cells buys 1.03 bits closer to the wall. Measured grid time grows the same
   way: 0.07 ms at 2⁻⁸, 0.4 ms at 2⁻¹², 6.7 ms at 2⁻¹⁶. Work goes as 1 / h, which
   is the framework's relation Δt_min = h_info / Δθ. For the grid it holds
   exactly.
4. **The floor needs a resolution of about 2⁻ⁿ, so work of about 2ⁿ.**
   Cleverer observers beat the grid. Meet in the middle reaches the exact floor
   at n = 40 with about 2²¹ sums, roughly the square root of the grid's cost. No
   known observer gets there in polynomial work.

Note on h_info: the formula (√π − √φ)/π evaluates to 0.15929. The value 0.15915
quoted in Shovelcat Theory 10 is 1/(2π) = 0.159155, a close but different
number. The test uses the formula's value; the difference doesn't change any
result.

## Part 5: plugging keys

**Setup.** Plug the pieces in one at a time, largest first. For each piece,
try both keys (upright and flipped), read how the rest of the structure
settles with that key in place, and keep the key with the better reading.
Three readings of a partial state (fixed total F, remaining pieces R):
- **exact**: the true best gap of the rest (meet in the middle);
- **KK**: the gap Karmarkar–Karp reaches on |F| plus the remaining pieces;
- **flow**: the best of 8 core flows on the same.

Every cheap reading is also a complete orientation, and the best one seen is
kept, so plugging keys with the KK reading is never worse than KK alone (its
first reading is KK on everything). The KK version is polynomial time: 2n
runs of KK. The instances are the part-2 set (seed 20261030), 30 per size,
and runtime is about 1 minute.

### Results (medians, bits above the wall)

| n | true floor | KK | keys, KK reading | keys, flow reading | keys, exact reading |
|---|---|---|---|---|---|
| 16 | 1.6 | 6.2 | 4.9 | 6.9 | 1.6 |
| 24 | 3.0 | 12.2 | 9.9 | 13.6 | 3.0 |
| 32 | 3.1 | 18.3 | 14.9 | 21.6 | 3.1 |
| 40 | 3.2 | 24.8 | 21.0 | 28.6 | 3.2 |

Keys with the KK reading beat KK on 24–28 of 30 instances for n ≥ 20 and tie
on the rest. The exact reading reaches the floor on all 210 instances.

### What part 5 shows

1. **With a perfect reading, n keys are enough.** Plugging keys one at a time
   with the exact reading reaches the floor every time. This is
   self-reducibility, and it holds for every NP-complete problem: a perfect
   yes/no answer to "can the rest still reach the wall?" turns into the answer
   itself after n plugs. All the cost sits in the reading.
2. **With a cheap reading, keys help but don't close the gap.** Reading with
   KK gets 3–4 bits closer than KK on its own, in polynomial time. That is more
   than heat bought for a million flips, but it still sits about 18 bits above
   the floor at n = 40.
3. **The order matters.** Without keeping the best reading, choosing each key
   by the cheap reading alone came out worse than KK (28 bits at n = 40),
   because each step's choice adds the reading's noise.
4. **Corners have no freedom.** Where the wall slices the cube, every vertex
   has at most one branch strictly between closures: n − 1 bounds are tight
   plus the wall itself. That is why part 1's flow always stranded exactly one
   branch. A cube corner on the wall is a slice vertex where that last branch
   also closes.

## Part 6: sheets of pins (2, 4 and 8 sheets)

**Setup.** Planted subset sum at density 1: n pieces of n bits each, and a
hidden answer that uses n/4 pieces from each half. A *sheet* is a list of
pins, where each pin is a choice of pieces holding its total.
- **2 sheets (meet in the middle):** every choice of n/4 pieces from each half,
  folded against each other at the wall.
- **4 sheets (one layer of tape):** split the answer into two parts, x = x1 + x2.
  The answer can be split many ways (representations). Tape lifts one layer:
  only parts whose total is R mod M survive (x2 needs T − R). M is set to about
  the number of splits, so about one copy of the answer survives the tape.
  The leaves are choices of n/8 pieces per half.
- **8 sheets (two layers of tape):** split each part again and lift a thinner
  layer first. The leaves are choices of n/16 pieces per half. This is the
  structure of Howgrave-Graham and Joux (2010).

If a try loses every copy of the answer (all its pins break), it is repeated
with fresh layers. The tape slack was chosen on separate tuning instances
(`tune_sheets.py`), and keeping about one copy per layer was fastest. Every
answer is checked exactly. There are 10 instances per size (seed 20261103),
and each method that runs at a size gets the same ones. Runtime is about 9
minutes.

### Results (medians; found = hidden answer recovered)

| n | 2 sheets: largest sheet / time | 4 sheets: largest sheet / time | 8 sheets: largest sheet / time |
|---|---|---|---|
| 32 | 2^13.7 / 0.009 s | 2^10.8 / 0.001 s | 2^9.2 / 0.001 s |
| 40 | 2^17.5 / 0.17 s | 2^13.9 / 0.011 s | — |
| 48 | 2^21.4 / 3.5 s | 2^17.0 / 0.13 s | 2^14.7 / 0.03 s |
| 52 | 2^23.3 / 15 s | — | — |
| 56 | — | 2^20.2 / 1.3 s | — |
| 64 | (out of reach here) | 2^23.3 / 24 s | 2^19.1 / 1.9 s |

Every method found the hidden answer on all of its instances (10 of 10 at
every size). The 8-sheet version needed a median of 1–2 tries.

**Fitted growth (log₂ of the largest sheet per piece):**

| | measured | theory |
|---|---|---|
| 2 sheets | 0.48 n | 0.5 n |
| 4 sheets | 0.39 n | 0.41 n |
| 8 sheets | 0.31 n | 0.34 n |

The measured slopes run slightly below theory because of polynomial factors at
these small sizes.

### What part 6 shows

1. **Each layer of tape lowers the exponent, as predicted.** Going from 2 to 4
   to 8 sheets, the largest sheet grows as 2^(0.48n), 2^(0.39n) and
   2^(0.31n). At n = 48, the 8-sheet version is more than 100 times faster
   than meet in the middle. At n = 64 it takes 1.9 s, where meet in the middle
   would need sheets of about 2³¹ pins.
2. **Pins break, and redundancy saves the answer.** Each layer keeps about one
   copy of the answer, so sometimes all copies break and the try is repeated
   (median 1–2 tries for 8 sheets). Thicker layers (more slack) made every try
   succeed but cost more than the retries.
3. **Deeper trees have overhead.** At n = 32 the 8-sheet version does more
   total work (2^14.0) than the 4-sheet version (2^12.8). It pulls ahead only
   as n grows.
4. **Still exponential.** The best tree here grows as about 2^(0.31n). The best
   known version (16 sheets, with the cancelling coefficients −1 and 2) is
   about 2^(0.283n), and in the worst case nothing known beats 2^(0.5n).

## Part 7: the θ threshold and the void reserve

### 7a. Where does it get hard?

**Setup.** n pieces of b bits each (uniform on 1 … 2^b − 1), so the load is
κ = b / n (bits per piece divided by the number of pieces). A *perfect* split has a gap equal to the
parity of the total (0 or 1), the smallest any split can have. For every
instance the run records the exact number of perfect splits (meet in the
middle, each split counted once). For n ≤ 32 it also records the work of
complete Karmarkar–Karp (Korf 1998), a complete search that stops at the first
perfect split or once it has proven the floor. Its floor is checked against
meet in the middle on every instance, and both were first checked against
brute force on 400 small cases.

- n = 16–32: κ from 0.5 to 1.5, 200 instances per b (100 at n = 32), with
  counts and complete search
- n = 36, 40: κ from 0.6 to 1.25, 100 instances per b, counts only
- n = 44: κ from 0.8 to 1.1, 60 instances per b, counts only

That is 27,580 instances (seed 20261103), about 24 minutes on 2 cores.

**Two predictions.**
- **Bell curve (Mertens 1998).** The signed totals pile up as a bell curve, so
  the expected number of perfect splits is E = 2^(n(1−κ)) · √(6/(πn)) for an
  odd total, and half that for an even one. The chance of at least one is
  1 − e^(−E). E = 1 at κ_c(n) = 1 − log₂(πn/6)/(2n). The π comes from the
  bell curve's √(2π), the same constant as Γ(1/2) = √π in the framework's
  threshold theorem (Shovelcat Theory 1).
- **θ scaling.** θ = π·κ, so κ = 1 is θ = π (the limit) and κ = 3/π ≈ 0.955 is
  θ = 3 (wall onset). This scaling is our choice: it pins the limit to π by
  construction. What the test can check is the shape. A fixed wall would put
  the transition in the same window, θ from 3 to π (κ from 0.955 to 1), at
  every n.

### 7a results

| n | κ at 50% (measured) | κ at 50% (bell curve) | best shift, bits per piece [95%] | width, 90% → 10% | 4.45 / n | θ at 50% | work knee: κ (θ) | work plateau (nodes) |
|---|---|---|---|---|---|---|---|---|
| 16 | 0.904 | 0.908 | +0.00 [−0.12, +0.13] | 0.296 | 0.278 | 2.84 | 0.917 (2.88) | 2^10.6 |
| 20 | 0.926 | 0.918 | +0.07 [−0.05, +0.20] | 0.211 | 0.223 | 2.91 | 0.935 (2.94) | 2^14.0 |
| 24 | 0.927 | 0.926 | −0.01 [−0.14, +0.12] | 0.207 | 0.185 | 2.91 | 0.939 (2.95) | 2^17.4 |
| 28 | 0.929 | 0.933 | +0.14 [+0.01, +0.26] | 0.166 | 0.159 | 2.92 | 0.937 (2.94) | 2^21.0 |
| 32 | 0.945 | 0.938 | −0.03 [−0.21, +0.15] | 0.132 | 0.139 | 2.97 | 0.938 (2.95) | 2^24.5 |
| 36 | 0.942 | 0.943 | −0.01 [−0.19, +0.18] | 0.126 | 0.124 | 2.96 | — | — |
| 40 | 0.950 | 0.947 | −0.06 [−0.23, +0.12] | 0.122 | 0.111 | 2.98 | — | — |
| 44 | 0.944 | 0.950 | +0.21 [−0.02, +0.44] | 0.114 | 0.101 | 2.96 | — | — |

"Best shift" is the offset in b that best fits 1 − e^(−E) to the data; 0 means
the formula needs no correction. The width predicted by 1 − e^(−E) is
log₂(ln 10 / ln(10/9)) ≈ 4.45 bits per piece, which is 4.45 / n in κ. The
work knee is where the median work first comes within half a bit of its
plateau, and the plateau is the median over κ ≥ 1.1.

### What 7a shows

1. **The bell curve with its π places the transition at every size, with no
   correction.** The best shift is zero to within about 0.2 bits per piece at
   all eight sizes. One interval (n = 28) just misses zero, about what is
   expected by chance among eight. The measured average number of perfect
   splits matches E across the whole range: for example at n = 32 it is 11.6
   against 11.7 at b = 26, and 0.73 against 0.73 at b = 30.
2. **Hardness is a wall, not a peak.** Below the transition, the complete
   search's work climbs about 1.2–1.4 bits for every extra bit per piece,
   because perfect splits get rarer and take longer to find. It stops climbing
   at the transition. At the 50% point it is already within 0.4–0.6 bits of
   its maximum, and it stays at that maximum all the way out to κ = 1.5
   (2^24.5 nodes at n = 32). The knee sits at κ ≈ 0.92–0.94, on top of the
   transition. The height of the wall grows as about 2^(0.87 n) for this
   search.
3. **In θ units the transition sits just under 3, and it moves.** It goes from
   θ ≈ 2.84 at n = 16 to about 2.96–2.98 at n = 32–44. The bell curve says it
   crosses 3 near n ≈ 50 and reaches π only as n → ∞.
4. **The window narrows like 1/n instead of holding a fixed width.** Measured
   in θ, the 90%→10% window is 0.93 wide at n = 16 and 0.36 at n = 44,
   following 14/n. It is as narrow as the 0.14 cushion only around n ≈ 100, and
   narrower after that. So "wall onset at 3, limit π" describes where the
   transition is heading as n grows, not a window it keeps at any fixed size.

### 7b. The tape's reserve

**Setup.** This is the 4-sheet solver from part 6 (one layer of tape), but with
exact 64-bit totals (n ≤ 56 and n-bit pieces keep every partial total below
2^61). That lets the layer's modulus M be any whole number instead of only a
power of two. The answer splits as x = x1 + x2 in reps = C(n/4, n/8)² ways, and
a layer with modulus M keeps on average c = reps / M copies. **c is the
reserve.** c = 1 keeps one copy on average. c = 1 + (π − 3) ≈ 1.1416 keeps a
0.1416 reserve above one copy, and c = 2^(π−3) ≈ 1.103 is the other reading of
"0.14".

Seventeen reserves from 0.25 to 6 were tested, including both 0.14 points, at
n = 32, 40, 48 and 56. Every instance is tried a fixed number of times at every
reserve, in shuffled order, each try with a fresh layer:
- n = 32, 40: 60 instances × 40 tries
- n = 48: 40 instances × 25 tries
- n = 56: 16 instances × 10 tries

The instances are planted as in part 6 (seed 20261104). Each try records
whether it kept a copy, its seconds, and its work, where work = probes (lookups) + pairs + pins. Every answer is checked exactly.
Runtime is about 25 minutes.

**Model.** A try keeps a copy with chance p = 1 − e^(−βc), where β = 1 is the
Poisson guess. It costs A + Bc: a fixed part A (looking up every leaf) plus a
part that grows with the reserve. The cost per success, (A + Bc)/p, is
smallest at the c* with e^(βc*) − 1 − βc* = βA/B. Counting alone predicts the
work ratio A/B = 2·reps / (5·|leaves|), written down before the runs.

### 7b results

| n | β (fitted) | work A/B: predicted / measured | best reserve c* for work: predicted / measured [95%] | seconds A/B | best reserve c* for seconds [95%] | cost at c = 1.1416 vs the best (work, seconds) |
|---|---|---|---|---|---|---|
| 32 | 0.98 | 1.08 / 1.08 | 1.18 / 1.20 [1.18, 1.21] | 2.5 | 1.67 [1.60, 1.73] | +0%, +4% |
| 40 | 0.99 | 1.64 / 1.64 | 1.39 / 1.40 [1.39, 1.42] | 2.4 | 1.61 [1.57, 1.65] | +2%, +3% |
| 48 | 0.97 | 2.54 / 2.54 | 1.65 / 1.67 [1.65, 1.70] | 3.7 | 1.91 [1.88, 1.95] | +2%, +4% |
| 56 | 0.98 | 3.98 / 3.98 | 1.93 / 1.96 [1.91, 2.02] | 9.4 | 2.60 [2.47, 2.72] | +4%, +17% |

"Cost vs the best" compares the measured cost per success with the cheapest
reserve on the grid.

### What 7b shows

1. **A layer keeps copies the way the Poisson guess says.** The fitted β is
   0.97–0.99, and the survival chance at each reserve matches 1 − e^(−c) to
   within a few hundredths. Instances behave alike: at c = 1 the spread of
   survival between instances is what coin-flip noise alone gives.
2. **The best reserve is set by overhead, and it moves.** Counted in work, the
   best reserve goes 1.20 → 1.40 → 1.67 → 1.96 copies as n goes 32 → 56. Those
   are the values predicted from counting before the runs, to within 0.03.
   Counted in seconds it is larger (1.6–2.6), because looking up a big leaf
   sheet costs more per entry than building pairs. The predicted ratio grows
   like 2^(0.094 n), so the best reserve keeps growing: about 3 copies at
   n = 80 and 5.7 at n = 128.
3. **Nothing special happens at 0.14.** The cost curve is smooth and flat near
   its bottom. At n = 32–48, every reserve from about 1.14 to 1.75 is within 5%
   of the cheapest in both work and seconds, and 1.1416 sits at the low edge
   of that band. At n = 56 the band moves up (2.0–2.5 in seconds). Survival at
   1.1416 runs slightly above the model (pooled z = 1.6), which is why it still
   looks good for work at n = 56. But c = 3.0 is further off (z = 2.2), and with
   17 reserves tested, deviations this size are expected by chance.
4. **Where "about 14% above one copy" does come out.** The best reserve is
   1.146 copies exactly when the fixed cost of a try equals the cost of one
   more surviving copy (A/B = 1, the root of e^c = 2 + c). In work units that
   happens between n = 24 and n = 32. That 1.146 is within 0.005 of 1 + (π − 3) = 1.1416, but this is
   a numerical coincidence (π − ln π = 1.997, close to 2), not a derivation.
   As a rule, a 14% reserve is right for one particular balance between fixed
   and per-copy costs, and the balance changes with the size of the problem.

## Part 8: the backbone (what freezes at the wall)

**Setup.** These are the same instances as part 7a (same seeds), with n = 20–40,
κ from 0.75 to 1.25, and 100 instances per b: 9,600 instances, about 13
minutes. For each instance, meet in the middle finds the 16 lowest corners
(the splits with the smallest gaps) exactly. The finder was first checked
against brute force on 300 small cases, and every gap is recomputed from its
signs. Measured:
- **frozen (best):** the fraction of pieces on the same side in every best
  split. When only one split is best, the whole answer counts as frozen.
- **frozen (8 lowest):** the fraction of pieces on the same side in all 8
  lowest corners.
- **distance:** flips needed to get from the best split to the second best,
  and to the nearest of the other 15 lowest corners, as a fraction of n (a
  split and its mirror count as the same).

The baseline for each measure is 16 random splits. Every perfect / no-perfect
result agrees with part 7a on the same instances.

### Results

| n | frozen (best) crosses 50% at κ | perfect splits cross 50% at κ | frozen (best): width from 10% to 90% | frozen (8 lowest): measured / random | distance to 2nd best (median): measured / random | nearest of 15 (median): measured / random | work vs frozen (8 lowest), ρ | work vs nearest distance, ρ |
|---|---|---|---|---|---|---|---|---|
| 20 | 0.838 | 0.931 | 0.234 | 0.91% / 0.79% | 0.400 / 0.400 | 0.250 / 0.300 | −0.01 | −0.03 |
| 24 | 0.862 | 0.914 | 0.190 | 0.90% / 0.76% | 0.417 / 0.417 | 0.292 / 0.292 | +0.04 | +0.01 |
| 28 | 0.875 | 0.926 | 0.144 | 0.88% / 0.78% | 0.429 / 0.429 | 0.321 / 0.321 | +0.00 | −0.04 |
| 32 | 0.885 | 0.945 | 0.123 | 0.82% / 0.75% | 0.438 / 0.438 | 0.312 / 0.312 | −0.04 | −0.11 |
| 36 | 0.905 | 0.942 | 0.118 | 0.75% / 0.81% | 0.444 / 0.444 | 0.333 / 0.333 | — | — |
| 40 | 0.914 | 0.950 | 0.122 | 0.80% / 0.76% | 0.450 / 0.450 | 0.350 / 0.350 | — | — |

The ρ columns are Spearman correlations with the part-7a search work. They are
taken over instances with no perfect split (sliver only) at 0.9 ≤ κ ≤ 1.1,
computed within each b and then averaged (364–509 instances per n).

### What part 8 shows

1. **The frozen part switches on with the wall, and the switch sharpens with
   n.** The best answer goes from fully loose (many perfect splits, no piece
   pinned) to fully frozen (one best split). The window it takes shrinks from
   0.23 in κ at n = 20 to 0.12 at n = 32–40, roughly like 1/n, so in the limit
   it is a sudden jump. It crosses 50% a little before half the instances
   are sliver-only, when the typical instance has about two best splits left.
   It is above 0.8 by the time the search work reaches its plateau (the
   part 7a knee, κ ≈ 0.94). Monasson et al. (1999) found the same signature
   in random 2+p-SAT: search cost turns exponential where the backbone
   appears all at once.
2. **Nothing is partly frozen: the answer freezes all at once because it is a
   single isolated corner.**
   - The 8 lowest corners agree on about 0.8% of the pieces, the same as 8
     random splits. A small excess at n = 20–28 is gone by n = 36.
   - They sit as far apart as random splits do. The median distance from the
     best split to the second best is 0.40–0.45 of the pieces at every size,
     exactly the random value.
   - Hardly ever (0–0.8% of instances) is any of the next 15 corners within
     10% of n flips.

   There is no shared core and no neighbourhood. The part of the wall that
   touches the sliver is one point with nothing near it.
3. **So nothing local can lead to it.** Among sliver-only instances near the
   wall, the search work is unrelated to how frozen the low corners are (ρ
   from −0.04 to +0.04) or how far apart they sit (ρ from −0.11 to +0.01).
   Mertens' random-energy picture predicts all of this: the low corners of
   number partitioning behave like independent random numbers. Random k-SAT is
   different. Its solutions form clusters, and inside a cluster some variables
   are frozen together (Achlioptas–Coja-Oghlan 2008), so partial freezing
   does exist there.

## Part 9: random 3-SAT next to partition (the sponge)

**Setup.** Random 3-SAT: n variables and m = αn clauses. Each clause has three
distinct variables, each negated with chance 1/2. An assignment's energy is
the number of clauses it breaks. Its ground states are the assignments with
the lowest energy: the solutions, if there are any.
- **Structure (n = 12, 16, 20, 24).** Every one of the 2^n assignments is
  checked. Ground states that differ in one variable are joined into
  clusters. For each cluster, the run records which variables never change
  inside it (frozen) and which do (free).
- **Search work (n = 25, 50, 75, 100).** DPLL with unit propagation, branching
  on the literal with the best Jeroslow–Wang score. The work is the number of
  branch nodes, the same kind of count as complete Karmarkar–Karp's nodes in
  part 7a.

α runs from 2 to 6 (structure) or 7 (search) in steps of 0.25, with 100
instances per cell: 15,200 instances, about 8 minutes. The energies were
checked against direct evaluation, and DPLL against exhaustive checking on
200 random instances. On every structure instance, DPLL's answer agrees with
the exhaustive one.

### Search work (median DPLL nodes)

| n | α where half are satisfiable | at α = 2 | peak (α) | at α = 7 |
|---|---|---|---|---|
| 25 | 4.42 | 2^3.9 | no peak | 2^3.0 |
| 50 | 4.38 | 2^4.9 | 2^5.4 (4.5) | 2^4.2 |
| 75 | 4.33 | 2^5.4 | 2^7.2 (4.5) | 2^5.2 |
| 100 | 4.31 | 2^5.8 | 2^9.3 (4.5) | 2^6.4 |

### Structure at n = 24 (means over 100 instances)

| α | satisfiable | ground states (median) | clusters | instances with 2+ clusters | frozen inside a cluster | ground states in partly frozen clusters | backbone (frozen in all) | flips between clusters (median, of n) |
|---|---|---|---|---|---|---|---|---|
| 2.0 | 100% | 26,460 | 1.3 | 21% | 0% | 0% | 0% | 0.50 |
| 2.5 | 100% | 4,672 | 3.0 | 71% | 5% | 21% | 0% | 0.50 |
| 3.0 | 100% | 804 | 5.2 | 96% | 24% | 80% | 2% | 0.46 |
| 3.5 | 96% | 166 | 4.7 | 96% | 52% | 98% | 14% | 0.42 |
| 4.0 | 83% | 30 | 3.5 | 73% | 72% | 96% | 37% | 0.42 |
| 4.25 | 71% | 18 | 2.8 | 73% | 78% | 93% | 46% | 0.38 |
| 4.5 | 52% | 14 | 2.9 | 66% | 81% | 91% | 50% | 0.38 |
| 5.0 | 15% | 9 | 3.0 | 67% | 86% | 88% | 53% | 0.38 |
| 6.0 | 2% | 6 | 2.3 | 49% | 89% | 73% | 67% | 0.33 |

n = 12, 16 and 20 show the same pattern (`summary_sat.json`).

**Partition at the same size (part 8, n = 24, at its threshold):** every best
split is a cluster of one. Flipping a piece moves the total by twice that
piece, so a single-flip neighbour can tie only if some piece equals the gap
itself, which essentially never happens with pieces of n bits. So each cluster is 100%
frozen, no cluster is partly frozen, the 8 lowest corners share 0.9% of
their pieces (random: 0.8%), and the best splits sit as far apart as random
splits (0.42 of n).

### What part 9 shows

1. **3-SAT's wall is a sponge, partition's is dust.**
   - Near its threshold, a 3-SAT instance's answers come in 2–3 clusters. The
     clusters sit 0.38–0.42 of n apart. Inside each one, about 80% of the
     variables are frozen and the rest are free, and over 90% of ground states
     sit in clusters like that.
   - The clusters form well before the threshold (most instances have several
     by α = 3), and their frozen cores grow steadily as α rises.
   - Partition at its threshold has no clusters at all, only isolated points.
2. **The backbone grows gradually here, not all at once.** The part frozen in
   every ground state climbs from 2% at α = 3 to 50% at α = 4.5 and 67% at
   α = 6. It never reaches 100%, because past the threshold several
   assignments tie for the fewest broken clauses, and they cluster too. In
   theory the 3-SAT backbone jumps suddenly as n → ∞ (Monasson et al. 1999),
   but at n ≤ 24 it is still smeared out.
3. **3-SAT's hardness is a peak; partition's is a wall.**
   - DPLL's work peaks at α ≈ 4.5, just past where half the instances are
     satisfiable, and the peak grows with n (2^5.4 → 2^7.2 → 2^9.3 for
     n = 50 → 100).
   - Past the peak it falls again, to 2^6.4 at α = 7 for n = 100: adding
     clauses makes "no" easier to prove, because contradictions show up sooner.
   - In partition, adding bits past the threshold never made "no" easier
     (part 7a): the search work stays at its plateau.

## Part 10: random 3-XORSAT (a different leg of the table)

**Setup.** Random 3-XORSAT: n variables and m = αn parity equations
x_i + x_j + x_k = b (mod 2), each over three distinct variables, with b random.
Its threshold is near α ≈ 0.92 (Mézard, Ricci-Tersenghi and Zecchina 2003).
Each equation is also written as 4 ordinary 3-SAT clauses, one forbidding each
wrong-parity assignment of its three variables. Breaking an equation then
breaks exactly one of its clauses, so the part-9 tools (every assignment
checked, clusters, DPLL) run on it unchanged. Gaussian elimination over GF(2)
solves the equations directly; its work is counted in row operations.

- **Structure:** n = 12–24, α from 0.3 to 1.5, 100 instances per cell.
- **Search:** DPLL (100,000-node limit) against Gaussian elimination at
  α = 0.95 for n = 50–200, plus an α sweep at n = 150, with 30 instances per
  cell.
- **Scale:** Gaussian elimination alone at n = 10³, 10⁴ and 10⁵.

That is 5,659 instances, about 8 minutes. The checks: on 300 random cases the
clause encoding's energy equals the number of broken equations, and
elimination, DPLL and exhaustive search all agree on satisfiability. On every
run instance that finished, DPLL agrees with elimination.

### Search work at α = 0.95 (medians)

| n | satisfiable | DPLL nodes | DPLL time | elimination row ops | elimination time |
|---|---|---|---|---|---|
| 50 | 37% | 2^4.0 | 4.5 ms | 118 | 0.07 ms |
| 100 | 40% | 2^7.0 | 60 ms | 320 | 0.17 ms |
| 150 | 20% | 2^10.2 | 0.81 s | 582 | 0.25 ms |
| 200 | 20% | 2^12.0 | 5.3 s | 889 | 0.35 ms |

One DPLL run at n = 200 hit the node limit. For comparison, DPLL at the 3-SAT
peak (part 9, α = 4.5) takes 2^5.4, 2^7.2 and 2^9.3 nodes at n = 50, 75 and
100. Elimination at n = 10³, 10⁴ and 10⁵ takes about 12 thousand, 610
thousand and 52 million row operations (34 s at n = 10⁵), growing as about
n^1.8.

**α sweep at n = 150 (median DPLL nodes):** 2^5.4 at α = 0.5, 2^4.9 at 0.8,
2^8.1 at 0.9, a peak of 2^10.2 at 0.95, then 2^9.0 at 1.0–1.1 and 2^7.0 by
1.3–1.5. Elimination takes 65–630 row operations everywhere.

### Structure (one-flip clusters), n = 24

| α | satisfiable | clusters | frozen inside a cluster | backbone |
|---|---|---|---|---|
| 0.3 | 97% | 361 | 61% | 0% |
| 0.5 | 98% | 273 | 81% | 1% |
| 0.8 | 89% | 17 | 92% | 17% |
| 0.9 | 56% | 12 | 93% | 30% |
| 1.0 | 28% | 7.8 | 95% | 32% |
| 1.2 | 1% | 4.5 | 96% | 43% |

### What part 10 shows

1. **For clause search, XOR-SAT looks like 3-SAT.** DPLL's work rises to a
   peak just past the threshold and falls off beyond it, the same
   easy–hard–easy shape as part 9. The peak grows exponentially, by 2–3 bits
   per 50 variables, reaching 2^12 nodes and 5 seconds at n = 200. At n = 100
   it is still below 3-SAT's peak (2^7.0 against 2^9.3), but it keeps
   climbing.
2. **Elimination goes straight through.** The same instances take 889 row
   operations (0.35 ms) at n = 200, about 15,000 times faster than DPLL, with
   no peak at all. It handles 100,000 variables in 34 s.
3. **The landscape doesn't decide; the leg of the table does.**
   - Measured one flip at a time, XOR-SAT's answers are even more broken up
     than 3-SAT's: hundreds of clusters at α = 0.3, and 93–95% frozen inside
     near the threshold, against about 80% for 3-SAT.
   - The reason: flipping any variable that sits in an equation breaks that
     equation, so one-flip moves only reach the variables in no equation.
   - Yet the problem is easy for elimination everywhere, and easy even for
     DPLL far below the threshold.
   - What makes XOR easy is its algebra: equations can be added together.
     Clause search can't see that; elimination uses nothing else.
4. **This is the table from the CSP dichotomy, measured.** XOR equations are
   one of Schaefer's six easy types: any three answers combine into another
   answer by x ⊕ y ⊕ z. 3-SAT clauses have no such rule, and the problem is
   NP-complete. Both basins drain to the same kind of peak for the same clause
   search; only a method that uses the right leg of the table gets through.

## Part 11: SHA-256 round by round (the triangle, the prism and the zeros)

**Setup.** The SHA-256 compression function, vectorized with numpy, records the
256-bit working state after every one of its 64 rounds. With all 64 rounds and
the final feed-forward it matches Python's `hashlib` on 200 random messages.
Seed 20261104, about 1 minute.
- **A. The cone.** Over 4,096 random one-block messages, flip one input bit
  and compare the state after each round. *Reached* bits differ in at least
  one message. *Balanced* bits flip at a rate between 0.45 and 0.55, which is
  fully mixed (one standard error is about 0.008).
- **B. The zeros (integrals).** Run the k lowest bits of message word 0 through
  all 2^k values, with the rest random, and XOR the state over all 2^k
  messages after each round. A bit whose sum is 0 in every trial (32 trials,
  16 at k = 20) is a structural zero. Here k = 1, 2, 4, 8, 12, 16, 20; k = 1 is
  just a single flip.
- **C. The constants.** A and B again with the 64 round constants replaced by
  zeros, and by a golden-ratio sequence (the fractional part of t·φ; t = 1
  gives 0x9E3779B9, the constant used by TEA and RC5).

### A. The cone

| bit flipped | first affects round | all 256 bits reached | all 256 bits balanced |
|---|---|---|---|
| message word 0, bit 0 / 7 / 15 / 23 / 31 | 1 | 5–6 | 7–8 |
| message word 15, bit 0 | 16 | 20 | 22 |
| initial state word a, bit 0 | 1 | 8 | 10 |
| initial state word e, bit 0 | 1 | 5 | 6 |

The reach grows by almost exactly 64 bits, two of the eight state words, per
round: 18, 81, 145, 209, 255 and then 256 for word 0 bit 0.

### B. The zeros (structural zero-sum bits, rounds 1–6)

| k | round 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| 1 | 245 | 191 | 127 | 63 | 10 | 0 |
| 4 | 251 | 198 | 134 | 70 | 11 | 0 |
| 8 | 250 | 191 | 127 | 63 | 5 | 0 |
| 16 | 252 | 199 | 135 | 71 | 11 | 0 |
| 20 | 249 | 194 | 130 | 66 | 9 | 0 |

### C. The constants

With all-zero constants and with the golden sequence, the cone is the same:
every bit is reached by round 5–6 and balanced by round 7–8. The zeros are the
same too: gone by round 6 at k = 8, 16 and 20.

### What part 11 shows

1. **The sliver grows as a triangle and runs on as a prism.**
   - A flipped bit spreads by two state words per round, so the triangle
     closes over all 256 bits by round 5–6, and every bit is fully mixed by
     round 7–8.
   - Each message word starts its own triangle when it enters. The last one,
     word 15, enters at round 16 and is fully mixed by round 22.
   - From there to round 64 is the prism: 42 rounds of full width after the
     last input is mixed in. That is the security margin.
2. **The zeros live only outside the triangle.** The bits whose sums stay zero
   are, round for round, the bits the cone hasn't reached yet. Summing over
   more inputs (up to 2^20) added a few zeros inside the cone in the first
   rounds, but never carried them past round 5. SHA-256 mixes with addition,
   and its carries raise the algebraic degree almost at once, so filling in
   more context buys no extra rounds.
   - Designs that mix only with AND and XOR raise the degree more slowly
     (it about doubles each round), and there the zeros go much further. For
     the full 24-round Keccak-f permutation inside SHA-3, zero-sum sets are
     known, but they need about 2^1575 inputs (Boura, Canteaut and
     De Cannière 2011).
3. **The constants don't build the triangle or the prism; the rounds do.**
   Zero, standard or golden constants give the same cone and the same zeros.
   Constants are there to break symmetries between rounds and words, which
   this test does not measure. SHA-256's own starting state already contains
   the golden field: its third word, 0x3c6ef372, is the fractional part of
   √5 (the square root of the third prime).
4. **Full mixing is the general lens, not the whole story.** By round 8 every
   bit looks like a coin flip, yet published attacks go much deeper. In 2024
   Li, Liu and Wang found the first practical collision for SHA-256 cut down
   to 31 of its 64 steps, and theoretical attacks reach further. They work by
   following differences that cancel along carefully chosen paths: a sharper
   lens than averages over random messages.

## Part 12: prisms meeting at the wall (meet in the middle)

**Setup.**
- **A. Double encryption.** The cipher is Speck32/64 (22 rounds on two 16-bit
  words), vectorized over keys and checked against its published test vector.
  A toy key of k bits fills the low bits of its 64-bit key. Double encryption,
  C = E_k2(E_k1(P)), uses two independent k-bit keys. Brute force tries every
  (k1, k2). Meet in the middle encrypts P under every k1, decrypts C under
  every k2, matches the middles, and checks the survivors on a second pair.
- **B. Even–Mansour.** E(x) = k2 ⊕ P(x ⊕ k1) on n-bit blocks. P is a public
  scramble: a 4-round Feistel network with random round tables, which is a
  pseudorandom permutation (Luby–Rackoff). k1 and k2 are the secret dust on
  its two faces.
  - **Key search** guesses k1; k2 then follows from one query.
  - **Daemen's attack (1991)** queries pairs (x, x ⊕ D). In E(x) ⊕ E(x ⊕ D)
    the outer key cancels. It then computes P(u) ⊕ P(u ⊕ D) offline and
    matches the two sets.

Work counts cipher calls (A), or calls of P plus queries (B). Every recovered
key is checked against the true one. Seed 20261104, 3–5 trials per size, about
3 minutes.

### A. Double encryption (median work)

| key bits per layer (k) | brute force | meet in the middle | time: brute / middle |
|---|---|---|---|
| 6 | 2^12 | 2^7 | 23 ms / 1 ms |
| 8 | 2^16 | 2^9 | 91 ms / 1 ms |
| 10 | 2^20 | 2^11 | 0.47 s / 1 ms |
| 12 | 2^24 | 2^13 | 2.1 s / 2 ms |
| 16 | — | 2^17 | — / 15 ms |
| 20 | — | 2^21 | — / 0.68 s |
| 24 | — | 2^25 | — / 54 s |

At k = 24 (48 key bits in all), brute force would take 2^48 encryptions,
about a year at the measured rate. Meet in the middle took 54 s and a table of
2^24 middles (64 MB). Most of that time went to checking the 2^16 survivors
of the first match.

### B. Even–Mansour (median work)

| block bits (n) | key search | Daemen's attack |
|---|---|---|
| 16 | 2^17 | 2^10 |
| 20 | 2^21 | 2^12 |
| 24 | 2^23.6 | 2^14 |
| 28 | — | 2^16 |
| 32 | — | 2^18 (19 ms) |

### What part 12 shows

1. **Two prisms meeting at the wall cost the square root of one long prism.**
   Encrypting twice with two k-bit keys should mean 2^(2k) work. Meeting in
   the middle takes 2^(k+1): exactly one layer's worth, done from each side.
   That is why double DES was never used and triple DES was. With three
   layers, the best meeting point still leaves two layers on one side, so the
   work stays at 2^(2k).
2. **The dust on the faces cancels in differences.** Even–Mansour's two
   secret n-bit keys (2n key bits) give only about 2^(n/2) security. In
   E(x) ⊕ E(x ⊕ D) the outer key cancels exactly, and a birthday match
   between the oracle's side and the public side finds the inner key. At
   n = 32, a 64-bit key pair fell to about 2^18 work in 19 ms.
3. **The price of meeting is room.** The middle needs a table of one side's
   2^k results. That is the same trade as the 2-sheet solver for partition in
   part 6: one sheet held in memory, the other folded against it.

## Part 13: the knot ladder (salt to DNA)

**The idea.** SHA-256 has two kinds of knots. Its modular additions carry bits
from one position to the next. Its Ch and Maj functions multiply bits (they
are degree 2). Everything else is XOR, rotation and shifting, which is
linear. Take the knots out one kind at a time and measure how much each one
costs someone running the rounds backwards.

**Setup.**
- **The four versions** (`knots.py`), each with the message schedule included:
  - **salt**: additions become XOR, Ch becomes e⊕f⊕g, Maj becomes a⊕b⊕c. No
    knots at all: the whole thing is a linear map over GF(2).
  - **chmaj**: Ch and Maj kept, additions made XOR.
  - **carries**: additions kept, Ch and Maj made XOR.
  - **full**: real SHA-256. On 20 random messages, it matches `hashlib`.
- **The task.** Some message bits are unknown and the rest are known. The
  256-bit working state after r rounds is given. Find message bits that give
  it. Every answer found is checked by recomputing the state, and all 1,017
  answers checked out.
- **Solvers.** The circuit is written as SAT, with known bits folded in as
  constants. There are two solvers:
  - **CryptoMiniSat 5.17** gets the XOR gates as native XOR constraints, which
    it can eliminate algebraically.
  - **CaDiCaL 1.9.5** gets plain clauses.
- **Time limit.** Every solve gets 30 s and runs in a child process that is
  killed at the limit. Both solvers' own limits proved unreliable: an earlier
  run had CryptoMiniSat going 69–430 s past a 30 s limit, and CaDiCaL ignored
  the interrupt and hung.
- **Rounds ladder.** 2 or 4 unknown words (64 or 128 bits). Round counts are
  r = 4, 8, 12, 16, 17, 18, 19, 20, 24, 32, 48, 64. A line stops at the first
  r where all 3 trials time out.
- **Bits ladder.** Only the lowest k bits of word 0 are unknown, k = 8, 12, …,
  32, at r = 17, 18, 20, 24, 32, 64. A line stops at the first k where all 3
  trials time out. Two extra methods run on this ladder:
  - **CryptoMiniSat given plain clauses**, at r = 64.
  - **Brute force**, which tries the k bits in order with numpy under the same
    30 s limit, at r = 17, 24, 64.
- **Gaussian elimination** on salt alone: 1, 2, 4 or 8 unknown words, every
  round count of the rounds ladder.

Seed 20261104, 3 trials per point, about 83 minutes in all.

### A. Whole words unknown: deepest round count with all 3 trials solved in 30 s

| version | CaDiCaL (64 / 128 bits) | CryptoMiniSat with XOR (64 / 128 bits) | Gaussian elimination (32–256 bits) |
|---|---|---|---|
| full | 16 / 16 | 16 / 16 | — |
| carries | 16 / 16 | 16 / 16 | — |
| chmaj | 16 / 16 | 16 / 16 | — |
| salt | 16 / 16 | 18 / 20 | **64** (all 64 rounds, ≤ 0.04 s) |

At r ≤ 16, every version solved in under 0.1 s. At r = 17, every knotted
version timed out in all 3 trials with both solvers. CaDiCaL on salt managed 1
of 3 at 128 bits.

### B. Part of one word unknown: most unknown bits k with all 3 trials solved in 30 s

Each cell gives CaDiCaL / CryptoMiniSat with XOR. 32 is the top of the ladder
(the whole word), and 0 means even 8 bits failed.

| rounds | full | carries | chmaj | salt | brute force (all four versions) |
|---|---|---|---|---|---|
| 17 | 16 / 12 | 16 / 12 | **32 / 32** | **32 / 32** | 24 (salt 28) |
| 18 | 16 / 16 | 16 / 12 | **32 / 32** | **32 / 32** | — |
| 20 | 12 / 12 | 12 / 12 | 16 / 20 | 16 / **32** | — |
| 24 | 12 / 12 | 12 / 12 | 16 / 16 | 16 / **32** | 24 |
| 32 | 12 / 8 | 12 / 8 | 12 / 16 | 12 / 0 | — |
| 64 | 8 / 0 | 8 / 0 | 12 / 0 | 12 / 0 | **24** |

At r = 64, CryptoMiniSat given plain clauses reached 8 bits on full and
carries and 12 on chmaj and salt. With XOR constraints it reached 0. Brute
force's 24 bits is simply how far 30 s of counting gets: about 2^24 tries.

### What part 13 shows

1. **Up to round 16, no knot matters.**
   - Every version, real SHA-256 included, ran backwards in under 0.1 s with
     up to 128 unknown bits.
   - In rounds 1–16, each message word enters once, as that round's W_t. With
     the output known, the solver can peel rounds off from the end. Each step
     has one answer, and unit propagation undoes even the additions without
     guessing.
   - The fold starts at round 17. That is when the message schedule feeds
     words back in: W16 depends on W0, W1, W9 and W14.
   - With 64 or more unknown bits, every knotted version fails right there.
     CaDiCaL fails on salt there too.
   - So the first wall is the wiring, where the logs cross back over each
     other, not the knots.
2. **Near the wall, the carries are the hard knot.**
   - At rounds 17–18, the Ch/Maj version is as easy as salt: the whole 32-bit
     word in seconds.
   - The two versions with carries stall at 12–16 bits.
   - Ch and Maj are small knots, each tying 3 bits at one position. A carry
     chain runs the length of a 32-bit word, and a round has 7 additions.
   - In the protein picture: Ch/Maj is a local fold; the carries are the long
     chain.
3. **Deeper, the general lens can't tell salt from DNA.**
   - At 64 rounds, the clause solver gets 12 bits on salt and on chmaj, and 8
     on carries and on full: almost the same.
   - Yet salt is purely linear. Gaussian elimination runs all 64 rounds
     backwards with 256 unknown bits in 0.04 s.
   - So salt only looks hard through the wrong lens. This is part 10 again
     (XOR-SAT: clause search struggles, elimination walks through), now inside
     a real hash design.
   - It is also the "follow the line and change the lens" picture. With the
     lens that matches its structure, the salt bacterium dissolves.
4. **A lens has to fit the whole circuit.**
   - CryptoMiniSat's native XOR handling is a partial version of the
     elimination lens. It carried salt to the full 32-bit word through round
     24, well past CaDiCaL's 16 bits.
   - At round 32 it failed on salt even with 8 unknown bits.
   - At 64 rounds it failed with 8 bits on every version, while the same
     solver given plain clauses solved 8–12.
   - Elimination over tens of thousands of XOR constraints, tangled with AND
     gates, apparently costs more than it saves. I haven't checked which
     internal limit is responsible.
   - One oddity I can't explain: in A, CryptoMiniSat on salt went deeper with
     128 unknown bits (r = 20) than with 64 (r = 18). With 3 trials it may be
     partly luck.
5. **At full depth, counting beats every solver tried.**
   - Plain brute force reached 24 bits on all four versions at 17, 24 and 64
     rounds; its limit is just speed.
   - Both SAT solvers managed only 8–12 bits at 64 rounds.
   - For the versions with carries, SAT is already worse than counting at
     round 17 (12–16 bits against 24).
   - This matches the literature. The best published preimage attack on
     reduced SHA-256 reaches 45 of 64 steps, and it costs about 2^255.5, only
     slightly below brute force's 2^256 (Khovratovich, Rechberger and Savelieva,
     FSE 2012, bicliques). Nobody has a lens for the full DNA.
6. **The ladder, from Na+Cl to DNA.**
   - Ranked by how far a general solver gets near the wall:
     salt ≈ chmaj < carries ≈ full.
   - The ranking flattens by 64 rounds.
   - What separates salt from DNA is not how hard each looks to a general
     solver. It is whether some lens exists that sees through it: salt has
     one (linear algebra), and full SHA-256 has none that anyone knows.
7. **Limits.**
   - Each solve has 30 s, there are 3 trials per point, and each solver runs
     in its default configuration.
   - A SAT solver failing is not a lower bound. Better encodings, or adding
     structure (as differential attacks do for collisions), can go further.
   - None of this says anything about P vs NP itself. It measures how today's
     general-purpose tools see each knot.

## Part 14: crossings and blind eyes

**The idea.**
- **Crossings.** A line can't pass over another without hiding it. In the
  circuit, a crossing is a knot (an AND inside Ch, Maj or a carry) where both
  inputs still carry unknown lines. Its output is hidden, so it becomes a new
  unknown.
- **Views.** Whether lines cross depends on where you look from, as in a knot
  drawing. Moving the body without overlap keeps it the same thing; lines
  passing over force a rebuild.
- **Blindness.** An eye that is blind to one kind of knot might still see some
  bits.

**Setup** (`crossings.py`). The task is part 13's bits ladder: the lowest k
bits of word 0 are unknown, and the state after r rounds is known.

**A. The lifted elimination eye.**
- **Lines as forms.** Every wire is an affine form over GF(2) in the unknown
  bits. XOR, rotation and shifting keep forms affine.
- **Crossings.** At a knot whose two inputs are both still undetermined, the
  output becomes a new hidden variable. This is linearization: each crossing
  gets its own dimension.
- **Matching.** Wherever a computed word is already known, its bits are
  matched as they come out, lowest first. The known words are the target, the
  IV, or the other side at the meeting point.
- **Determined lines don't cross.** Before every knot, both inputs are reduced
  by the equations found so far, so a line that is already determined crosses
  nothing.
- **Closing.** Once both lines at a crossing are determined, the hidden line
  is determined too, and this is repeated until nothing changes. A crossing
  that never closes stays **open**.
- **Result.** At the end the hidden variables are eliminated. d' is the
  number of unknown bits still not pinned down, so the eye has 2^d'
  candidates left to try.
  - d' = 0: elimination alone finds the answer, and the answer is checked
    against the planted bits.
  - d' = k: the eye learned nothing and is back to counting.
- **Views.** The rounds are written as the sequence a_i, e_i. A split at s
  reads rounds 1..s forwards from the IV and rounds r..s+1 backwards from the
  target. Undoing a round is exact once its message word is known. The two
  sides meet in the four state words around round s.
  - s = r is the front view.
  - s = 0 is the back view.
  - Every split 0..r is tried (every 4th for r ≥ 32).
- **Grid.** Versions salt, chmaj, carries and full; k = 4, 8, 12, 16, 24, 32;
  r = 4 to 64; 3 trials.
- **Checks.**
  - On test cases, every computed word matched the real round values.
  - Every equation was checked against the true answer as it was added.
  - All 6,521 elimination solves returned the planted bits.

**B. Blind eyes.**
- **The eyes.** An eye blind to a kind of knot sees the version with that
  knot removed:
  - blind to carries is part 13's chmaj;
  - blind to Ch/Maj is carries;
  - blind to both is salt.
- **The measure.** On 65,536 random messages, round by round, how many of the
  64 bits of that round's new words a_i and e_i does each eye still predict? A
  bit counts as seen when the eye agrees with real SHA-256 on it at least 0.02
  away from 1/2 (about 10 standard errors).
- **Rotations.** Everything is run again on a version of SHA-256 with every
  rotation and shift amount set to 0, so Σ0, Σ1, σ0 and σ1 become the
  identity.

Seed 20261105, about 23 minutes.

### A. Crossings by view (k = 8 unknown bits, median of 3 trials)

| version | rounds | front | back | fewest (split) | still open at the best split | d' (of 8) |
|---|---|---|---|---|---|---|
| salt | any | 0 | 0 | 0 | 0 | 0 |
| chmaj | 16 | 660 | **0** | 0 (s = 0) | 0 | 0 |
| chmaj | 17 | 724 | 348 | **85** (s = 3) | 0 | 0 |
| chmaj | 20 | 916 | 587 | 511 (s = 3, 5) | 511 | 8 |
| chmaj | 64 | 3,732 | 3,678 | 3,602 (s = 3) | 3,602 | 8 |
| carries | 16 | 3,076 | **0** | 0 (s = 0) | 0 | 0 |
| carries | 17 | 3,318 | 2,711 | 2,565 (s = 1) | 2,430 | 8 |
| carries | 64 | 16,811 | 16,377 | 16,224 (s = 1) | 16,083 | 8 |
| full | 16 | 3,728 | **0** | 0 (s = 0) | 0 | 0 |
| full | 17 | 4,027 | 3,330 | 3,143 (s = 1) | 2,957 | 8 |
| full | 20 | 4,867 | 3,858 | 3,668 (s = 1) | 3,513 | 8 |
| full | 64 | 20,508 | 19,945 | 19,752 (s = 1) | 19,600 | 8 |

### Most unknown bits the eye sees through (d' = 0 in all 3 trials, best split), next to part 13

| rounds | salt | chmaj | carries | full | CaDiCaL in 30 s (part 13: salt / chmaj / carries / full) | brute force in 30 s |
|---|---|---|---|---|---|---|
| ≤ 16 | 32 | 32 | 32 | 32 | whole words, < 0.1 s | — |
| 17 | 32 | 12 | 0 | 0 | 32 / 32 / 16 / 16 | 24 |
| 18 | 32 | 12 | 0 | 0 | 32 / 32 / 16 / 16 | — |
| 20 | 32 | 4 | 0 | 0 | 16 / 16 / 12 / 12 | — |
| 24 | 32 | 0 | 0 | 0 | 16 / 16 / 12 / 12 | 24 |
| 64 | 32 | 0 | 0 | 0 | 12 / 12 / 8 / 8 | 24 |

Here 0 means the eye failed even with 4 unknown bits. At r = 19, chmaj saw
through 4 bits in 2 of 3 trials. At 16 bits and r = 17–18, chmaj was partly
seen: 2 to 7 of the 16 bits were pinned.

### B. Blind eyes: bits of a_i and e_i still seen (of 64)

| eye | rotations | round 1 | 2 | 3 | 4 | 5 | 6 | 8 | 64 |
|---|---|---|---|---|---|---|---|---|---|
| blind to carries | on (real) | 59 | 17 | 0 | 0 | 0 | 0 | 0 | 0 |
| blind to Ch/Maj | on | 60 | 7 | 0 | 0 | 0 | 0 | 0 | 0 |
| blind to both | on | 59 | 8 | 0 | 0 | 0 | 0 | 0 | 0 |
| blind to carries | off | 61 | 49 | 28 | 18 | 8 | 2 | 2 | **2 (exact)** |
| blind to Ch/Maj | off | 59 | 24 | 24 | 6 | 3 | 2 | 0 | 0 |
| blind to both | off | 61 | 24 | 32 | 13 | 3 | 2 | 0 | 0 |

With rotations off, the two bits the carry-blind eye keeps forever are bit 0
of a_i and bit 0 of e_i, right on every message at every round. The other two
eyes see nothing after round 11.

### What part 14 shows

1. **Up to round 16, the body is only moved.**
   - From the back there are no crossings at all, for every version, with up
     to 32 unknown bits.
   - From the front, real SHA-256 shows 3,728 crossings by round 16. Every one
     of them comes undone once the output is reached: none stay open, and the
     eye reads off the answer.
   - The lines that cross from the front un-cross. From the back they never
     crossed. This is the mirror result from the nested-quaternion work again:
     a move that doesn't overlap anything keeps it the same thing.
2. **From round 17, the crossings stay.** That is when word 0 comes back
   around the 16-slot message ring.
   - For the versions with carries, every view has thousands of crossings.
     Even at the best split, about 2,400–3,000 stay open at round 17 and
     19,600 by round 64.
   - The meeting point gives only 256 equations, one per state bit. Each open
     hidden line uses one up. With far more open lines than equations, the eye
     is completely covered: it learned nothing about even 4 unknown bits.
   - The fluid filling the eye is measurable: open lines against room.
3. **The view changes how many crossings you meet, not what you finally see.**
   - For chmaj at round 17, the front meets 724 crossings, the back 348, and a
     split 3 rounds in only 85. All of them close, and every view ends with
     the same d'.
   - That held in all 864 cases (version × k × rounds × trial): every split
     ended with exactly the same d'.
   - Closing crossings until nothing changes gives the same knowledge whatever
     the reading order. Where you stand decides how much tangle you walk
     through on the way, not what you find.
   - For carries and full, the fewest crossings are at s = 1: read one round
     forward, the rest backwards.
4. **Ch/Maj knots fill the room slowly; carries fill it at once.**
   - Ch/Maj-only stays see-through up to 12 bits at rounds 17–18. It is
     covered from about round 19, when its open lines (about 510) pass the 256
     equations.
   - The carry versions are covered from the first round where crossings
     stay. A carry chain makes up to 31 crossings per addition, and there are
     7 additions a round.
5. **This eye is weaker than clause search.**
   - At round 17, CaDiCaL recovered 32 bits on chmaj and 16 on full. This eye
     got 12 and 0.
   - The eye only closes a crossing once both of its lines are determined by
     equations. Clause search also tries values and learns from the dead ends.
     That is parking guesses, which this eye doesn't do.
   - So d' is the cost for one specific eye, not a lower bound.
6. **Selective blindness works exactly where nothing rotates.**
   - Blind to the carries, with the rotations off, the eye sees bit 0 of every
     new word forever. No carry ever reaches bit 0, so the salt view of that
     bit is exact.
   - With SHA-256's real rotations, the same eye is blind by round 3. Each Σ
     moves carried bits from higher up down into bit 0.
   - The rotations are what pull the eye out of the carry-free zone.
7. **XOR is the wrong blindfold for Ch.**
   - Ch(e, f, g) and e⊕f⊕g agree on exactly half of all inputs, so an eye that
     swaps Ch for XOR sees nothing past it, even with no rotations.
   - Linear cryptanalysis uses better stand-ins. Ch agrees with g, or with f,
     3/4 of the time, and Maj with any one of its inputs 3/4 of the time.
   - Choosing what to be blind to is a skill. A good blind eye keeps the part
     that still correlates.

## Files

- `floor_flow.py`: the methods (core flow `core_flow`, nested flow `nested_flow`)
- `lattice.py`: folding (LLL/BKZ via fpylll). BKZ uses fplll's pruning strategies
  (`strategies/default.json` from the fplll repository). Point
  `FPLLL_STRATEGIES` at it.
- `run_fold.py`: part 3 (`python run_fold.py`, or `python run_fold.py B` for part B only)
- `results_fold_planted.csv`, `results_fold_partition.csv`, `summary_fold.json`: part 3
- `run_resolution.py`: part 4 (`python run_resolution.py`; needs numpy only)
- `results_resolution.csv`, `summary_resolution.json`: part 4
- `run_keys.py`, `results_keys.csv`, `summary_keys.json`: part 5
- `sheets.py`, `tune_sheets.py`, `run_sheets.py`, `results_sheets.csv`, `summary_sheets.json`: part 6
- `threshold.py` (complete Karmarkar–Karp in numba, exact counting, the
  bell-curve count), `run_threshold.py`, `analyze_threshold.py`,
  `results_threshold.csv`, `summary_threshold.json`: part 7a
- `reserve.py` (exact 4-sheet solver with any modulus), `run_reserve.py`
  (`python run_reserve.py [n ...]`), `analyze_reserve.py`,
  `results_reserve_<n>.csv`, `summary_reserve.json`: part 7b
- `backbone.py` (exact lowest corners by meet in the middle), `run_backbone.py`,
  `analyze_backbone.py`, `results_backbone.csv`, `summary_backbone.json`: part 8
- `sat3.py` (random 3-SAT, exhaustive energies and clusters in numba, DPLL),
  `run_sat.py`, `analyze_sat.py`, `results_sat_structure.csv`,
  `results_sat_search.csv`, `summary_sat.json`: part 9
- `xorsat.py` (random 3-XORSAT, clause encoding, Gaussian elimination),
  `run_xor.py`, `analyze_xor.py`, `results_xor_structure.csv`,
  `results_xor_search.csv`, `results_xor_scale.csv`, `summary_xor.json`: part 10
- `sha_rounds.py` (SHA-256 round by round in numpy, checked against hashlib),
  `run_sha.py`, `analyze_sha.py`, `results_sha_cone.csv`,
  `results_sha_integral.csv`, `summary_sha.json`: part 11
- `prisms.py` (Speck32/64 checked against its test vector, double encryption,
  Even–Mansour, the attacks), `run_prisms.py`, `results_prisms.csv`: part 12
- `knots.py` (the four versions of SHA-256, the circuit-to-SAT encoder with
  native XOR or clauses, the forked hard time limit, Gaussian elimination for
  salt, numpy brute force), `run_knots.py`, `analyze_knots.py`,
  `results_knots.csv`, `summary_knots.json`, `knots_log.txt`: part 13 (needs
  pycryptosat and python-sat)
- `crossings.py` (the lifted elimination eye with front, back and split views;
  the round-by-round evaluator with rotations on or off), `run_crossings.py`,
  `analyze_crossings.py`, `results_crossings.csv`, `results_blind.csv`,
  `summary_crossings.json`, `crossings_log.txt`: part 14 (uses `knots.py`)
- `heat.py`: heat / annealing (uses numba if installed)
- `run.py`: part 1 (`python run.py`; needs numpy)
- `tune_heat.py`: picks the schedules on separate tuning instances
- `run_heat.py`: part 2 (`python run_heat.py`; numba strongly recommended)
- `results.csv`, `summary.json`: part 1, one row per instance and medians
- `results_heat.csv`, `summary_heat.json`: part 2
