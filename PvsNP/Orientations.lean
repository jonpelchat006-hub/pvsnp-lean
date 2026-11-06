/-!
# Orientations: reaching the void with a saw blade

Each piece has a size and can face one of two ways: upright (+) or flipped
(−). The question is whether the pieces can be oriented so that the total
lands exactly on the void, 0. This is the PARTITION problem, one of Karp's
original NP-complete problems (1972; cited, not proved here).

The file proves correct the four tools people actually use on it:

* **Checking** a proposed orientation is just a sum (`check_iff`).
* **Branching**: trying every orientation, `2ⁿ` branch tips for `n` pieces
  (`length_allChoices`, `balanced_iff_bruteForce`).
* **Mirror symmetry**: flipping every piece also lands on 0, so the first
  piece can be fixed upright (`balanced_cons_iff`).
* **Pruning**: a branch that has drifted further from 0 than the remaining
  pieces could ever bring back can be cut without losing any solution
  (`balanced_iff_search`).
* **Merging at intersections**: branches that land on the same running
  total share one cell of a grid, one cell per possible total, so the grid
  is exactly as wide as the total of the pieces plus one (`table_length`,
  `balanced_iff_grid`). Small pieces merge a lot
  (`merging_with_small_pieces`: `n + 1` cells for `2ⁿ` branches); for the
  pieces `1, 2, 4, …` the grid is as big as the whole tree, so merging saves
  nothing (`no_merging_with_powers`).
* **Meet in the middle**: split the pieces into two halves, list the totals
  each half can reach, and look for a total on one side that mirrors one on
  the other (`balanced_iff_meet`).

Lean checks correctness here, not running time: that needs a machine model.
The speed facts are standard and stated only in words. Brute force does
`2ⁿ` work. The grid does about (number of pieces) × (total) work, which is
small when the numbers are small and exponential in the input length when
they carry many digits. Meet in the middle lists about `2^(n/2)` totals per
side; its speed-up comes from sorting one side, which is not formalized
here (`meetInMiddle` below matches by plain search). No method is known that
beats roughly `2^(n/2)` in the worst case.
-/

namespace PvsNP.Orientations

/-! ## Orientations and the void -/

/-- The total when piece `i` faces the way `s[i]` says: `true` = upright (+),
`false` = flipped (−). -/
def signedSum : List Nat → List Bool → Int
  | a :: as, b :: bs => (if b then (a : Int) else -(a : Int)) + signedSum as bs
  | _, _ => 0

/-- **The problem.** The pieces can be oriented to land exactly on 0. -/
def Balanced (as : List Nat) : Prop :=
  ∃ s : List Bool, s.length = as.length ∧ signedSum as s = 0

/-- A total never goes further from 0 than the sum of all the pieces. -/
theorem signedSum_bound : ∀ (as : List Nat) (s : List Bool),
    -((as.sum : Nat) : Int) ≤ signedSum as s ∧ signedSum as s ≤ ((as.sum : Nat) : Int)
  | [], s => by simp [signedSum]
  | a :: as, [] => by simp [signedSum]; omega
  | a :: as, b :: s => by
    have ih := signedSum_bound as s
    cases b <;> simp [signedSum, List.sum_cons] <;> omega

/-! ## 1. Checking -/

/-- Checking a proposed orientation: right length, total is 0. -/
def check (as : List Nat) (s : List Bool) : Bool :=
  s.length == as.length && signedSum as s == 0

theorem check_iff (as : List Nat) (s : List Bool) :
    check as s = true ↔ s.length = as.length ∧ signedSum as s = 0 := by
  simp [check]

/-! ## 2. Branching: every orientation -/

/-- Every orientation of `n` pieces. -/
def allChoices : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allChoices n).flatMap fun s => [true :: s, false :: s]

theorem mem_allChoices : ∀ {n : Nat} {s : List Bool}, s ∈ allChoices n ↔ s.length = n
  | 0, s => by cases s <;> simp [allChoices]
  | n + 1, s => by
    simp only [allChoices, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨s', hs', h | h⟩ <;> subst h <;> simp [mem_allChoices.1 hs']
    · intro h
      cases s with
      | nil => simp at h
      | cons b s' =>
        refine ⟨s', mem_allChoices.2 (by simpa using h), ?_⟩
        cases b <;> simp

theorem length_flatMap_two (l : List (List Bool)) :
    (l.flatMap fun s => [true :: s, false :: s]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega

/-- Each piece doubles the branches: `n` pieces give `2ⁿ` branch tips. -/
theorem length_allChoices (n : Nat) : (allChoices n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allChoices, length_flatMap_two, ih, Nat.pow_succ, Nat.mul_comm]

/-- Brute force: try every branch. -/
def bruteForce (as : List Nat) : Bool :=
  (allChoices as.length).any (check as)

theorem balanced_iff_bruteForce (as : List Nat) : Balanced as ↔ bruteForce as = true := by
  simp only [bruteForce, List.any_eq_true, check_iff, mem_allChoices, Balanced]
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, hs, h⟩
  · rintro ⟨s, hs, _, h⟩; exact ⟨s, hs, h⟩

/-! ## 3. Mirror symmetry: half the blade -/

/-- Flipping every piece mirrors the total through 0. -/
theorem signedSum_mirror : ∀ (as : List Nat) (s : List Bool),
    signedSum as (s.map not) = -signedSum as s
  | [], s => by simp [signedSum]
  | a :: as, [] => by simp [signedSum]
  | a :: as, b :: s => by
    have ih := signedSum_mirror as s
    cases b <;> simp [signedSum, ih] <;> omega

/-- So the first piece can always be taken upright: only half the branches
need searching. -/
theorem balanced_cons_iff (a : Nat) (as : List Nat) :
    Balanced (a :: as) ↔
      ∃ s : List Bool, s.length = as.length ∧ signedSum (a :: as) (true :: s) = 0 := by
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | nil => simp at hs
    | cons b s =>
      cases b
      · refine ⟨s.map not, by simpa using hs, ?_⟩
        have hm := signedSum_mirror (a :: as) (false :: s)
        simp only [List.map_cons, Bool.not_false] at hm
        rw [hm]; omega
      · exact ⟨s, by simpa using hs, h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨true :: s, by simp [hs], h⟩

/-! ## 4. Pruning: hiding branches that cannot come back -/

/-- Depth-first search from running total `t`. A branch is cut as soon as it
is further from 0 than all the remaining pieces together. -/
def search : Int → List Nat → Bool
  | t, [] => t == 0
  | t, a :: as =>
    if ((as.sum + a : Nat) : Int) < t ∨ ((as.sum + a : Nat) : Int) < -t then false
    else search (t + a) as || search (t - a) as

/-- **Pruning never loses a solution.** -/
theorem search_iff : ∀ (t : Int) (as : List Nat),
    search t as = true ↔ ∃ s : List Bool, s.length = as.length ∧ t + signedSum as s = 0
  | t, [] => by
    constructor
    · intro h
      exact ⟨[], rfl, by simpa [search, signedSum] using h⟩
    · rintro ⟨s, _, h⟩
      simpa [search, signedSum] using h
  | t, a :: as => by
    have ih₁ := search_iff (t + a) as
    have ih₂ := search_iff (t - a) as
    unfold search
    split
    · rename_i hp
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro s hs h
      cases s with
      | nil => simp at hs
      | cons b s =>
        have hb := signedSum_bound as s
        cases b <;> simp [signedSum] at h <;> omega
    · rw [Bool.or_eq_true, ih₁, ih₂]
      constructor
      · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
        · exact ⟨true :: s, by simp [hs], by simp [signedSum] <;> omega⟩
        · exact ⟨false :: s, by simp [hs], by simp [signedSum] <;> omega⟩
      · rintro ⟨s, hs, h⟩
        cases s with
        | nil => simp at hs
        | cons b s =>
          cases b
          · exact Or.inr ⟨s, by simpa using hs, by simp [signedSum] at h <;> omega⟩
          · exact Or.inl ⟨s, by simpa using hs, by simp [signedSum] at h <;> omega⟩

theorem balanced_iff_search (as : List Nat) : Balanced as ↔ search 0 as = true := by
  rw [search_iff]
  simp [Balanced]

/-! ## 5. Merging at intersections: the grid of reachable totals -/

/-- The total of the pieces picked by `s` (`true` = picked). -/
def pickSum : List Nat → List Bool → Nat
  | a :: as, b :: bs => (if b then a else 0) + pickSum as bs
  | _, _ => 0

theorem pickSum_le : ∀ (as : List Nat) (s : List Bool), pickSum as s ≤ as.sum
  | [], s => by simp [pickSum]
  | a :: as, [] => by simp [pickSum]
  | a :: as, b :: s => by
    have ih := pickSum_le as s
    cases b <;> simp [pickSum, List.sum_cons] <;> omega

/-- Upright pieces minus flipped pieces = twice the upright ones minus the
total. -/
theorem signedSum_eq_pickSum : ∀ (as : List Nat) (s : List Bool), s.length = as.length →
    signedSum as s = 2 * (pickSum as s : Int) - (as.sum : Int)
  | [], [], _ => by simp [signedSum, pickSum]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: s, h => by
    have ih := signedSum_eq_pickSum as s (by simpa using h)
    cases b <;> simp [signedSum, pickSum, List.sum_cons, ih] <;> omega

/-- The grid. Cell `t` is lit when some choice of pieces totals `t`. Every
branch that reaches the same total lands in the same cell, so the grid has
exactly one cell per possible total. -/
def table : List Nat → List Bool
  | [] => [true]
  | a :: as =>
    (List.range (as.sum + a + 1)).map fun t =>
      (table as).getD t false || (decide (a ≤ t) && (table as).getD (t - a) false)

/-- **The grid is as wide as the total of the pieces, plus one.** -/
theorem table_length : ∀ as : List Nat, (table as).length = as.sum + 1
  | [] => rfl
  | a :: as => by simp [table, List.sum_cons]; omega

theorem table_spec : ∀ (as : List Nat) (t : Nat),
    (table as).getD t false = true ↔ ∃ s : List Bool, s.length = as.length ∧ pickSum as s = t
  | [], t => by
    constructor
    · intro h
      cases t with
      | zero => exact ⟨[], rfl, rfl⟩
      | succ t => simp [table] at h
    · rintro ⟨s, hs, h⟩
      cases s with
      | nil => subst h; rfl
      | cons _ _ => simp at hs
  | a :: as, t => by
    have ih₁ := table_spec as t
    have ih₂ := table_spec as (t - a)
    by_cases ht : t < as.sum + a + 1
    · simp only [table, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
        Option.map_some, Option.getD_some]
      rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_iff, ih₁, ih₂]
      constructor
      · rintro (⟨s, hs, h⟩ | ⟨hat, s, hs, h⟩)
        · exact ⟨false :: s, by simp [hs], by simp [pickSum, h]⟩
        · exact ⟨true :: s, by simp [hs], by simp [pickSum]; omega⟩
      · rintro ⟨s, hs, h⟩
        cases s with
        | nil => simp at hs
        | cons b s =>
          cases b
          · exact Or.inl ⟨s, by simpa using hs, by simpa [pickSum] using h⟩
          · refine Or.inr ⟨?_, s, by simpa using hs, ?_⟩ <;> simp [pickSum] at h <;> omega
    · constructor
      · intro h
        have hlen := table_length (a :: as)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [List.sum_cons] at hlen ⊢; omega)] at h
        simp at h
      · rintro ⟨s, hs, h⟩
        have := pickSum_le (a :: as) s
        simp [List.sum_cons] at this
        omega

/-- Decide the problem from the grid: the total must be even and its half
must be a lit cell. -/
def gridDecide (as : List Nat) : Bool :=
  as.sum % 2 == 0 && (table as).getD (as.sum / 2) false

theorem balanced_iff_grid (as : List Nat) : Balanced as ↔ gridDecide as = true := by
  simp only [gridDecide, Bool.and_eq_true, beq_iff_eq, table_spec]
  constructor
  · rintro ⟨s, hs, h⟩
    have he := signedSum_eq_pickSum as s hs
    refine ⟨by omega, s, hs, by omega⟩
  · rintro ⟨heven, s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [signedSum_eq_pickSum as s hs]
    omega

instance (as : List Nat) : Decidable (Balanced as) :=
  decidable_of_iff _ (balanced_iff_grid as).symm

/-- **Small pieces merge a lot.** `n` pieces of size 1: `2ⁿ` branches, but
only `n + 1` cells. -/
theorem merging_with_small_pieces (n : Nat) :
    (allChoices n).length = 2 ^ n ∧ (table (List.replicate n 1)).length = n + 1 := by
  refine ⟨length_allChoices n, ?_⟩
  rw [table_length]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.sum_cons] at ih ⊢; omega

/-- The pieces `1, 2, 4, …, 2ⁿ⁻¹`. -/
def powers (n : Nat) : List Nat := (List.range n).map (2 ^ ·)

theorem sum_powers (n : Nat) : (powers n).sum + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powers, List.range_succ, List.map_append, List.sum_append] at ih ⊢
    simp [Nat.pow_succ]
    omega

/-- **When merging saves nothing.** For the pieces `1, 2, 4, …` the grid has
exactly as many cells as the tree has branch tips. -/
theorem no_merging_with_powers (n : Nat) :
    (table (powers n)).length = (allChoices (powers n).length).length := by
  rw [table_length, sum_powers, length_allChoices, powers, List.length_map, List.length_range]

/-! ## 6. Meet in the middle -/

theorem signedSum_append : ∀ (L R : List Nat) (sL sR : List Bool), sL.length = L.length →
    signedSum (L ++ R) (sL ++ sR) = signedSum L sL + signedSum R sR
  | [], R, [], sR, _ => by simp [signedSum]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | a :: L, R, b :: sL, sR, h => by
    have ih := signedSum_append L R sL sR (by simpa using h)
    simp only [List.cons_append, signedSum, ih]
    omega

/-- Every total one half of the pieces can reach. -/
def totals (L : List Nat) : List Int :=
  (allChoices L.length).map (signedSum L)

theorem length_totals (L : List Nat) : (totals L).length = 2 ^ L.length := by
  simp [totals, length_allChoices]

theorem mem_totals (L : List Nat) (x : Int) :
    x ∈ totals L ↔ ∃ s : List Bool, s.length = L.length ∧ signedSum L s = x := by
  simp [totals, mem_allChoices]

/-- Match a total on the left with its mirror image on the right. (A fast
implementation sorts one side first; this one searches plainly.) -/
def meetInMiddle (L R : List Nat) : Bool :=
  (totals L).any fun x => (totals R).contains (-x)

/-- **Meet in the middle is correct**: the whole set lands on 0 exactly when
some left total is mirrored by some right total. -/
theorem balanced_iff_meet (L R : List Nat) : Balanced (L ++ R) ↔ meetInMiddle L R = true := by
  simp only [meetInMiddle, List.any_eq_true, List.contains_iff_mem, mem_totals]
  constructor
  · rintro ⟨s, hs, h⟩
    have hsplit := List.take_append_drop L.length s
    have hL : (s.take L.length).length = L.length := by
      simp [List.length_take]; simp at hs; omega
    have hR : (s.drop L.length).length = R.length := by
      simp [List.length_drop]; simp at hs; omega
    rw [← hsplit, signedSum_append L R _ _ hL] at h
    exact ⟨signedSum L (s.take L.length), ⟨_, hL, rfl⟩, _, hR, by omega⟩
  · rintro ⟨x, ⟨sL, hL, rfl⟩, sR, hR, h⟩
    refine ⟨sL ++ sR, by simp [hL, hR], ?_⟩
    rw [signedSum_append L R _ _ hL]
    omega

/-! ## Examples (checked by the kernel, no `native_decide`) -/

/-- `3 − 1 − 1 − 2 + 2 − 1 = 0`. -/
example : check [3, 1, 1, 2, 2, 1] [true, false, false, false, true, false] = true := by decide

example : Balanced [3, 1, 1, 2, 2, 1] := by decide

/-- `2, 3, 7`: total 12, but no choice of pieces makes 6. -/
example : ¬ Balanced [2, 3, 7] := by decide

example : bruteForce [3, 1, 1, 2, 2, 1] = true := by decide
example : search 0 [3, 1, 1, 2, 2, 1] = true := by decide
example : meetInMiddle [3, 1, 1] [2, 2, 1] = true := by decide

end PvsNP.Orientations
