import PvsNP.Orientations

/-!
# The observer's resolution

An observer with step size `δ` sees each piece only as a whole number of steps,
`a / δ` (the *coarse* piece). The rest, `a % δ`, is below its resolution (the
*fine* part). This file proves exactly what such an observer can and cannot
tell about the void wall.

* `signedSum_split` — every orientation's total is `δ · (coarse total) + (fine total)`.
* `fine_sum_le` — the invisible part is at most `n · (δ − 1)` for `n` pieces.
* **The blur zone.**
  - `exact_seen_near`: if the pieces can be balanced exactly, the observer sees
    a coarse orientation within the blur, `δ · |coarse total| ≤ Σ fine`;
  - `near_seen_close`: if it sees one within the blur, the real gap is at most
    `2 · Σ fine ≤ 2n(δ − 1)`.
  So the observer separates "on the wall" from "further than `2n(δ − 1)`", and
  anything in between is invisible to it: a wire that small can sit on either
  side of the wall without the observer being able to tell.
* `rounding_gap` — an orientation that is best for the coarse pieces is within
  `2 · Σ fine` of *any* orientation of the real pieces, in particular within
  `2n(δ − 1)` of the floor.
* `coarse_grid_length` — the observer's grid of reachable totals has at most
  `total / δ + 1` cells.

Together: with `δ ≈ h · total / (2n)` the observer gets within `h · total` of
the floor, and its grid has about `2n / h` cells. That is linear in `1 / h`, so
each halving of the resolution doubles the work (the approximation scheme for
subset sum, Ibarra–Kim 1975). Seeing the floor itself needs `δ = 1`, which means
a grid as wide as the whole total.
-/

namespace PvsNP.Resolution

open PvsNP.Orientations

/-- What an observer with step `δ` sees of each piece: its whole steps. -/
def coarse (δ : Nat) (as : List Nat) : List Nat := as.map (· / δ)

/-- What the observer cannot see: the part of each piece below one step. -/
def fine (δ : Nat) (as : List Nat) : List Nat := as.map (· % δ)

/-- Every orientation's total splits into the seen part and the unseen part. -/
theorem signedSum_split (δ : Nat) : ∀ (as : List Nat) (s : List Bool),
    signedSum as s = (δ : Int) * signedSum (coarse δ as) s + signedSum (fine δ as) s
  | [], s => by simp [signedSum, coarse, fine]
  | a :: as, [] => by simp [signedSum, coarse, fine]
  | a :: as, b :: s => by
    have ih := signedSum_split δ as s
    have hd : (a : Int) = (δ : Int) * ((a / δ : Nat) : Int) + ((a % δ : Nat) : Int) := by
      have := Nat.div_add_mod a δ
      exact_mod_cast this.symm
    simp only [coarse, fine, List.map_cons, signedSum] at ih ⊢
    rw [ih, Int.mul_add]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hd, Int.mul_neg]
      omega
    · simp only [↓reduceIte]
      rw [hd]
      omega

/-- The unseen part is at most `δ − 1` per piece. -/
theorem fine_sum_le (δ : Nat) (hδ : 0 < δ) : ∀ as : List Nat,
    (fine δ as).sum ≤ as.length * (δ - 1)
  | [] => by simp [fine]
  | a :: as => by
    have ih := fine_sum_le δ hδ as
    have hm : a % δ < δ := Nat.mod_lt a hδ
    simp only [fine, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega

/-- The coarse pieces, scaled back up by `δ`, never exceed the real total. -/
theorem coarse_sum_mul_le (δ : Nat) : ∀ as : List Nat, (coarse δ as).sum * δ ≤ as.sum
  | [] => by simp [coarse]
  | a :: as => by
    have ih := coarse_sum_mul_le δ as
    have h := Nat.div_mul_le_self a δ
    simp only [coarse, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.add_mul]
    omega

/-- **The observer's grid is small.** It has at most `total / δ + 1` cells. -/
theorem coarse_grid_length (δ : Nat) (hδ : 0 < δ) (as : List Nat) :
    (table (coarse δ as)).length ≤ as.sum / δ + 1 := by
  rw [table_length]
  have h := coarse_sum_mul_le δ as
  have : (coarse δ as).sum ≤ as.sum / δ := (Nat.le_div_iff_mul_le hδ).2 h
  omega

/-- Size of a total, as a natural number. -/
abbrev gap (as : List Nat) (s : List Bool) : Nat := (signedSum as s).natAbs

theorem fine_bound (δ : Nat) (as : List Nat) (s : List Bool) :
    -(((fine δ as).sum : Nat) : Int) ≤ signedSum (fine δ as) s ∧
      signedSum (fine δ as) s ≤ (((fine δ as).sum : Nat) : Int) :=
  signedSum_bound (fine δ as) s

/-- **Exact balance is seen inside the blur.** -/
theorem exact_seen_near (δ : Nat) (as : List Nat) (s : List Bool) (h : signedSum as s = 0) :
    δ * gap (coarse δ as) s ≤ (fine δ as).sum := by
  have hs := signedSum_split δ as s
  have hb := fine_bound δ as s
  have hm : ((δ * gap (coarse δ as) s : Nat) : Int) =
      ((((δ : Int) * signedSum (coarse δ as) s).natAbs : Nat) : Int) := by
    rw [Int.natAbs_mul]; simp [gap]
  have : ((δ : Int) * signedSum (coarse δ as) s).natAbs ≤ (fine δ as).sum := by omega
  omega

/-- **Inside the blur means close.** If the observer sees an orientation within
its blur, the real gap of that orientation is at most twice the unseen part. -/
theorem near_seen_close (δ : Nat) (as : List Nat) (s : List Bool)
    (h : δ * gap (coarse δ as) s ≤ (fine δ as).sum) :
    gap as s ≤ 2 * (fine δ as).sum := by
  have hs := signedSum_split δ as s
  have hb := fine_bound δ as s
  have hm : δ * gap (coarse δ as) s = ((δ : Int) * signedSum (coarse δ as) s).natAbs := by
    rw [Int.natAbs_mul]; simp [gap]
  rw [hm] at h
  simp only [gap]
  omega

/-- **Rounding costs at most twice the unseen part.** An orientation that is best
for the coarse pieces is within `2 · Σ fine` of any orientation of the real
pieces. -/
theorem rounding_gap (δ : Nat) (as : List Nat) (s t : List Bool)
    (hbest : gap (coarse δ as) s ≤ gap (coarse δ as) t) :
    gap as s ≤ gap as t + 2 * (fine δ as).sum := by
  have hs := signedSum_split δ as s
  have ht := signedSum_split δ as t
  have bs := fine_bound δ as s
  have bt := fine_bound δ as t
  have hmul : ((δ : Int) * signedSum (coarse δ as) s).natAbs ≤
      ((δ : Int) * signedSum (coarse δ as) t).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ hbest
  simp only [gap]
  omega

/-- With `n` pieces, rounding costs at most `2n(δ − 1)`. -/
theorem rounding_gap_le (δ : Nat) (hδ : 0 < δ) (as : List Nat) (s t : List Bool)
    (hbest : gap (coarse δ as) s ≤ gap (coarse δ as) t) :
    gap as s ≤ gap as t + 2 * (as.length * (δ - 1)) := by
  have h1 := rounding_gap δ as s t hbest
  have h2 := fine_sum_le δ hδ as
  omega

/-- The finest observer, `δ = 1`, sees everything: nothing is unseen. -/
theorem fine_one (as : List Nat) : (fine 1 as).sum = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [fine] at ih ⊢; exact ⟨Nat.mod_one a, ih⟩

/-! ## Example (checked by the kernel)

Pieces `37, 22, 15, 9`: the total is 83, and the real floor is 9
(for example `37 − 22 − 15 − 9 = −9`). An observer with step 8 sees the coarse
pieces `4, 2, 1, 1` and misses `5, 6, 7, 1` (19 in all). To it, `4 − 2 − 1 − 1 = 0`:
the wire looks like it is on the wall. The real gap of that orientation is 9,
inside the bound `2 · 19 = 38` from `near_seen_close`. -/

example : coarse 8 [37, 22, 15, 9] = [4, 2, 1, 1] := by decide
example : (fine 8 [37, 22, 15, 9]).sum = 19 := by decide
example : gap (coarse 8 [37, 22, 15, 9]) [true, false, false, false] = 0 := by decide
example : gap [37, 22, 15, 9] [true, false, false, false] = 9 := by decide
example : (table (coarse 8 [37, 22, 15, 9])).length = 9 := by decide

end PvsNP.Resolution
