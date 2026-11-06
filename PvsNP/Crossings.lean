/-!
# Signed crossings telescope

Recovered from `structural-reasoning/theory/folding/FOLDING_CONTINUITY.md`.
We model a finite sequence of observations on two sides of a boundary.
Every side change contributes +1 or -1. No geometric continuity hypothesis
is needed for this discrete identity. The identity alone does not establish
physical conservation, a closed geometric loop, or validity of a detector.
-/

namespace PvsNP.Crossings

def sideValue (side : Bool) : Int := if side then 1 else 0

/-- Signed crossing count, starting on `start` and visiting `rest` in order. -/
def netFrom : Bool → List Bool → Int
  | _, [] => 0
  | start, next :: rest => sideValue next - sideValue start + netFrom next rest

def finalSide : Bool → List Bool → Bool
  | start, [] => start
  | _, next :: rest => finalSide next rest

/-- All intermediate side values cancel. -/
theorem net_eq_end_sub_start (start : Bool) (rest : List Bool) :
    netFrom start rest = sideValue (finalSide start rest) - sideValue start := by
  induction rest generalizing start with
  | nil => simp [netFrom, finalSide]
  | cons next rest ih =>
    simp only [netFrom, finalSide, ih]
    omega

/-- The net signed count is always -1, 0, or +1. -/
theorem net_three_values (start : Bool) (rest : List Bool) :
    netFrom start rest = -1 ∨ netFrom start rest = 0 ∨ netFrom start rest = 1 := by
  rw [net_eq_end_sub_start]
  cases h : finalSide start rest <;> cases start <;> simp [sideValue]

theorem net_bound (start : Bool) (rest : List Bool) :
    -1 ≤ netFrom start rest ∧ netFrom start rest ≤ 1 := by
  obtain h | h | h := net_three_values start rest <;> rw [h] <;> decide

/-- Returning to the same side makes the net zero. -/
theorem net_zero_of_same_side {start : Bool} {rest : List Bool}
    (h : finalSide start rest = start) : netFrom start rest = 0 := by
  rw [net_eq_end_sub_start, h]
  omega

/-- Zero net means the endpoints share a side, not necessarily a position. -/
theorem net_zero_iff_same_side (start : Bool) (rest : List Bool) :
    netFrom start rest = 0 ↔ finalSide start rest = start := by
  rw [net_eq_end_sub_start]
  cases h : finalSide start rest <;> cases start <;> simp [sideValue]

/-- Many crossings can coexist with zero net. -/
example : netFrom false [true, false, true, false] = 0 := by decide

end PvsNP.Crossings

