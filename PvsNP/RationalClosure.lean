import Init.Data.Rat
import PvsNP.ClosureUnit

/-!
# Rational roots of the closure equation

Source: C:/Users/GamerTech/structural-reasoning/theory/folding/
FOLDING_CLOSURE_UNIT.md. This extends ClosureUnit's natural-number result
for x*x = x+k to rational roots. The parameter k is a natural number;
nonintegral parameters are outside this classification. The proof uses the
reduced denominator of standard exact Rat; no real square-root function or
real embedding is needed. No measured-fold or physical interpretation is assumed.
-/

namespace PvsNP.RationalClosure

/-- Adding an integer cannot increase a rational's reduced denominator. -/
theorem den_add_int_le (x : Rat) (k : Int) : (x + (k : Rat)).den ≤ x.den := by
  rw [Rat.den_add]
  simp only [Rat.den_intCast, Nat.mul_one]
  exact Nat.div_le_self _ _

/-- A rational root of this monic equation has denominator one. -/
theorem root_den_eq_one {x : Rat} {k : Int} (hx : x * x = x + (k : Rat)) :
    x.den = 1 := by
  have hpow : x * x = x ^ 2 := by simp [Rat.pow_succ, Rat.pow_zero]
  have hden := congrArg Rat.den hx
  rw [hpow, Rat.den_pow] at hden
  have hbound : x.den * x.den ≤ x.den := by
    have hb := den_add_int_le x k
    rw [← hden] at hb
    simpa [Nat.pow_succ, Nat.pow_zero] using hb
  have hpos := x.den_pos
  by_cases h : x.den ≤ 1
  · omega
  · have htwo : 2 ≤ x.den := by omega
    have hm := Nat.mul_le_mul_left x.den htwo
    omega

/-- A reduced denominator of one identifies the rational with its numerator. -/
theorem eq_int_of_den_eq_one {x : Rat} (hd : x.den = 1) :
    x = (x.num : Rat) := by
  have h := Rat.num_divInt_den x
  rw [hd] at h
  have h1 : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1)
  simpa [Rat.divInt_eq_div, Rat.div_def, h1, Rat.mul_one] using h.symm

/-- Every rational root is an integer, explicitly its reduced numerator. -/
theorem root_eq_int {x : Rat} {k : Int} (hx : x * x = x + (k : Rat)) :
    x = (x.num : Rat) :=
  eq_int_of_den_eq_one (root_den_eq_one hx)

/-- Integer roots, including negative roots, force a pronic natural parameter. -/
theorem pronic_of_int_root {z : Int} {k : Nat} (hz : z * z = z + (k : Int)) :
    PvsNP.ClosureUnit.Pronic k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have hn : n * n = n + k := by
      have hcast : ((n * n : Nat) : Int) = ((n + k : Nat) : Int) := by
        simpa only [Int.natCast_mul, Int.natCast_add] using hz
      exact Int.ofNat.inj hcast
    exact (PvsNP.ClosureUnit.natural_root_iff_pronic k).1 ⟨n, hn⟩
  · have hn : ((n * n : Nat) : Int) = -(n : Int) + (k : Int) := by
      simpa only [Int.neg_mul_neg, Int.natCast_mul] using hz
    refine ⟨n, ?_⟩
    have hk : k = n * n + n := by omega
    simpa [Nat.mul_add] using hk

/-- Rational roots exist exactly at the natural pronic parameters. -/
theorem rational_root_iff_pronic (k : Nat) :
    (∃ x : Rat, x * x = x + (k : Rat)) ↔ PvsNP.ClosureUnit.Pronic k := by
  constructor
  · rintro ⟨x, hx⟩
    have he := root_eq_int (k := (k : Int)) hx
    rw [he] at hx
    have hi : x.num * x.num = x.num + (k : Int) := by
      apply Rat.intCast_inj.mp
      simpa only [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_natCast] using hx
    exact pronic_of_int_root hi
  · intro hk
    obtain ⟨n, hn⟩ := (PvsNP.ClosureUnit.natural_root_iff_pronic k).2 hk
    refine ⟨(n : Rat), ?_⟩
    simpa only [Rat.natCast_mul, Rat.natCast_add] using congrArg (fun n : Nat => (n : Rat)) hn

/-- Allowing rational roots does not introduce any new natural parameters. -/
theorem rational_root_iff_natural_root (k : Nat) :
    (∃ x : Rat, x * x = x + (k : Rat)) ↔ (∃ n : Nat, n * n = n + k) :=
  (rational_root_iff_pronic k).trans (PvsNP.ClosureUnit.natural_root_iff_pronic k).symm

/-- A natural number has a rational square root exactly when it is a natural square. -/
theorem rational_square_iff_natural_square (n : Nat) :
    (∃ x : Rat, x * x = (n : Rat)) ↔ (∃ r : Nat, r * r = n) := by
  constructor
  · rintro ⟨x, hx⟩
    have hden : x.den * x.den = 1 := by
      have hd := congrArg Rat.den hx
      have hp : x * x = x ^ 2 := by simp [Rat.pow_succ, Rat.pow_zero]
      rw [hp, Rat.den_pow, Rat.den_natCast] at hd
      simpa [Nat.pow_succ, Nat.pow_zero] using hd
    have he := eq_int_of_den_eq_one (Nat.eq_one_of_mul_eq_one_right hden)
    rw [he] at hx
    have hi : x.num * x.num = (n : Int) := by
      apply Rat.intCast_inj.mp
      simpa only [Rat.intCast_mul, Rat.intCast_natCast] using hx
    have ha := congrArg Int.natAbs hi
    exact ⟨x.num.natAbs, by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using ha⟩
  · rintro ⟨r, hr⟩
    have hc := congrArg (fun r : Nat => (r : Rat)) hr
    exact ⟨(r : Rat), by simpa only [Rat.natCast_mul] using hc⟩

/-- The old discriminant claim holds even if its proposed square root is rational. -/
theorem rational_square_discriminant_iff_pronic (k : Nat) :
    (∃ r : Rat, r * r = ((1 + 4 * k : Nat) : Rat)) ↔
      PvsNP.ClosureUnit.Pronic k :=
  (rational_square_iff_natural_square (1 + 4 * k)).trans
    (PvsNP.ClosureUnit.square_discriminant_iff_pronic k)

/-- The unit-one equation has no rational solution. -/
theorem unit_one_no_rational_root : ¬ ∃ x : Rat, x * x = x + 1 := by
  intro h
  exact PvsNP.ClosureUnit.one_not_pronic ((rational_root_iff_pronic 1).1 h)

end PvsNP.RationalClosure
