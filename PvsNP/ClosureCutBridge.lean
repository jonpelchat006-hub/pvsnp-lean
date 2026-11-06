import PvsNP.RationalClosure
import PvsNP.CutFraction

/-!
# Closure parameters expressed by rational cut fractions

Combines the two independently proved parts of FOLDING_CLOSURE_UNIT.md:
the rational root classification and the invertible cut-fraction map.
Only natural parameters k are classified here. Rational parameters such as
k=1/2, real square-root existence, and measured protein cuts are separate.
-/

namespace PvsNP.ClosureCutBridge

open CutFraction ClosureUnit

/-- An exact rational cut realizes a natural closure parameter precisely
when that parameter is pronic. -/
theorem rational_cut_iff_pronic (k : Nat) :
    (∃ f : Rat, 0 < f ∧ f < 1 ∧
      f * (2 * f - 1) = (k : Rat) * (1 - f)^2) ↔ Pronic k := by
  constructor
  · rintro ⟨f, hf, h1, hk⟩
    apply (RationalClosure.rational_root_iff_pronic k).1
    refine ⟨ratio f, (closure_equation_in_fraction (ratio_pos hf h1)).2 ?_⟩
    simpa only [fraction_ratio hf h1] using hk
  · rintro ⟨m, hm⟩
    have hx : 0 < ((m + 1 : Nat) : Rat) := Rat.natCast_pos.2 (by omega)
    have hr : ((m + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat) =
        ((m + 1 : Nat) : Rat) + (k : Rat) := by
      have he := successor_root m
      rw [← hm] at he
      simpa only [Rat.natCast_mul, Rat.natCast_add] using
        congrArg (fun n : Nat => (n : Rat)) he
    exact ⟨fraction ((m + 1 : Nat) : Rat), fraction_pos hx, fraction_lt_one hx,
      (closure_equation_in_fraction hx).1 hr⟩

/-- The golden-cut polynomial has no rational root, even outside (0,1). -/
theorem no_rational_golden_cut : ¬ ∃ f : Rat, f * f + f = 1 := by
  rintro ⟨f, hf⟩
  apply RationalClosure.unit_one_no_rational_root
  exact ⟨-f, by grind⟩

/-- The rational midpoint realizes the zero closure parameter. -/
theorem midpoint_zero_parameter :
    (1/2 : Rat) * (2 * (1/2 : Rat) - 1) = 0 * (1 - (1/2 : Rat))^2 := by grind

end PvsNP.ClosureCutBridge
