import PvsNPM

/-! Run `lake env lean Audit.lean` inside `mathlib/`. Every headline theorem
should depend only on Lean's standard axioms (propext, Classical.choice,
Quot.sound) — no `sorryAx`, no custom axioms. -/

#print axioms PvsNP.Void.absorption_nonneg
#print axioms PvsNP.Void.mass_eq_permanent
#print axioms PvsNP.Void.absorbed_eq
#print axioms PvsNP.Void.absorbed_eq_of_nonneg
#print axioms PvsNP.Void.card_upright_eq_card_flipped
#print axioms PvsNP.Void.two_mul_card_upright
#print axioms PvsNP.Void.absorbed_ones
#print axioms PvsNP.Void.absorbed_one
#print axioms PvsNP.Void.permanent_absorbs_nothing
#print axioms PvsNP.Void.absorbed_rotating
