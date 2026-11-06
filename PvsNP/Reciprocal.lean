import Init.Data.Rat

/-!
# Reciprocal domains over exact rational numbers

Recovered from the partials/multiples picture in the chat "Conceptual Framework
Assessment". This core-only entry establishes the rational case. Real numbers,
logarithms, physical interpretations, and stability claims are not formalized.
The positive-domain restriction matters: totalized inverse also fixes zero.
-/

namespace PvsNP.Reciprocal

def Partial (x : Rat) : Prop := 0 < x ∧ x < 1
def Multiple (x : Rat) : Prop := 1 < x

theorem reciprocal_involution (x : Rat) : x⁻¹⁻¹ = x := Rat.inv_inv x

theorem inv_gt_one_iff {x : Rat} (hx : 0 < x) : 1 < x⁻¹ ↔ x < 1 := by
  have h := Rat.lt_div_iff (a := 1) (b := 1) hx
  simpa [Rat.div_def] using h

theorem inv_lt_one_iff {x : Rat} (hx : 0 < x) : x⁻¹ < 1 ↔ 1 < x := by
  have h := Rat.div_lt_iff (a := 1) (c := 1) hx
  simpa [Rat.div_def] using h

theorem partial_to_multiple {x : Rat} (hx : Partial x) : Multiple x⁻¹ :=
  (inv_gt_one_iff hx.1).2 hx.2

theorem multiple_to_partial {x : Rat} (hx : Multiple x) : Partial x⁻¹ := by
  have hp : 0 < x := by
    unfold Multiple at hx
    rw [Rat.lt_iff] at hx ⊢
    simp at hx ⊢
    omega
  exact ⟨Rat.inv_pos.2 hp, (inv_lt_one_iff hp).2 hx⟩

theorem partial_iff_inverse_multiple {x : Rat} (hx : 0 < x) :
    Partial x ↔ Multiple x⁻¹ :=
  ⟨partial_to_multiple, fun h => ⟨hx, (inv_gt_one_iff hx).1 h⟩⟩

theorem inverse_partial_iff_multiple {x : Rat} (hx : 0 < x) :
    Partial x⁻¹ ↔ Multiple x :=
  ⟨fun h => (inv_lt_one_iff hx).1 h.2, multiple_to_partial⟩

/-- The positive rationals split into the two domains and their boundary. -/
theorem positive_partition {x : Rat} (hx : 0 < x) :
    Partial x ∨ x = 1 ∨ Multiple x := by
  obtain h | h := Rat.le_total (a := x) (b := 1)
  · obtain h | h := Rat.le_iff_lt_or_eq.1 h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (Or.inl h)
  · obtain h | h := Rat.le_iff_lt_or_eq.1 h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h.symm)

/-- One is the unique positive rational fixed point of reciprocal. -/
theorem positive_fixed_point {x : Rat} (hx : 0 < x) : x⁻¹ = x ↔ x = 1 := by
  constructor
  · intro hfix
    obtain hp | he | hm := positive_partition hx
    · have hgt := partial_to_multiple hp
      change 1 < x⁻¹ at hgt
      rw [hfix] at hgt
      exact False.elim ((Rat.not_le.mpr hgt) (Rat.le_of_lt hp.2))
    · exact he
    · have hlt := (multiple_to_partial hm).2
      rw [hfix] at hlt
      exact False.elim ((Rat.not_le.mpr hm) (Rat.le_of_lt hlt))
  · intro h
    subst x
    exact Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1)

/-- Zero is also fixed by Lean's totalized inverse, outside the positive domain. -/
theorem zero_fixed_point : (0 : Rat)⁻¹ = 0 := Rat.inv_zero

end PvsNP.Reciprocal
