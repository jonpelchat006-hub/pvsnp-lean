/-!
# Closure-unit arithmetic

Source: structural-reasoning/theory/folding/FOLDING_CLOSURE_UNIT.md.
For natural k, the equation x*x = x+k has a natural root exactly when
k is pronic (a product of consecutive naturals). Its discriminant 1+4*k
is then an odd square. This entry concerns natural numbers; a separate
rational-root argument is needed to conclude irrationality of other roots.
No empirical folding or self-reference interpretation is assumed.
-/

namespace PvsNP.ClosureUnit

def Pronic (k : Nat) : Prop := ∃ m, k = m * (m + 1)

theorem successor_root (m : Nat) :
    (m + 1) * (m + 1) = (m + 1) + m * (m + 1) := by
  simp [Nat.add_mul, Nat.mul_add]
  omega

theorem natural_root_iff_pronic (k : Nat) :
    (∃ x : Nat, x * x = x + k) ↔ Pronic k := by
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | zero => exact ⟨0, by simpa using hx.symm⟩
    | succ m =>
      refine ⟨m, ?_⟩
      have hm := successor_root m
      omega
  · rintro ⟨m, rfl⟩
    exact ⟨m + 1, successor_root m⟩

theorem discriminant_identity (m : Nat) :
    (2 * m + 1) * (2 * m + 1) = 1 + 4 * (m * (m + 1)) := by
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem square_discriminant_of_pronic {k : Nat} (hk : Pronic k) :
    ∃ r : Nat, r * r = 1 + 4 * k := by
  obtain ⟨m, rfl⟩ := hk
  exact ⟨2 * m + 1, discriminant_identity m⟩

theorem pronic_of_square_discriminant {k r : Nat} (h : r * r = 1 + 4 * k) :
    Pronic k := by
  have hodd : r % 2 = 1 := by
    have hp := congrArg (fun n => n % 2) h
    rw [Nat.mul_mod] at hp
    have hr := Nat.mod_lt r (by decide : 0 < 2)
    by_cases hz : r % 2 = 0
    · simp [hz, Nat.add_mod, Nat.mul_mod] at hp
    · omega
  have hr : r = 2 * (r / 2) + 1 := by omega
  have hd := discriminant_identity (r / 2)
  rw [← hr] at hd
  exact ⟨r / 2, by omega⟩

theorem square_discriminant_iff_pronic (k : Nat) :
    (∃ r : Nat, r * r = 1 + 4 * k) ↔ Pronic k :=
  ⟨fun ⟨_, h⟩ => pronic_of_square_discriminant h, square_discriminant_of_pronic⟩

theorem one_not_pronic : ¬ Pronic 1 := by
  rintro ⟨m, hm⟩
  cases m with
  | zero => simp at hm
  | succ n =>
    have hb : 2 ≤ (n + 1) * (n + 1 + 1) :=
      Nat.le_trans (by decide : 2 ≤ 1 * 2)
        (Nat.mul_le_mul (by omega) (by omega))
    omega

theorem unit_one_no_natural_root : ¬ ∃ x : Nat, x * x = x + 1 :=
  fun h => one_not_pronic ((natural_root_iff_pronic 1).1 h)

theorem zero_pronic : Pronic 0 := ⟨0, rfl⟩
theorem two_pronic : Pronic 2 := ⟨1, rfl⟩
theorem six_pronic : Pronic 6 := ⟨2, rfl⟩

end PvsNP.ClosureUnit
