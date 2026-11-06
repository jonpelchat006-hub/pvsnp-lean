/-!
# Polynomial bounds on ℕ

Every polynomial bound in this library has the single shape `(n + c) ^ k`.
That shape is always monotone in `n`, which is exactly what makes bounds
compose: if `g n ≤ (n + c₂)^k₂` and `f m ≤ (m + c₁)^k₁`, then
`f (g n)` is bounded by another expression of the same shape.

Core Lean only — no Mathlib — so the file builds in seconds anywhere.
-/

namespace PvsNP

/-- The canonical polynomial shape used throughout: `(n + c) ^ k`. -/
def poly (c k n : Nat) : Nat := (n + c) ^ k

/-- `f` is bounded by some polynomial. -/
def PolyBound (f : Nat → Nat) : Prop := ∃ c k, ∀ n, f n ≤ poly c k n

theorem poly_mono {c k m n : Nat} (h : m ≤ n) : poly c k m ≤ poly c k n :=
  Nat.pow_le_pow_left (Nat.add_le_add_right h c) k

theorem poly_mono_c {c c' k n : Nat} (h : c ≤ c') : poly c k n ≤ poly c' k n :=
  Nat.pow_le_pow_left (Nat.add_le_add_left h n) k

/-- Raising the base to a bigger exponent never hurts once the base is ≥ 1. -/
theorem poly_mono_k {c k k' n : Nat} (hb : 1 ≤ n + c) (h : k ≤ k') :
    poly c k n ≤ poly c k' n :=
  Nat.pow_le_pow_right hb h

/-- The key composition lemma: a polynomial of a polynomial is a polynomial,
with explicit constants. -/
theorem poly_comp_le (c₁ k₁ c₂ k₂ n : Nat) :
    poly c₁ k₁ (poly c₂ k₂ n) ≤ poly (c₁ + c₂ + 2) ((k₂ + 2) * k₁) n := by
  unfold poly
  -- M is the common base, and M ≥ 2.
  have hM : 2 ≤ n + (c₁ + c₂ + 2) := by omega
  have hM1 : 0 < n + (c₁ + c₂ + 2) := by omega
  -- the inner polynomial is at most M^(k₂+1)
  have hA : (n + c₂) ^ k₂ ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 1) :=
    calc (n + c₂) ^ k₂ ≤ (n + (c₁ + c₂ + 2)) ^ k₂ := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 1) := Nat.pow_le_pow_right hM1 (by omega)
  -- the additive constant is also at most M^(k₂+1)
  have hc : c₁ ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 1) :=
    calc c₁ ≤ (n + (c₁ + c₂ + 2)) ^ 1 := by rw [Nat.pow_one]; omega
      _ ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 1) := Nat.pow_le_pow_right hM1 (by omega)
  -- so the sum is at most 2·M^(k₂+1) ≤ M^(k₂+2)
  have hsum : (n + c₂) ^ k₂ + c₁ ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 2) := by
    have h2 : 2 * (n + (c₁ + c₂ + 2)) ^ (k₂ + 1)
        ≤ (n + (c₁ + c₂ + 2)) ^ (k₂ + 1) * (n + (c₁ + c₂ + 2)) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hM
    rw [show k₂ + 2 = (k₂ + 1) + 1 from rfl, Nat.pow_succ]
    omega
  calc ((n + c₂) ^ k₂ + c₁) ^ k₁
      ≤ ((n + (c₁ + c₂ + 2)) ^ (k₂ + 2)) ^ k₁ := Nat.pow_le_pow_left hsum _
    _ = (n + (c₁ + c₂ + 2)) ^ ((k₂ + 2) * k₁) := (Nat.pow_mul _ _ _).symm

namespace PolyBound

variable {f g : Nat → Nat}

theorem const (a : Nat) : PolyBound (fun _ => a) :=
  ⟨a, 1, fun n => by show a ≤ (n + a) ^ 1; rw [Nat.pow_one]; omega⟩

theorem id : PolyBound (fun n => n) :=
  ⟨0, 1, fun n => by show n ≤ (n + 0) ^ 1; rw [Nat.pow_one]; omega⟩

theorem of_le (hg : PolyBound g) (h : ∀ n, f n ≤ g n) : PolyBound f := by
  obtain ⟨c, k, hk⟩ := hg
  exact ⟨c, k, fun n => Nat.le_trans (h n) (hk n)⟩

theorem add (hf : PolyBound f) (hg : PolyBound g) : PolyBound (fun n => f n + g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂ + 2, k₁ + k₂ + 1, fun n => ?_⟩
  show f n + g n ≤ poly (c₁ + c₂ + 2) (k₁ + k₂ + 1) n
  unfold poly at *
  have hM : 2 ≤ n + (c₁ + c₂ + 2) := by omega
  have hM1 : 0 < n + (c₁ + c₂ + 2) := by omega
  have a₁ : f n ≤ (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂) :=
    calc f n ≤ (n + c₁) ^ k₁ := h₁ n
      _ ≤ (n + (c₁ + c₂ + 2)) ^ k₁ := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂) := Nat.pow_le_pow_right hM1 (by omega)
  have a₂ : g n ≤ (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂) :=
    calc g n ≤ (n + c₂) ^ k₂ := h₂ n
      _ ≤ (n + (c₁ + c₂ + 2)) ^ k₂ := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂) := Nat.pow_le_pow_right hM1 (by omega)
  have h2 : 2 * (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂)
      ≤ (n + (c₁ + c₂ + 2)) ^ (k₁ + k₂) * (n + (c₁ + c₂ + 2)) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hM
  rw [Nat.pow_succ]
  omega

theorem mul (hf : PolyBound f) (hg : PolyBound g) : PolyBound (fun n => f n * g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, k₁ + k₂, fun n => ?_⟩
  unfold poly at *
  calc f n * g n ≤ (n + c₁) ^ k₁ * (n + c₂) ^ k₂ := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ ≤ (n + (c₁ + c₂)) ^ k₁ * (n + (c₁ + c₂)) ^ k₂ :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
    _ = (n + (c₁ + c₂)) ^ (k₁ + k₂) := (Nat.pow_add _ _ _).symm

/-- Polynomials are closed under composition. -/
theorem comp (hf : PolyBound f) (hg : PolyBound g) : PolyBound (fun n => f (g n)) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  exact ⟨c₁ + c₂ + 2, (k₂ + 2) * k₁, fun n =>
    Nat.le_trans (h₁ (g n)) (Nat.le_trans (poly_mono (h₂ n)) (poly_comp_le c₁ k₁ c₂ k₂ n))⟩

end PolyBound

end PvsNP
