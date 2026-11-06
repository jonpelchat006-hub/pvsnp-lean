module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The void: what cancellation absorbs

A sum of terms that point in different directions loses some of its size
to cancellation. This file measures that loss exactly and proves what it is
for the determinant.

* `absorption s t` — the total size of the terms minus the size of their sum.
  It is never negative, and it is zero when every term points the same way.
  It makes sense for any kind of phase: signs, complex rotations, vectors.
* The determinant is a sum of `n!` terms, one per matching `σ` of rows to
  columns. Each term is the product along `σ`, kept upright (+) or turned
  half a turn (−) according to the sign of `σ`.
  - `card_upright_eq_card_flipped` / `two_mul_card_upright` — for `n ≥ 2`
    exactly half the terms are upright and half are turned.
  - `mass_eq_permanent` — the total size of the terms, before anything
    cancels, is the permanent of the matrix of entry sizes.
  - `absorbed_eq` — so what the void absorbs is
    `permanent (entry sizes) − ‖det‖`, and for a non-negative real matrix
    simply `permanent − |det|` (`absorbed_eq_of_nonneg`).
* Examples: the all-ones matrix absorbs everything (`absorbed_ones`); the
  permanent of a non-negative matrix absorbs nothing
  (`permanent_absorbs_nothing`); and in a 2×2 determinant whose two terms
  are `1` and `−e^{iθ}`, the void takes `2 − 2|sin(θ/2)|`
  (`absorbed_rotating`) — everything when the rotation sets the terms
  against each other, nothing when it lines them up.

## Why this matters for complexity (cited, not proved here)

The surviving part, `det`, is computable in polynomial time (Gaussian
elimination). The permanent of a 0/1 matrix is #P-complete (Valiant, 1979).
Since `absorbed = permanent − |det|`, computing exactly what the void
absorbs is as hard as computing the permanent. The easy object is what
survives the cancellation; the hard object is the cancellation itself.
-/

@[expose] public section

namespace PvsNP.Void

open Finset Equiv Matrix

/-! ## Absorption of any finite sum -/

section Absorption

variable {ι E : Type*} [SeminormedAddCommGroup E]

/-- What a sum loses to cancellation: the total size of its terms minus the
size of the result — "the part absorbed on the 0 plane". -/
noncomputable def absorption (s : Finset ι) (t : ι → E) : ℝ :=
  (∑ i ∈ s, ‖t i‖) - ‖∑ i ∈ s, t i‖

/-- The void never gives back more than went in. -/
theorem absorption_nonneg (s : Finset ι) (t : ι → E) : 0 ≤ absorption s t :=
  sub_nonneg.2 (norm_sum_le s t)

/-- Terms that all point the same way (non-negative reals) lose nothing. -/
theorem absorption_eq_zero_of_nonneg (s : Finset ι) (t : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ t i) :
    absorption s t = 0 := by
  unfold absorption
  rw [Real.norm_of_nonneg (sum_nonneg h), sub_eq_zero]
  exact sum_congr rfl fun i hi => Real.norm_of_nonneg (h i hi)

/-- A term and its exact opposite are absorbed completely. -/
theorem absorption_opposites (x : E) :
    absorption univ (fun b : Bool => if b then x else -x) = 2 * ‖x‖ := by
  simp [absorption, two_mul]

end Absorption

/-! ## The determinant's terms -/

section Determinant

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NormedField 𝕜]

/-- The determinant's term for the matching `σ`: the product along `σ`, kept
upright (+) or turned half a turn (−) by the sign of `σ`. -/
def detTerm (A : Matrix n n 𝕜) (σ : Perm n) : 𝕜 :=
  ((Perm.sign σ : ℤ) : 𝕜) * ∏ i, A (σ i) i

theorem det_eq_sum_detTerm (A : Matrix n n 𝕜) : A.det = ∑ σ, detTerm A σ :=
  det_apply' A

/-- Turning a term half a turn does not change its size. -/
theorem norm_detTerm (A : Matrix n n 𝕜) (σ : Perm n) :
    ‖detTerm A σ‖ = ∏ i, ‖A (σ i) i‖ := by
  rw [detTerm, norm_mul, norm_prod]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

/-- The total size of the determinant's terms before anything cancels. -/
noncomputable def mass (A : Matrix n n 𝕜) : ℝ :=
  ∑ σ, ‖detTerm A σ‖

/-- **The mass is a permanent**: the permanent of the matrix of entry sizes. -/
theorem mass_eq_permanent (A : Matrix n n 𝕜) : mass A = (A.map (‖·‖)).permanent := by
  simp only [mass, norm_detTerm, permanent, map_apply]

/-- What the void absorbs from the determinant. -/
noncomputable def absorbed (A : Matrix n n 𝕜) : ℝ :=
  absorption univ (detTerm A)

/-- **Absorption theorem.** What cancels out of the determinant is exactly
the permanent of the entry sizes minus the size of the determinant. -/
theorem absorbed_eq (A : Matrix n n 𝕜) :
    absorbed A = (A.map (‖·‖)).permanent - ‖A.det‖ := by
  have hm := mass_eq_permanent A
  unfold mass at hm
  rw [absorbed, absorption, hm, ← det_eq_sum_detTerm]

theorem absorbed_nonneg (A : Matrix n n 𝕜) : 0 ≤ absorbed A :=
  absorption_nonneg _ _

/-- Corollary: the determinant is never bigger than the permanent of the
entry sizes. -/
theorem norm_det_le_permanent (A : Matrix n n 𝕜) : ‖A.det‖ ≤ (A.map (‖·‖)).permanent := by
  have h := absorbed_nonneg A
  rw [absorbed_eq] at h
  linarith

/-- If every entry has size 1, the mass is `n!`: every matching contributes 1. -/
theorem mass_of_unit_entries (A : Matrix n n 𝕜) (h : ∀ i j, ‖A i j‖ = 1) :
    mass A = (Fintype.card n).factorial := by
  simp [mass, norm_detTerm, h, Fintype.card_perm]

end Determinant

/-! ## Half upright, half turned -/

section Split

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Half the terms sit on each side of the zero line.** With at least two
indices, exactly as many matchings are upright (+) as turned (−):
composing with one fixed swap turns every term over. -/
theorem card_upright_eq_card_flipped [Nontrivial n] :
    #{σ : Perm n | Perm.sign σ = 1} = #{σ : Perm n | Perm.sign σ = -1} := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne n
  refine card_nbij' (fun σ => swap a b * σ) (fun σ => swap a b * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    have h : Perm.sign σ = 1 := by simpa using hσ
    simp [Perm.sign_mul, Perm.sign_swap hab, h]
  · intro σ hσ
    have h : Perm.sign σ = -1 := by simpa using hσ
    simp [Perm.sign_mul, Perm.sign_swap hab, h]
  · intro σ _
    exact swap_mul_self_mul a b σ
  · intro σ _
    exact swap_mul_self_mul a b σ

/-- So the upright terms are exactly half of all `n!` terms. -/
theorem two_mul_card_upright [Nontrivial n] :
    2 * #{σ : Perm n | Perm.sign σ = 1} = (Fintype.card n).factorial := by
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Perm n)))
    (fun σ => Perm.sign σ = 1)
  have hneg : (univ.filter fun σ : Perm n => ¬ Perm.sign σ = 1) =
      univ.filter fun σ : Perm n => Perm.sign σ = -1 := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  rw [hneg, ← card_upright_eq_card_flipped, card_univ, Fintype.card_perm] at hsplit
  omega

end Split

/-! ## Real matrices with non-negative entries -/

section Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a non-negative real matrix: **absorbed = permanent − |det|**. -/
theorem absorbed_eq_of_nonneg (A : Matrix n n ℝ) (h : ∀ i j, 0 ≤ A i j) :
    absorbed A = A.permanent - |A.det| := by
  have hA : A.map (‖·‖) = A := by
    ext i j
    exact Real.norm_of_nonneg (h i j)
  rw [absorbed_eq, hA, Real.norm_eq_abs]

/-- The permanent has no signs: for a non-negative matrix its sum absorbs
nothing. -/
theorem permanent_absorbs_nothing (A : Matrix n n ℝ) (h : ∀ i j, 0 ≤ A i j) :
    absorption univ (fun σ : Perm n => ∏ i, A (σ i) i) = 0 :=
  absorption_eq_zero_of_nonneg _ _ fun _ _ => prod_nonneg fun _ _ => h _ _

/-- **Total absorption.** For the all-ones matrix with `n ≥ 2`, the `n!` terms
each have size 1, and they cancel to exactly 0: the void takes all of them. -/
theorem absorbed_ones [Nontrivial n] :
    absorbed (Matrix.of fun _ _ : n => (1 : ℝ)) = (Fintype.card n).factorial := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne n
  have hdet : (Matrix.of fun _ _ : n => (1 : ℝ)).det = 0 := det_zero_of_row_eq hab rfl
  have hm := mass_of_unit_entries (Matrix.of fun _ _ : n => (1 : ℝ)) (by simp)
  unfold mass at hm
  rw [absorbed, absorption, hm, ← det_eq_sum_detTerm, hdet, norm_zero, sub_zero]

/-- The identity matrix absorbs nothing: only one matching survives. -/
theorem absorbed_one : absorbed (1 : Matrix n n ℝ) = 0 := by
  rw [absorbed_eq_of_nonneg _ (fun i j => by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]),
    permanent_one, det_one, abs_one, sub_self]

end Real

/-! ## A rotating phase -/

/-- **Rotation sets the absorption.** The two terms of this 2×2 determinant are
`1` and `−e^{iθ}`. At `θ = 0` they point in opposite directions and cancel
completely (absorbed `= 2`); at a half turn `θ = π` they line up and nothing
cancels (absorbed `= 0`); in between the void takes `2 − 2|sin(θ/2)|`. -/
theorem absorbed_rotating (θ : ℝ) :
    absorbed !![(1 : ℂ), Complex.exp (Complex.I * θ); 1, 1] = 2 - 2 * |Real.sin (θ / 2)| := by
  have hunit : ∀ i j, ‖(!![(1 : ℂ), Complex.exp (Complex.I * θ); 1, 1]) i j‖ = 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  have hm := mass_of_unit_entries _ hunit
  unfold mass at hm
  rw [absorbed, absorption, hm, ← det_eq_sum_detTerm, det_fin_two_of, norm_sub_rev,
    mul_one, mul_one, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num

end PvsNP.Void

end
