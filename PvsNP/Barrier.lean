import PvsNP.Classes

/-!
# The interface barrier: closure properties cannot settle P vs NP

`PvsNP/Classes.lean` proves the whole structural theory of NP-completeness
from eight closure properties of "polynomial time". This file shows those
eight properties carry **no information** about P vs NP:

* `omniscient` satisfies every axiom and has **P = NP**;
* `blind` satisfies every axiom and has **P ≠ NP**.

So any genuine proof of P ≠ NP (or P = NP) must use something specific about
real computation — how a machine step works, how information flows through a
circuit — beyond what the textbook structural arguments use.

This is a toy relative of the classical barriers. Baker–Gill–Solovay (1975)
built oracles `A`, `B` with `Pᴬ = NPᴬ` and `Pᴮ ≠ NPᴮ`; both oracle worlds
satisfy every axiom of `Model`, which is the formal reason why
"relativizing" arguments cannot resolve the question. The two models below
are far cruder than oracle worlds, but they make the same point with a
fully checked proof. (Natural proofs, Razborov–Rudich 1997, and
algebrization, Aaronson–Wigderson 2009, rule out further families of
techniques; those are not formalized here.)
-/

namespace PvsNP

open Model

/-! ## Model 1: everything is easy -/

/-- Every function with polynomially bounded output counts as "polynomial
time", and every predicate is "decidable in polynomial time". -/
def omniscient : Model where
  Fn  f := ∃ c k, ∀ x, (f x).length ≤ poly c k x.length
  Dec _ := True
  Ver _ := True
  fn_id := ⟨0, 1, fun x => by show x.length ≤ (x.length + 0) ^ 1; rw [Nat.pow_one]; omega⟩
  fn_comp := by
    rintro f g ⟨c₁, k₁, h₁⟩ ⟨c₂, k₂, h₂⟩
    exact ⟨c₂ + c₁ + 2, (k₁ + 2) * k₂, fun x =>
      Nat.le_trans (h₂ (f x))
        (Nat.le_trans (poly_mono (h₁ x)) (poly_comp_le c₂ k₂ c₁ k₁ x.length))⟩
  fn_size := fun h => h
  fn_ite := by
    intro d a b _
    refine ⟨a.length + b.length, 1, fun x => ?_⟩
    show (if d x then a else b).length ≤ (x.length + (a.length + b.length)) ^ 1
    rw [Nat.pow_one]
    cases d x <;> simp <;> omega
  dec_comp := fun _ _ => trivial
  dec_not := fun _ => trivial
  ver_of_dec := fun _ => trivial
  ver_comp := fun _ _ => trivial

/-- In `omniscient`, every language whatsoever is in P. -/
theorem omniscient_inP (L : Language) : omniscient.InP L := by
  classical
  exact ⟨fun x => decide (L x), trivial, fun x => (decide_eq_true_iff).symm⟩

theorem omniscient_PeqNP : omniscient.PeqNP :=
  fun L => ⟨P_subset_NP, fun _ => omniscient_inP L⟩

/-! ## Model 2: polynomial time can only see constants -/

/-- "Polynomial-time" functions are the constants and the identity;
"polynomial-time" decisions are the constant answers; checkers are
unrestricted. -/
def blind : Model where
  Fn  f := (∃ a, ∀ x, f x = a) ∨ (∀ x, f x = x)
  Dec d := ∃ b, ∀ x, d x = b
  Ver _ := True
  fn_id := Or.inr fun _ => rfl
  fn_comp := by
    rintro f g (⟨a, hf⟩ | hf) (⟨b, hg⟩ | hg)
    · exact Or.inl ⟨b, fun x => hg (f x)⟩
    · exact Or.inl ⟨a, fun x => by show g (f x) = a; rw [hg, hf]⟩
    · exact Or.inl ⟨b, fun x => hg (f x)⟩
    · exact Or.inr fun x => by show g (f x) = x; rw [hg, hf]
  fn_size := by
    rintro f (⟨a, hf⟩ | hf)
    · refine ⟨a.length, 1, fun x => ?_⟩
      show (f x).length ≤ (x.length + a.length) ^ 1
      rw [hf, Nat.pow_one]; omega
    · refine ⟨0, 1, fun x => ?_⟩
      show (f x).length ≤ (x.length + 0) ^ 1
      rw [hf, Nat.pow_one]; omega
  fn_ite := by
    rintro d a b ⟨c, hd⟩
    exact Or.inl ⟨if c then a else b, fun x => by
      show (if d x then a else b) = (if c then a else b); rw [hd]⟩
  dec_comp := by
    rintro f d _ ⟨c, hd⟩
    exact ⟨c, fun x => hd (f x)⟩
  dec_not := by
    rintro d ⟨c, hd⟩
    exact ⟨!c, fun x => by show (!d x) = !c; rw [hd]⟩
  ver_of_dec := fun _ => trivial
  ver_comp := fun _ _ => trivial

/-- The witness language: "the input is exactly the one-bit string `1`". -/
def isOne : Language := fun x => x = [true]

theorem blind_isOne_NP : blind.InNP isOne := by
  refine ⟨fun x _ => decide (x = [true]), fun x => x, trivial, Or.inr fun _ => rfl,
    fun x => ?_⟩
  constructor
  · intro h
    exact ⟨[], Nat.zero_le _, decide_eq_true (show x = [true] from h)⟩
  · rintro ⟨_, _, h⟩
    exact (of_decide_eq_true h : x = [true])

theorem blind_isOne_not_P : ¬ blind.InP isOne := by
  rintro ⟨d, ⟨c, hc⟩, hd⟩
  have h1 : d [true] = true := (hd [true]).1 rfl
  have h2 : ¬ d [] = true := fun h => by
    have : isOne [] := (hd []).2 h
    simp [isOne] at this
  rw [hc] at h1 h2
  exact h2 h1

theorem blind_PneNP : ¬ blind.PeqNP :=
  fun h => blind_isOne_not_P ((h isOne).2 blind_isOne_NP)

/-! ## The barrier -/

/-- **The eight closure axioms of polynomial time are consistent with both
P = NP and P ≠ NP.** No argument that uses only those axioms can resolve
the question. -/
theorem closure_axioms_do_not_decide_PvsNP :
    (∃ M : Model, M.PeqNP) ∧ (∃ M : Model, ¬ M.PeqNP) :=
  ⟨⟨omniscient, omniscient_PeqNP⟩, ⟨blind, blind_PneNP⟩⟩

end PvsNP
