import PvsNP.RepresentationRefinement
import Init.Data.Function
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

/-!
# Future distinctions and finite memory

Motivation: the retained-distinction/collision memory work in
C:/Users/GamerTech/Desktop/Vesica AI/AI Detector/planet/ALGEBRA_LINEAGE.md, and the exact
representation lemmas in RepresentationRefinement.lean. This is the standard
finite-state distinguishability argument, followed by the standard exact
deterministic one-way EQUALITY bound; no new discovery is claimed.

A representation that answers the task and respects all allowed transitions
must preserve states separated by a possible future. Finite capacity then
bounds how many such states fit. The integer-counter example quantifies over
unbounded exact integers. The communication example allows one deterministic
message and requires correctness on every pair. These restrictions are part
of the statements, not lower bounds on unrestricted algorithms, approximate
or randomized methods, or P versus NP.
-/

namespace PvsNP.FiniteState

open PvsNP.Representation

variable {State Code Action Answer : Type}

/-- Every pair of distinct states can be told apart by some finite future. -/
def FutureDistinguishable (step : State → Action → State) (task : State → Answer) : Prop :=
  ∀ x y, x ≠ y → ∃ actions : List Action,
    task (actions.foldl step x) ≠ task (actions.foldl step y)

/-- Recoverability plus transition compatibility preserves every future distinction. -/
theorem injective_of_future_distinguishable {encode : State → Code}
    {step : State → Action → State} {task : State → Answer}
    (hd : FutureDistinguishable step task) (ht : Recoverable encode task)
    (hc : TransitionCompatible encode step) : Function.Injective encode := by
  intro x y hxy
  classical
  by_cases heq : x = y
  · exact heq
  · obtain ⟨actions, ha⟩ := hd x y heq
    exact False.elim (ha (equal_future_answers ht hc actions hxy))

/-- The finite pigeonhole bound, proved by mapping a duplicate-free enumeration. -/
theorem fin_le_of_injective {n m : Nat} {encode : Fin n → Fin m}
    (hi : Function.Injective encode) : n ≤ m := by
  have hn : ((List.finRange n).map encode).Nodup := by
    apply List.pairwise_map.2
    exact (List.nodup_finRange n).imp (fun hne he => hne (hi he))
  have hb := hn.length_le_of_subset (l₂ := List.finRange m)
    (fun code _ => List.mem_finRange code)
  simpa only [List.length_map, List.length_finRange] using hb

/-- A finite transition system with n distinguishable states needs at least n codes. -/
theorem finite_state_capacity_bound {n m : Nat} {encode : Fin n → Fin m}
    {step : Fin n → Action → Fin n} {task : Fin n → Answer}
    (hd : FutureDistinguishable step task) (ht : Recoverable encode task)
    (hc : TransitionCompatible encode step) : n ≤ m :=
  fin_le_of_injective (injective_of_future_distinguishable hd ht hc)

/-- Different exact integer totals can be separated by appending the opposite of one. -/
theorem integer_counter_distinguishable :
    FutureDistinguishable (fun total action : Int => total + action)
      (fun total => decide (total = 0)) := by
  intro x y hne
  refine ⟨[-x], ?_⟩
  simp only [List.foldl_cons, List.foldl_nil, Int.add_right_neg, decide_true]
  intro he
  have hz : y + -x = 0 := of_decide_eq_true he.symm
  exact hne (by omega)

/-- A finite code cannot be an exact, transition-compatible zero-test counter
for all unbounded integer states and all integer increments. -/
theorem no_finite_exact_counter (m : Nat) (encode : Int → Fin m) :
    ¬ (Recoverable encode (fun total => decide (total = 0)) ∧
      TransitionCompatible encode (fun total action => total + action)) := by
  rintro ⟨ht, hc⟩
  have hi := injective_of_future_distinguishable integer_counter_distinguishable ht hc
  have hf : Function.Injective (fun i : Fin (m + 1) => encode (i.val : Int)) := by
    intro i j he
    apply Fin.ext
    have h := hi he
    omega
  have hb := fin_le_of_injective hf
  omega

/-- A deterministic message answering equality for every possible query is injective. -/
theorem equality_message_injective [DecidableEq State] {send : State → Code}
    {receive : Code → State → Bool}
    (correct : ∀ x y, receive (send x) y = decide (x = y)) :
    Function.Injective send := by
  intro x y hxy
  have hself := correct x x
  have hother := correct y x
  rw [← hxy, hself] at hother
  have hyx : y = x := of_decide_eq_true (by simpa only [decide_true] using hother.symm)
  exact hyx.symm

/-- One exact deterministic EQUALITY message for n possibilities needs n possible codes. -/
theorem equality_message_capacity {n m : Nat} {send : Fin n → Fin m}
    {receive : Fin m → Fin n → Bool}
    (correct : ∀ x y, receive (send x) y = decide (x = y)) : n ≤ m :=
  fin_le_of_injective (equality_message_injective correct)

/-- The message-capacity bound is sharp, including empty and singleton domains. -/
theorem equality_protocol_iff_capacity (n m : Nat) :
    (∃ send : Fin n → Fin m, ∃ receive : Fin m → Fin n → Bool,
      ∀ x y, receive (send x) y = decide (x = y)) ↔ n ≤ m := by
  constructor
  · rintro ⟨send, receive, correct⟩
    exact equality_message_capacity correct
  · intro hnm
    refine ⟨Fin.castLE hnm, fun code y => decide (code.val = y.val), ?_⟩
    intro x y
    simp only [Fin.val_castLE, Fin.ext_iff]

/-- For 2^inputBits inputs and at most 2^messageBits messages, exact deterministic
one-way EQUALITY requires messageBits ≥ inputBits. Fin represents the alphabets. -/
theorem equality_bits_lower_bound {inputBits messageBits : Nat}
    {send : Fin (2 ^ inputBits) → Fin (2 ^ messageBits)}
    {receive : Fin (2 ^ messageBits) → Fin (2 ^ inputBits) → Bool}
    (correct : ∀ x y, receive (send x) y = decide (x = y)) :
    inputBits ≤ messageBits :=
  (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (equality_message_capacity correct)

end PvsNP.FiniteState
