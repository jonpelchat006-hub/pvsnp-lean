import PvsNP.Representation

/-!
# When merging representations preserves a task

Source ideas: the retained-distinction memory work (ALGEBRA_LINEAGE.md),
coarse-graining and vocabulary limits in SPARSE_VESICA_EXPANSION.md, and
merging reachable totals in PvsNP/Orientations.lean.

A code is sufficient for a task precisely when the task is constant on its
fibres, provided an answer exists for unused codes. Safe repeated merging
also needs transitions to preserve equal codes. Equal current answers alone
do not guarantee equal future answers. These are exact-function statements,
not runtime bounds or correctness proofs for the original Python programs.
-/

namespace PvsNP.Representation

variable {State Code Fine Coarse Answer Action : Type}

theorem refines_refl (encode : State → Code) : Refines encode encode :=
  ⟨fun x => x, fun _ => rfl⟩

theorem refines_trans {fine : State → Fine} {middle : State → Code}
    {coarse : State → Coarse} (hfm : Refines fine middle) (hmc : Refines middle coarse) :
    Refines fine coarse := by
  obtain ⟨p, hp⟩ := hfm
  obtain ⟨q, hq⟩ := hmc
  exact ⟨fun x => q (p x), fun x => (congrArg q (hp x)).trans (hq x)⟩

/-- Exact characterization. Nonempty answers supply a value on unused codes.
The constructed decoder is classical; no algorithm or cost is asserted. -/
theorem recoverable_iff_fiber_constant [Nonempty Answer]
    (encode : State → Code) (task : State → Answer) :
    Recoverable encode task ↔ ∀ x y, encode x = encode y → task x = task y := by
  constructor
  · intro h x y he
    exact equal_answers_of_equal_codes h he
  · intro h
    classical
    let decode (c : Code) : Answer :=
      if hc : ∃ x, encode x = c then task (Classical.choose hc)
      else Classical.choice (inferInstance : Nonempty Answer)
    refine ⟨decode, fun x => ?_⟩
    have hx : ∃ y, encode y = encode x := ⟨x, rfl⟩
    simp only [decode, hx, ↓reduceDIte]
    exact h _ x (Classical.choose_spec hx)

/-- A transition respects the representation when equal codes stay equal
after the same action. -/
def TransitionCompatible (encode : State → Code) (step : State → Action → State) : Prop :=
  ∀ x y, encode x = encode y → ∀ a, encode (step x a) = encode (step y a)

/-- Transition compatibility persists through every finite action sequence. -/
theorem equal_codes_after_actions {encode : State → Code}
    {step : State → Action → State} (hc : TransitionCompatible encode step)
    (actions : List Action) {x y : State} (hxy : encode x = encode y) :
    encode (actions.foldl step x) = encode (actions.foldl step y) := by
  induction actions generalizing x y with
  | nil => exact hxy
  | cons a rest ih => exact ih (hc x y hxy a)

/-- Sufficient codes plus compatible transitions preserve every future answer. -/
theorem equal_future_answers {encode : State → Code} {task : State → Answer}
    {step : State → Action → State} (ht : Recoverable encode task)
    (hc : TransitionCompatible encode step) (actions : List Action)
    {x y : State} (hxy : encode x = encode y) :
    task (actions.foldl step x) = task (actions.foldl step y) :=
  equal_answers_of_equal_codes ht (equal_codes_after_actions hc actions hxy)

/-- Equal answers now need not remain equal after a transition. -/
theorem current_answer_insufficient :
    let task := fun n : Nat => decide (n = 0)
    task 1 = task 2 ∧ task (Nat.pred 1) ≠ task (Nat.pred 2) := by decide

/-- Adding one signed piece preserves equality of the histories' totals. -/
theorem signed_sum_transition_compatible :
    TransitionCompatible (fun xs : List Int => xs.sum) (fun xs a => a :: xs) := by
  intro x y hxy a
  change x.sum = y.sum at hxy
  simp only [List.sum_cons]
  rw [hxy]

/-- For sum-based acceptance, histories with equal totals can be merged
without changing the answer for any fixed continuation of signed pieces.
This is a correctness statement about merging, not a bound on table size. -/
theorem equal_totals_same_future (x y future : List Int) (target : Int)
    (hxy : x.sum = y.sum) :
    decide ((future.foldl (fun xs a => a :: xs) x).sum = target) =
      decide ((future.foldl (fun xs a => a :: xs) y).sum = target) := by
  have ht : Recoverable (fun xs : List Int => xs.sum)
      (fun xs => decide (xs.sum = target)) := ⟨fun s => decide (s = target), fun _ => rfl⟩
  exact equal_future_answers ht signed_sum_transition_compatible future hxy

end PvsNP.Representation
