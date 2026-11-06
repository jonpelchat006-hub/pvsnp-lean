import PvsNP.RepresentationRefinement

/-!
# Canonical merging by all future answers

Source trail: the retained-distinction memory work and the coarse-graining
ideas recorded in RESEARCH_LIBRARY.md. Two states can safely be treated as
one when every finite continuation gives the same task answer.

This defines the corresponding quotient, proves that its task and actions
are well-defined, and shows every sufficient, transition-compatible encoding
can recover it (assuming a nonempty state type for unused codes).
The quotient is an abstract mathematical construction, not a computable
minimization algorithm or a running-time bound.
-/

namespace PvsNP.FutureQuotient

open Representation

variable {State Code Action Answer : Type}

def FutureEq (step : State → Action → State) (task : State → Answer)
    (x y : State) : Prop :=
  ∀ actions : List Action, task (actions.foldl step x) = task (actions.foldl step y)

theorem futureEq_refl (step : State → Action → State) (task : State → Answer)
    (x : State) : FutureEq step task x x := fun _ => rfl

theorem futureEq_symm {step : State → Action → State} {task : State → Answer}
    {x y : State} (h : FutureEq step task x y) : FutureEq step task y x :=
  fun actions => (h actions).symm

theorem futureEq_trans {step : State → Action → State} {task : State → Answer}
    {x y z : State} (hxy : FutureEq step task x y) (hyz : FutureEq step task y z) :
    FutureEq step task x z :=
  fun actions => (hxy actions).trans (hyz actions)

theorem futureEq_task {step : State → Action → State} {task : State → Answer}
    {x y : State} (h : FutureEq step task x y) : task x = task y := h []

theorem futureEq_step {step : State → Action → State} {task : State → Answer}
    {x y : State} (h : FutureEq step task x y) (a : Action) :
    FutureEq step task (step x a) (step y a) :=
  fun actions => h (a :: actions)

def futureSetoid (step : State → Action → State) (task : State → Answer) : Setoid State where
  r := FutureEq step task
  iseqv := ⟨futureEq_refl step task, futureEq_symm, futureEq_trans⟩

abbrev FutureCode (step : State → Action → State) (task : State → Answer) :=
  Quotient (futureSetoid step task)

def code (step : State → Action → State) (task : State → Answer)
    (x : State) : FutureCode step task := Quotient.mk _ x

def output (step : State → Action → State) (task : State → Answer) :
    FutureCode step task → Answer :=
  Quotient.lift task (fun _ _ h => futureEq_task h)

def advance (step : State → Action → State) (task : State → Answer) (a : Action) :
    FutureCode step task → FutureCode step task :=
  Quotient.lift (fun x => code step task (step x a))
    (fun _ _ h => Quotient.sound (futureEq_step h a))

theorem code_eq_iff_futureEq (step : State → Action → State) (task : State → Answer)
    (x y : State) : code step task x = code step task y ↔ FutureEq step task x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := futureSetoid step task) h⟩

theorem output_code (step : State → Action → State) (task : State → Answer)
    (x : State) : output step task (code step task x) = task x := rfl

theorem advance_code (step : State → Action → State) (task : State → Answer)
    (a : Action) (x : State) :
    advance step task a (code step task x) = code step task (step x a) := rfl

theorem task_recoverable (step : State → Action → State) (task : State → Answer) :
    Recoverable (code step task) task := ⟨output step task, fun _ => rfl⟩

theorem code_transition_compatible (step : State → Action → State)
    (task : State → Answer) : TransitionCompatible (code step task) step := by
  intro x y hxy a
  exact Quotient.sound (futureEq_step (Quotient.exact hxy) a)

/-- No safe encoding merges more states than the future-answer quotient.
The factor map is classical and carries no computability guarantee. -/
theorem safe_encoding_refines_future [Nonempty State]
    {encode : State → Code} {step : State → Action → State} {task : State → Answer}
    (ht : Recoverable encode task) (hc : TransitionCompatible encode step) :
    Refines encode (code step task) := by
  classical
  letI : Nonempty (FutureCode step task) :=
    ⟨code step task (Classical.choice (inferInstance : Nonempty State))⟩
  change Recoverable encode (code step task)
  apply (recoverable_iff_fiber_constant encode (code step task)).2
  intro x y hxy
  apply Quotient.sound
  intro actions
  exact equal_future_answers ht hc actions hxy

end PvsNP.FutureQuotient
