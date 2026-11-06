/-!
# What can be recovered from a representation?

Source idea: the September 2026 cube-memory work retained separate directional
channels after an older summary hid distinct records. See `RESEARCH_LIBRARY.md`.
These are elementary factorization results, formalized here for reuse; no
claim of a new mathematical discovery is intended.

We model exact functions, without a resource bound. A collision obstructs a
task only if that task needs the lost distinction. This does not say that
every algorithm must use this representation, nor verify the Python code.
-/

namespace PvsNP.Representation

variable {State Code Fine Answer : Type}

/-- The task can be answered using the code alone. No efficiency is claimed. -/
def Recoverable (encode : State → Code) (task : State → Answer) : Prop :=
  ∃ decode : Code → Answer, ∀ x, decode (encode x) = task x

/-- Equal codes must give equal answers to every recoverable task. -/
theorem equal_answers_of_equal_codes {encode : State → Code} {task : State → Answer}
    (h : Recoverable encode task) {x y : State} (hxy : encode x = encode y) :
    task x = task y := by
  obtain ⟨decode, hd⟩ := h
  exact (hd x).symm.trans ((congrArg decode hxy).trans (hd y))

/-- A collision between states requiring different answers prevents recovery. -/
theorem collision_obstructs_recovery {encode : State → Code} {task : State → Answer}
    {x y : State} (hxy : encode x = encode y) (ht : task x ≠ task y) :
    ¬ Recoverable encode task :=
  fun h => ht (equal_answers_of_equal_codes h hxy)

/-- No fixed postprocessing can recover a distinction already lost. -/
theorem postprocessing_preserves_collision (encode : State → Code) (process : Code → Fine)
    {x y : State} (hxy : encode x = encode y) :
    process (encode x) = process (encode y) :=
  congrArg process hxy

/-- `fine` refines `coarse` when the old code can be read from the new one. -/
def Refines (fine : State → Fine) (coarse : State → Code) : Prop :=
  ∃ project : Fine → Code, ∀ x, project (fine x) = coarse x

/-- A refinement preserves every task recoverable from the old code. -/
theorem recoverable_of_refines {fine : State → Fine} {coarse : State → Code}
    {task : State → Answer} (hr : Refines fine coarse) (ht : Recoverable coarse task) :
    Recoverable fine task := by
  obtain ⟨project, hp⟩ := hr
  obtain ⟨decode, hd⟩ := ht
  exact ⟨fun c => decode (project c), fun x => (congrArg decode (hp x)).trans (hd x)⟩

/-- Retaining an extra channel always refines the original representation. -/
theorem pair_refines (encode : State → Code) (extra : State → Fine) :
    Refines (fun x => (encode x, extra x)) encode :=
  ⟨Prod.fst, fun _ => rfl⟩

/-- A task explicitly retained as an extra channel is recoverable. -/
theorem recoverable_from_pair (encode : State → Code) (task : State → Answer) :
    Recoverable (fun x => (encode x, task x)) task :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- Exact reconstruction of the entire state forces the encoding to be injective. -/
theorem injective_of_reconstructible {encode : State → Code}
    (h : Recoverable encode (fun x => x)) :
    ∀ x y, encode x = encode y → x = y :=
  fun _ _ hxy => equal_answers_of_equal_codes h hxy

/-! ## Exact example: opposite directions disappear from a signed sum

This isolates the additive mechanism in `views.py` (directional contributions
are scaled by 1/2 there). It is not a formal model of the complete memory packer.
-/

abbrev Borders := Int × Int

def borderSummary (b : Borders) : Int := b.1 + b.2

def hasUpPass (b : Borders) : Bool := b.1 == 1

/-- An observed pass/refusal pair and two unobserved borders share a summary. -/
theorem border_collision : borderSummary (1, -1) = borderSummary (0, 0) := by
  decide

/-- The summary cannot answer whether the upward border was observed to pass. -/
theorem up_pass_not_recoverable : ¬ Recoverable borderSummary hasUpPass := by
  apply collision_obstructs_recovery border_collision
  decide

/-- Separate directional coordinates retain the answer. -/
theorem up_pass_recoverable_from_coordinates :
    Recoverable (fun b : Borders => b) hasUpPass :=
  ⟨hasUpPass, fun _ => rfl⟩

/-- A collision is harmless for a task that only asks for the sum itself. -/
theorem sum_recoverable : Recoverable borderSummary borderSummary :=
  ⟨fun x => x, fun _ => rfl⟩

end PvsNP.Representation
