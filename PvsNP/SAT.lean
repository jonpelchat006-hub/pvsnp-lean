/-!
# SAT: short certificates and brute-force decidability

The mathematical content of "SAT ∈ NP", separated from any machine model:

* `sat_iff_certificate` — a CNF formula is satisfiable exactly when there is a
  certificate that is a sub-collection of the formula's own variable
  occurrences. Its encoding is therefore no longer than the formula's, which
  is the "short certificate" half of SAT ∈ NP. (The other half — that checking
  takes polynomial time — needs a concrete machine model.)
* `sat_iff_bruteForce` — satisfiability is decidable by trying every subset
  of the occurring variables. That takes exponential time; whether one can
  do fundamentally better is exactly the P vs NP question.
-/

namespace PvsNP.SAT

/-- A literal: a variable index and a polarity (`true` = positive). -/
structure Lit where
  var : Nat
  pos : Bool
deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def Lit.eval (a : Assignment) (l : Lit) : Bool :=
  if l.pos then a l.var else !a l.var

def Clause.eval (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => l.eval a || Clause.eval a c

def CNF.eval (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => c.eval a && CNF.eval a φ

def Satisfiable (φ : CNF) : Prop := ∃ a : Assignment, φ.eval a = true

/-- Every variable occurrence in the formula, in order (with repeats). -/
def CNF.vars : CNF → List Nat
  | [] => []
  | c :: φ => c.map (·.var) ++ CNF.vars φ

/-- The assignment that sets exactly the variables in `S` to true. -/
def ofSet (S : List Nat) : Assignment := fun v => decide (v ∈ S)

/-! ## Evaluation only looks at the variables that occur -/

theorem Clause.eval_congr {a b : Assignment} :
    ∀ {c : Clause}, (∀ l ∈ c, a l.var = b l.var) → c.eval a = c.eval b
  | [], _ => rfl
  | l :: c, h => by
    have hl : l.eval a = l.eval b := by
      simp [Lit.eval, h l (List.mem_cons_self ..)]
    have hc := Clause.eval_congr (c := c) fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    simp [Clause.eval, hl, hc]

theorem CNF.eval_congr {a b : Assignment} :
    ∀ {φ : CNF}, (∀ v ∈ φ.vars, a v = b v) → φ.eval a = φ.eval b
  | [], _ => rfl
  | c :: φ, h => by
    have hc : c.eval a = c.eval b := Clause.eval_congr fun l hl =>
      h l.var (by simp [CNF.vars]; exact Or.inl ⟨l, hl, rfl⟩)
    have hφ := CNF.eval_congr (φ := φ) fun v hv => h v (by simp [CNF.vars, hv])
    simp [CNF.eval, hc, hφ]

/-! ## Short certificates -/

/-- **SAT has short certificates.** `φ` is satisfiable iff some list `S` of
variables — drawn from `φ`'s own occurrences and no longer than that list —
makes `φ` true when exactly the variables in `S` are set to true. -/
theorem sat_iff_certificate (φ : CNF) :
    Satisfiable φ ↔ ∃ S : List Nat,
      (∀ v ∈ S, v ∈ φ.vars) ∧ S.length ≤ φ.vars.length ∧ φ.eval (ofSet S) = true := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨φ.vars.filter a, fun v hv => (List.mem_filter.1 hv).1,
      List.length_filter_le _ _, ?_⟩
    rw [CNF.eval_congr (b := a) fun v hv => ?_]
    · exact ha
    · simp [ofSet, List.mem_filter, hv]
  · rintro ⟨S, _, _, h⟩
    exact ⟨ofSet S, h⟩

/-! ## Brute force -/

/-- All sub-lists (subsets, as lists) of a list. -/
def subs : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => subs l ++ (subs l).map (x :: ·)

theorem filter_mem_subs (p : Nat → Bool) : ∀ l : List Nat, l.filter p ∈ subs l
  | [] => by simp [subs]
  | x :: l => by
    have ih := filter_mem_subs p l
    by_cases hx : p x = true
    · simp [hx, subs, ih]
    · simp [hx, subs, ih]

/-- Try every subset of the occurring variables. Exponential time. -/
def bruteForce (φ : CNF) : Bool :=
  (subs φ.vars).any fun S => φ.eval (ofSet S)

theorem sat_iff_bruteForce (φ : CNF) : Satisfiable φ ↔ bruteForce φ = true := by
  constructor
  · rintro ⟨a, ha⟩
    unfold bruteForce
    rw [List.any_eq_true]
    refine ⟨φ.vars.filter a, filter_mem_subs a _, ?_⟩
    rw [CNF.eval_congr (b := a) fun v hv => ?_]
    · exact ha
    · simp [ofSet, List.mem_filter, hv]
  · intro h
    unfold bruteForce at h
    rw [List.any_eq_true] at h
    obtain ⟨S, _, hS⟩ := h
    exact ⟨ofSet S, hS⟩

instance (φ : CNF) : Decidable (Satisfiable φ) :=
  decidable_of_iff _ (sat_iff_bruteForce φ).symm

/-! ## Sanity checks (checked by the kernel, no `native_decide`) -/

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁)` — satisfied by x₀ = x₁ = true. -/
def example₁ : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩]]

/-- `x₀ ∧ ¬x₀` — unsatisfiable. -/
def example₂ : CNF := [[⟨0, true⟩], [⟨0, false⟩]]

example : Satisfiable example₁ := by decide
example : ¬ Satisfiable example₂ := by decide

end PvsNP.SAT
