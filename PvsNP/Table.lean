/-!
# The table: rules that combine answers

A *rule* takes three true/false values and returns one. Applied variable by
variable, it combines three assignments into a new one. A set of answers
*keeps* a rule when combining any three answers by it always gives another
answer (in the constraint-satisfaction literature: the rule is a
*polymorphism*).

Schaefer's six rules:

| rule | value | kept by |
|---|---|---|
| `zero` | false | sets containing the all-false assignment |
| `one` | true | sets containing the all-true assignment |
| `both` | `a && b` | Horn clauses |
| `either` | `a ‖ b` | dual-Horn clauses |
| `majority` | the majority of `a, b, c` | clauses of width 2 (2-SAT) |
| `minority` | `a xor b xor c` | parity equations (XOR-SAT) |

Schaefer's dichotomy theorem (1978, cited, not proved here): a problem built
from Boolean constraints of fixed kinds is solvable in polynomial time if all
its kinds keep one common rule from this list, and NP-complete otherwise. The
legs of the table are the six rules.

This file proves:
* `parity_keeps_minority`: every system of parity equations keeps `minority`.
  This is the rule Gaussian elimination works with (experiment part 10:
  elimination crosses XOR-SAT's threshold without noticing it).
* `width_two_keeps_majority`: every clause with at most two literals keeps
  `majority` (the 2-SAT leg).
* `nae3_breaks_all`: the formula "x0, x1, x2 not all equal", written as the two
  3-literal clauses `x0 ∨ x1 ∨ x2` and `¬x0 ∨ ¬x1 ∨ ¬x2`, breaks all six rules,
  each with an explicit witness of three answers whose combination is not an
  answer. By Schaefer's theorem this places not-all-equal 3-SAT on no leg of
  the table: it is NP-complete.
* `table`: the three together.

Nothing here is about running time. The link from "keeps a rule" to "solvable
in polynomial time" is Schaefer's theorem, which is cited.
-/

namespace PvsNP.Table

/-- An assignment of true/false to the variables `0, 1, 2, …`. -/
abbrev Assignment := Nat → Bool

/-- Combine three assignments variable by variable with a rule. -/
def combine (op : Bool → Bool → Bool → Bool) (x y z : Assignment) : Assignment :=
  fun v => op (x v) (y v) (z v)

/-- A set of answers keeps a rule: combining any three answers by it gives an
answer. -/
def Keeps (op : Bool → Bool → Bool → Bool) (good : Assignment → Prop) : Prop :=
  ∀ x y z, good x → good y → good z → good (combine op x y z)

/-! ## Schaefer's six rules -/

def zero : Bool → Bool → Bool → Bool := fun _ _ _ => false
def one : Bool → Bool → Bool → Bool := fun _ _ _ => true
def both : Bool → Bool → Bool → Bool := fun a b _ => a && b
def either : Bool → Bool → Bool → Bool := fun a b _ => a || b
def majority : Bool → Bool → Bool → Bool := fun a b c => (a && b) || (a && c) || (b && c)
def minority : Bool → Bool → Bool → Bool := fun a b c => xor (xor a b) c

/-! ## Parity equations keep `minority` -/

/-- The parity of the variables in a list (repeats counted). -/
def parity (x : Assignment) : List Nat → Bool
  | [] => false
  | v :: vs => xor (x v) (parity x vs)

/-- A parity equation `x_{v₁} + ⋯ + x_{vₖ} = rhs (mod 2)`. -/
structure ParityEq where
  vars : List Nat
  rhs : Bool

/-- An assignment solves a system when it satisfies every equation. -/
def SolvesParity (sys : List ParityEq) (x : Assignment) : Prop :=
  ∀ e ∈ sys, parity x e.vars = e.rhs

/-- Parity commutes with the minority rule. -/
theorem parity_minority (x y z : Assignment) (vs : List Nat) :
    parity (combine minority x y z) vs
      = minority (parity x vs) (parity y vs) (parity z vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show xor (minority (x v) (y v) (z v)) (parity (combine minority x y z) vs)
      = minority (xor (x v) (parity x vs)) (xor (y v) (parity y vs)) (xor (z v) (parity z vs))
    rw [ih]
    generalize x v = a
    generalize y v = b
    generalize z v = c
    generalize parity x vs = A
    generalize parity y vs = B
    generalize parity z vs = C
    cases a <;> cases b <;> cases c <;> cases A <;> cases B <;> cases C <;> rfl

/-- **The XOR leg.** Every system of parity equations keeps `minority`. -/
theorem parity_keeps_minority (sys : List ParityEq) : Keeps minority (SolvesParity sys) := by
  intro x y z hx hy hz e he
  rw [parity_minority, hx e he, hy e he, hz e he]
  cases e.rhs <;> rfl

/-! ## Clauses -/

/-- A literal: a variable, negated or not. -/
structure Lit where
  var : Nat
  neg : Bool

/-- The value of a literal under an assignment. -/
def Lit.value (x : Assignment) (l : Lit) : Bool := xor (x l.var) l.neg

/-- A clause holds when one of its literals is true. -/
def ClauseHolds (c : List Lit) (x : Assignment) : Prop := c.any (Lit.value x) = true

/-- A formula (a list of clauses) holds when every clause holds. -/
def Solves (f : List (List Lit)) (x : Assignment) : Prop := ∀ c ∈ f, ClauseHolds c x

/-- A literal's value commutes with the majority rule. -/
theorem value_majority (x y z : Assignment) (l : Lit) :
    Lit.value (combine majority x y z) l
      = majority (Lit.value x l) (Lit.value y l) (Lit.value z l) := by
  show xor (majority (x l.var) (y l.var) (z l.var)) l.neg
    = majority (xor (x l.var) l.neg) (xor (y l.var) l.neg) (xor (z l.var) l.neg)
  generalize x l.var = a
  generalize y l.var = b
  generalize z l.var = c
  generalize l.neg = s
  cases a <;> cases b <;> cases c <;> cases s <;> rfl

/-- **The 2-SAT leg.** Every clause with at most two literals keeps `majority`. -/
theorem width_two_keeps_majority (c : List Lit) (hc : c.length ≤ 2) :
    Keeps majority (ClauseHolds c) := by
  intro x y z hx hy hz
  match c, hc with
  | [], _ => exact absurd hx (by simp [ClauseHolds])
  | [l], _ =>
    simp only [ClauseHolds, List.any_cons, List.any_nil, Bool.or_false] at hx hy hz ⊢
    rw [value_majority, hx, hy, hz]
    rfl
  | [l₁, l₂], _ =>
    simp only [ClauseHolds, List.any_cons, List.any_nil, Bool.or_false] at hx hy hz ⊢
    rw [value_majority, value_majority]
    revert hx hy hz
    generalize Lit.value x l₁ = a₁
    generalize Lit.value y l₁ = b₁
    generalize Lit.value z l₁ = c₁
    generalize Lit.value x l₂ = a₂
    generalize Lit.value y l₂ = b₂
    generalize Lit.value z l₂ = c₂
    cases a₁ <;> cases b₁ <;> cases c₁ <;> cases a₂ <;> cases b₂ <;> cases c₂ <;> decide
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-! ## Not-all-equal 3-SAT breaks every rule -/

/-- An assignment read from a list (variables past its end are false). -/
def bits (l : List Bool) : Assignment := fun v => l.getD v false

/-- `x0 ∨ x1 ∨ x2` -/
def pos3 : List Lit := [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩]

/-- `¬x0 ∨ ¬x1 ∨ ¬x2` -/
def neg3 : List Lit := [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩]

/-- "x0, x1, x2 are not all equal", as two 3-literal clauses. -/
def nae3 : List (List Lit) := [pos3, neg3]

instance (f : List (List Lit)) (x : Assignment) : Decidable (Solves f x) :=
  inferInstanceAs (Decidable (∀ c ∈ f, c.any (Lit.value x) = true))

/-- A rule is broken when three answers combine into a non-answer. -/
theorem breaks {op : Bool → Bool → Bool → Bool} {good : Assignment → Prop}
    (x y z : Assignment) (hx : good x) (hy : good y) (hz : good z)
    (bad : ¬ good (combine op x y z)) : ¬ Keeps op good :=
  fun h => bad (h x y z hx hy hz)

theorem nae3_breaks_zero : ¬ Keeps zero (Solves nae3) :=
  breaks (bits [true, false, false]) (bits [true, false, false]) (bits [true, false, false])
    (by decide) (by decide) (by decide) (by decide)

theorem nae3_breaks_one : ¬ Keeps one (Solves nae3) :=
  breaks (bits [true, false, false]) (bits [true, false, false]) (bits [true, false, false])
    (by decide) (by decide) (by decide) (by decide)

theorem nae3_breaks_both : ¬ Keeps both (Solves nae3) :=
  breaks (bits [true, false, false]) (bits [false, true, false]) (bits [true, false, false])
    (by decide) (by decide) (by decide) (by decide)

theorem nae3_breaks_either : ¬ Keeps either (Solves nae3) :=
  breaks (bits [false, true, true]) (bits [true, false, true]) (bits [true, false, false])
    (by decide) (by decide) (by decide) (by decide)

theorem nae3_breaks_majority : ¬ Keeps majority (Solves nae3) :=
  breaks (bits [true, false, false]) (bits [false, true, false]) (bits [false, false, true])
    (by decide) (by decide) (by decide) (by decide)

theorem nae3_breaks_minority : ¬ Keeps minority (Solves nae3) :=
  breaks (bits [true, false, false]) (bits [false, true, false]) (bits [true, true, false])
    (by decide) (by decide) (by decide) (by decide)

/-- Not-all-equal 3-SAT keeps none of Schaefer's six rules. -/
theorem nae3_breaks_all :
    ¬ Keeps zero (Solves nae3) ∧ ¬ Keeps one (Solves nae3) ∧
    ¬ Keeps both (Solves nae3) ∧ ¬ Keeps either (Solves nae3) ∧
    ¬ Keeps majority (Solves nae3) ∧ ¬ Keeps minority (Solves nae3) :=
  ⟨nae3_breaks_zero, nae3_breaks_one, nae3_breaks_both, nae3_breaks_either,
    nae3_breaks_majority, nae3_breaks_minority⟩

/-- **The table.** Parity equations stand on the `minority` leg and width-2
clauses on the `majority` leg; not-all-equal 3-SAT stands on none of the six. -/
theorem table :
    (∀ sys, Keeps minority (SolvesParity sys)) ∧
    (∀ c : List Lit, c.length ≤ 2 → Keeps majority (ClauseHolds c)) ∧
    (¬ Keeps zero (Solves nae3) ∧ ¬ Keeps one (Solves nae3) ∧
      ¬ Keeps both (Solves nae3) ∧ ¬ Keeps either (Solves nae3) ∧
      ¬ Keeps majority (Solves nae3) ∧ ¬ Keeps minority (Solves nae3)) :=
  ⟨parity_keeps_minority, width_two_keeps_majority, nae3_breaks_all⟩

end PvsNP.Table
