/-!
# A real lower bound in a restricted model: OR needs n queries

Proving P ≠ NP means proving a *lower bound*: some problem cannot be solved
with few resources by *any* algorithm. For general algorithms and circuits
nobody knows how. In restricted models we can, and this file is the
simplest complete example.

A decision tree reads one input bit per step and branches on it. Its depth
is the worst-case number of bits read. We prove:

* `or_lower_bound` — every decision tree computing `OR` of `n` bits has
  depth at least `n` (the adversary argument), and
* `or_upper_bound` — depth `n` is achievable,

so the decision-tree complexity of `OR_n` is exactly `n`.
-/

namespace PvsNP.DecisionTree

/-- A decision tree over inputs `Nat → Bool`. `node i t₀ t₁` reads bit `i`
and continues in `t₀` if it is `false`, in `t₁` if it is `true`. -/
inductive DTree where
  | leaf : Bool → DTree
  | node : Nat → DTree → DTree → DTree

namespace DTree

def eval (x : Nat → Bool) : DTree → Bool
  | leaf b => b
  | node i t₀ t₁ => if x i then eval x t₁ else eval x t₀

def depth : DTree → Nat
  | leaf _ => 0
  | node _ t₀ t₁ => max (depth t₀) (depth t₁) + 1

/-- The bits read when the tree runs on input `x`. -/
def path (x : Nat → Bool) : DTree → List Nat
  | leaf _ => []
  | node i t₀ t₁ => i :: (if x i then path x t₁ else path x t₀)

theorem path_length_le (x : Nat → Bool) : ∀ t : DTree, (t.path x).length ≤ t.depth
  | leaf _ => Nat.le_refl _
  | node i t₀ t₁ => by
    have h₀ := path_length_le x t₀
    have h₁ := path_length_le x t₁
    simp only [path, depth, List.length_cons]
    cases x i <;> simp <;> omega

/-- Two inputs that agree on every bit `x`'s run reads end in the same leaf. -/
theorem eval_eq_of_agree {x y : Nat → Bool} :
    ∀ t : DTree, (∀ i ∈ t.path x, y i = x i) → t.eval y = t.eval x
  | leaf _, _ => rfl
  | node i t₀ t₁, h => by
    have hi : y i = x i := h i (List.mem_cons_self ..)
    simp only [eval, hi]
    cases hx : x i
    · exact eval_eq_of_agree t₀ fun j hj => h j (by simp [path, hx, hj])
    · exact eval_eq_of_agree t₁ fun j hj => h j (by simp [path, hx, hj])

end DTree

open DTree

/-- `OR` of the first `n` bits. -/
def orN : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, x => x n || orN n x

theorem orN_zero_input (n : Nat) : orN n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orN, ih]

theorem orN_unit {n j : Nat} (hj : j < n) : orN n (fun i => decide (i = j)) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j = n
    · simp [orN, h]
    · simp [orN, ih (by omega)]

/-- Pigeonhole: a list that contains every number below `n` has length ≥ `n`. -/
theorem length_ge_of_cover : ∀ (n : Nat) (l : List Nat), (∀ j < n, j ∈ l) → n ≤ l.length
  | 0, _, _ => Nat.zero_le _
  | n + 1, l, h => by
    have hn : n ∈ l := h n (Nat.lt_succ_self n)
    have h' : ∀ j < n, j ∈ l.erase n := fun j hj =>
      (List.mem_erase_of_ne (Nat.ne_of_lt hj)).2 (h j (by omega))
    have := length_ge_of_cover n (l.erase n) h'
    rw [List.length_erase_of_mem hn] at this
    have := List.length_pos_of_mem hn
    omega

/-- **Lower bound.** Any decision tree computing `OR` of `n` bits must read
all `n` of them in the worst case.

Adversary argument: run the tree on the all-zeros input. If it read fewer
than `n` bits, some bit `j < n` was never read; flipping it to `1` changes
`OR` from `false` to `true` but cannot change the leaf reached. -/
theorem or_lower_bound (n : Nat) (t : DTree) (ht : ∀ x, t.eval x = orN n x) :
    n ≤ t.depth := by
  apply Nat.le_of_not_lt
  intro hlt
  let zero : Nat → Bool := fun _ => false
  have hshort : (t.path zero).length < n := Nat.lt_of_le_of_lt (path_length_le zero t) hlt
  -- some bit below n is never read on the all-zeros run
  have hmiss : ∃ j < n, j ∉ t.path zero := by
    apply Classical.byContradiction
    intro hno
    have hcover : ∀ j < n, j ∈ t.path zero := fun j hj =>
      Classical.byContradiction fun hj' => hno ⟨j, hj, hj'⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (length_ge_of_cover n _ hcover) hshort)
  obtain ⟨j, hj, hjp⟩ := hmiss
  let e : Nat → Bool := fun i => decide (i = j)
  have hagree : ∀ i ∈ t.path zero, e i = zero i := fun i hi => by
    have : i ≠ j := fun h => hjp (h ▸ hi)
    simp [e, zero, this]
  have hsame := eval_eq_of_agree t hagree
  rw [ht, ht, orN_unit hj, orN_zero_input] at hsame
  exact Bool.noConfusion hsame

/-- The obvious tree: read bits `n-1, …, 0`, stop at the first `1`. -/
def orTree : Nat → DTree
  | 0 => leaf false
  | n + 1 => node n (orTree n) (leaf true)

/-- **Upper bound.** Depth `n` suffices. -/
theorem or_upper_bound (n : Nat) :
    (∀ x, (orTree n).eval x = orN n x) ∧ (orTree n).depth = n := by
  induction n with
  | zero => exact ⟨fun _ => rfl, rfl⟩
  | succ n ih =>
    refine ⟨fun x => ?_, ?_⟩
    · simp only [orTree, DTree.eval, orN, ih.1 x]
      cases x n <;> simp
    · simp [orTree, DTree.depth, ih.2]

/-- **Decision-tree complexity of `OR_n` is exactly `n`.** -/
theorem or_complexity_exact (n : Nat) :
    (∃ t : DTree, (∀ x, t.eval x = orN n x) ∧ t.depth = n) ∧
    (∀ t : DTree, (∀ x, t.eval x = orN n x) → n ≤ t.depth) :=
  ⟨⟨orTree n, or_upper_bound n⟩, or_lower_bound n⟩

end PvsNP.DecisionTree
