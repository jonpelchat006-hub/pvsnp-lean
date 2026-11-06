/-!
# An exact count for parts of size one, two, and three

Core-Lean extraction from the older research/waves/Waves.lean. Enumerates
multiplicity triples (a,b,c) with a+2*b+3*c=n, and proves a closed count.
This is integer partition counting, distinct from the PARTITION decision
problem. No bit-complexity or general partition-counting claim is made.
-/

namespace PvsNP.CountingWaves

abbrev Triple := Nat × Nat × Nat

def withoutThrees (n : Nat) : List Triple :=
  (List.range (n / 2 + 1)).map fun b => (n - 2 * b, b, 0)

def addThree (t : Triple) : Triple := (t.1, t.2.1, t.2.2 + 1)

def triples : Nat → List Triple
  | 0 => withoutThrees 0
  | 1 => withoutThrees 1
  | 2 => withoutThrees 2
  | n + 3 => withoutThrees (n + 3) ++ (triples n).map addThree

theorem mem_withoutThrees (n a b c : Nat) :
    (a, b, c) ∈ withoutThrees n ↔ a + 2 * b = n ∧ c = 0 := by
  simp only [withoutThrees, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, ha, hb, hc⟩
    omega
  · rintro ⟨h, rfl⟩
    exact ⟨b, by omega, by omega, rfl, rfl⟩

/-- The enumeration contains exactly the nonnegative multiplicity solutions. -/
theorem mem_triples (n a b c : Nat) :
    (a, b, c) ∈ triples n ↔ a + 2 * b + 3 * c = n := by
  induction n using Nat.strongRecOn generalizing a b c with
  | ind n ih =>
    match n with
    | 0 => rw [triples, mem_withoutThrees]; omega
    | 1 => rw [triples, mem_withoutThrees]; omega
    | 2 => rw [triples, mem_withoutThrees]; omega
    | n + 3 =>
      simp only [triples, List.mem_append, mem_withoutThrees, List.mem_map]
      constructor
      · rintro (⟨h, hc⟩ | ⟨⟨a', b', c'⟩, ht, he⟩)
        · omega
        · have hs := (ih n (by omega) a' b' c').1 ht
          simp only [addThree, Prod.mk.injEq] at he
          omega
      · intro h
        by_cases hc : c = 0
        · exact Or.inl ⟨by omega, hc⟩
        · exact Or.inr ⟨(a, b, c - 1), (ih n (by omega) a b (c - 1)).2 (by omega),
            by simp [addThree]; omega⟩

theorem withoutThrees_length (n : Nat) : (withoutThrees n).length = n / 2 + 1 := by
  simp [withoutThrees]

theorem withoutThrees_nodup (n : Nat) : (withoutThrees n).Nodup := by
  apply List.pairwise_map.2
  apply List.nodup_range.imp
  intro a b hne he
  exact hne (congrArg (fun t : Triple => t.2.1) he)

/-- No solution is counted twice. -/
theorem triples_nodup (n : Nat) : (triples n).Nodup := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact withoutThrees_nodup 0
    | 1 => exact withoutThrees_nodup 1
    | 2 => exact withoutThrees_nodup 2
    | n + 3 =>
      apply List.nodup_append.2
      refine ⟨withoutThrees_nodup (n + 3), ?_, ?_⟩
      · apply List.pairwise_map.2
        apply (ih n (by omega)).imp
        intro a b hne he
        apply hne
        rcases a with ⟨a1, a2, a3⟩
        rcases b with ⟨b1, b2, b3⟩
        simp only [addThree, Prod.mk.injEq] at he ⊢
        omega
      · intro a ha b hb he
        obtain ⟨t, _, rfl⟩ := List.mem_map.1 hb
        have hz := ((mem_withoutThrees (n + 3) a.1 a.2.1 a.2.2).1 ha).2
        have hec := congrArg (fun t : Triple => t.2.2) he
        dsimp [addThree] at hec
        omega

/-- A full period of the two- and three-step contributions adds n+6. -/
theorem length_add_six (n : Nat) :
    (triples (n + 6)).length = (triples n).length + (n + 6) := by
  rw [show n + 6 = (n + 3) + 3 by omega, triples]
  simp only [List.length_append, List.length_map, withoutThrees_length, triples,
    List.length_append, List.length_map, withoutThrees_length]
  omega

def closedCount (n : Nat) : Nat := ((n + 3) * (n + 3) + 6) / 12

theorem closedCount_add_six (n : Nat) : closedCount (n + 6) = closedCount n + (n + 6) := by
  unfold closedCount
  have h : (n + 6 + 3) * (n + 6 + 3) + 6 =
      (n + 3) * (n + 3) + 6 + (n + 6) * 12 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  rw [h, Nat.add_mul_div_right _ _ (by decide)]

/-- The length of the explicit enumeration equals a fixed arithmetic formula. -/
theorem length_eq_closedCount (n : Nat) : (triples n).length = closedCount n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 6
    · match n with
      | 0 | 1 | 2 | 3 | 4 | 5 => decide
      | n + 6 => omega
    · have he : n = (n - 6) + 6 := by omega
      rw [he, length_add_six, ih (n - 6) (by omega), closedCount_add_six]

/-- A duplicate-free enumeration of exactly the solutions, with the closed count. -/
theorem certified_enumeration (n : Nat) :
    (∀ a b c, (a, b, c) ∈ triples n ↔ a + 2 * b + 3 * c = n) ∧
    (triples n).Nodup ∧ (triples n).length = closedCount n :=
  ⟨mem_triples n, triples_nodup n, length_eq_closedCount n⟩

example : closedCount 1000000 = 83333833334 := by decide

end PvsNP.CountingWaves

