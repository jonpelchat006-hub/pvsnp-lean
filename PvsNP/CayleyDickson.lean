import PvsNP.Representation

/-!
# An exact zero-product certificate from the older algebra experiments

Source: Desktop Vesica AI/AI Detector/planet/cayley.py and ALGEBRA_LINEAGE.md.
Convention: (a,b)(c,d) = (ac - conjugate(d)b, da + b conjugate(c)).
Nested pairs are ordered with the first half before the second; e0 is scalar.
Integer coordinates avoid floating tolerance and machine integer overflow.
This verifies one witness, not the complete Python implementation or a claim
about ARC, geometry, or complexity. No associativity is assumed.
-/

namespace PvsNP.CayleyDickson

/-- Depth n has 2^n integer coordinates. -/
abbrev Carrier : Nat → Type
  | 0 => Int
  | n + 1 => Carrier n × Carrier n

def zero : (n : Nat) → Carrier n
  | 0 => 0
  | n + 1 => (zero n, zero n)

def add : (n : Nat) → Carrier n → Carrier n → Carrier n
  | 0, a, b => a + b
  | n + 1, a, b => (add n a.1 b.1, add n a.2 b.2)

def neg : (n : Nat) → Carrier n → Carrier n
  | 0, a => -a
  | n + 1, a => (neg n a.1, neg n a.2)

def conjugate : (n : Nat) → Carrier n → Carrier n
  | 0, a => a
  | n + 1, a => (conjugate n a.1, neg n a.2)

def mul : (n : Nat) → Carrier n → Carrier n → Carrier n
  | 0, a, b => a * b
  | n + 1, a, b =>
    (add n (mul n a.1 b.1) (neg n (mul n (conjugate n b.2) a.2)),
     add n (mul n b.2 a.1) (mul n a.2 (conjugate n b.1)))

/-- Out-of-range indices denote zero. All witness indices below are in range. -/
def basis : (n : Nat) → Nat → Carrier n
  | 0, i => if i = 0 then 1 else 0
  | n + 1, i =>
    if i < 2 ^ n then (basis n i, zero n)
    else (zero n, basis n (i - 2 ^ n))

def normSq : (n : Nat) → Carrier n → Int
  | 0, a => a * a
  | n + 1, a => normSq n a.1 + normSq n a.2

def leftWitness : Carrier 4 := add 4 (basis 4 1) (basis 4 10)
def rightWitness : Carrier 4 := add 4 (basis 4 5) (basis 4 14)

/-- The recorded sedenion witness, checked by kernel reduction. -/
theorem witness_product_zero : mul 4 leftWitness rightWitness = zero 4 := by decide

theorem leftWitness_nonzero : leftWitness ≠ zero 4 := by decide
theorem rightWitness_nonzero : rightWitness ≠ zero 4 := by decide

theorem witness_norms : normSq 4 leftWitness = 2 ∧ normSq 4 rightWitness = 2 := by decide

theorem nonzero_zero_product :
    ∃ a b : Carrier 4, a ≠ zero 4 ∧ b ≠ zero 4 ∧ mul 4 a b = zero 4 :=
  ⟨leftWitness, rightWitness, leftWitness_nonzero, rightWitness_nonzero,
    witness_product_zero⟩

/-- Multiplication by a nonzero element need not preserve distinctions. -/
theorem left_cancellation_fails :
    ∃ a b c : Carrier 4, a ≠ zero 4 ∧ b ≠ c ∧ mul 4 a b = mul 4 a c := by
  exact ⟨leftWitness, rightWitness, zero 4, leftWitness_nonzero,
    rightWitness_nonzero, by decide⟩

/-- The sum-of-squares norm is not multiplicative at depth four. -/
theorem normSq_not_multiplicative :
    normSq 4 (mul 4 leftWitness rightWitness) ≠
      normSq 4 leftWitness * normSq 4 rightWitness := by decide

/-- The product alone cannot say whether the right operand was nonzero. -/
theorem nonzero_not_recoverable_from_product :
    ¬ Representation.Recoverable (mul 4 leftWitness)
      (fun b : Carrier 4 => decide (b ≠ zero 4)) := by
  apply Representation.collision_obstructs_recovery
    (x := rightWitness) (y := zero 4)
  · decide
  · decide

/-- Retaining the operand beside its product preserves its entire identity. -/
theorem operand_recoverable_from_record :
    Representation.Recoverable
      (fun b : Carrier 4 => (mul 4 leftWitness b, b)) (fun b => b) :=
  Representation.recoverable_from_pair _ _

end PvsNP.CayleyDickson
