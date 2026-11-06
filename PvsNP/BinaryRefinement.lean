/-!
# Regions and cuts in a binary refinement tree

Source: structural-reasoning/theory/folding/FOLDING_TOWER.md.
Each internal node represents one operation splitting a region into two
nonempty children; leaves represent the final regions. Every finite tree
of this form has one more region than cut. The exact depth-d counts
2^d and 2^d - 1 require every leaf to be at the same depth. For an
unbalanced tree, depth gives an upper bound instead.

This is an abstract combinatorial model, with no geometric realization
assumed. Matching these counts to algebra dimensions does not define an
algebra multiplication or prove that a physical or learned system has one.
-/

namespace PvsNP.BinaryRefinement

/-- A region is either retained, or split into exactly two further regions. -/
inductive Tree where
  | leaf
  | cut (left right : Tree)
deriving DecidableEq

def regions : Tree → Nat
  | .leaf => 1
  | .cut left right => regions left + regions right

def cuts : Tree → Nat
  | .leaf => 0
  | .cut left right => cuts left + cuts right + 1

/-- Maximum number of cuts along a root-to-leaf path. -/
def depth : Tree → Nat
  | .leaf => 0
  | .cut left right => max (depth left) (depth right) + 1

/-- All leaves occur at exactly depth d; both children must be refined equally. -/
inductive Perfect : Tree → Nat → Prop where
  | leaf : Perfect .leaf 0
  | cut {left right : Tree} {d : Nat} :
      Perfect left d → Perfect right d → Perfect (.cut left right) (d + 1)

/-- The tree obtained by splitting every current region at every round. -/
def complete : Nat → Tree
  | 0 => .leaf
  | d + 1 => .cut (complete d) (complete d)

theorem regions_positive (tree : Tree) : 0 < regions tree := by
  induction tree with
  | leaf => decide
  | cut left right ihLeft ihRight =>
    simp only [regions]
    omega

/-- Each binary split adds one cut and one final region. -/
theorem regions_eq_cuts_add_one (tree : Tree) : regions tree = cuts tree + 1 := by
  induction tree with
  | leaf => rfl
  | cut left right ihLeft ihRight =>
    simp only [regions, cuts, ihLeft, ihRight]
    omega

theorem cuts_eq_regions_sub_one (tree : Tree) : cuts tree = regions tree - 1 := by
  have h := regions_eq_cuts_add_one tree
  omega

theorem complete_perfect (d : Nat) : Perfect (complete d) d := by
  induction d with
  | zero => exact .leaf
  | succ d ih => exact .cut ih ih

theorem depth_of_perfect {tree : Tree} {d : Nat} (h : Perfect tree d) :
    depth tree = d := by
  induction h with
  | leaf => rfl
  | cut hLeft hRight ihLeft ihRight => simp [depth, ihLeft, ihRight]

/-- Uniform refinement gives the exact doubling count. -/
theorem regions_of_perfect {tree : Tree} {d : Nat} (h : Perfect tree d) :
    regions tree = 2 ^ d := by
  induction h with
  | leaf => rfl
  | cut hLeft hRight ihLeft ihRight =>
    simp only [regions, ihLeft, ihRight, Nat.pow_succ]
    omega

theorem cuts_of_perfect {tree : Tree} {d : Nat} (h : Perfect tree d) :
    cuts tree = 2 ^ d - 1 := by
  rw [cuts_eq_regions_sub_one, regions_of_perfect h]

theorem depth_complete (d : Nat) : depth (complete d) = d :=
  depth_of_perfect (complete_perfect d)

theorem regions_complete (d : Nat) : regions (complete d) = 2 ^ d :=
  regions_of_perfect (complete_perfect d)

theorem cuts_complete (d : Nat) : cuts (complete d) = 2 ^ d - 1 :=
  cuts_of_perfect (complete_perfect d)

/-- Arbitrary nested bisections can have fewer leaves than the perfect tree. -/
theorem regions_le_pow_depth (tree : Tree) : regions tree ≤ 2 ^ depth tree := by
  induction tree with
  | leaf => decide
  | cut left right ihLeft ihRight =>
    have hLeft : 2 ^ depth left ≤ 2 ^ max (depth left) (depth right) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
    have hRight : 2 ^ depth right ≤ 2 ^ max (depth left) (depth right) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
    simp only [regions, depth, Nat.pow_succ]
    omega

theorem regions_le_pow_of_depth_le {tree : Tree} {d : Nat} (h : depth tree ≤ d) :
    regions tree ≤ 2 ^ d :=
  Nat.le_trans (regions_le_pow_depth tree) (Nat.pow_le_pow_right (by decide) h)

theorem cuts_le_pow_depth_sub_one (tree : Tree) : cuts tree ≤ 2 ^ depth tree - 1 := by
  have h := regions_le_pow_depth tree
  have hc := regions_eq_cuts_add_one tree
  omega

/-! The source's 2/1, 4/3, 8/7, 16/15 tower is an exact count. -/
example :
    (regions (complete 1), cuts (complete 1)) = (2, 1) ∧
    (regions (complete 2), cuts (complete 2)) = (4, 3) ∧
    (regions (complete 3), cuts (complete 3)) = (8, 7) ∧
    (regions (complete 4), cuts (complete 4)) = (16, 15) := by decide

/-- Maximum depth alone does not force the perfect-tree count. -/
example :
    let tree := Tree.cut .leaf (.cut .leaf .leaf)
    depth tree = 2 ∧ regions tree = 3 ∧ regions tree ≠ 2 ^ depth tree := by decide

end PvsNP.BinaryRefinement
