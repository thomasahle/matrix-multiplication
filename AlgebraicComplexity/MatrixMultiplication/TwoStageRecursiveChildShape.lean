/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveChildShape
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Two-stage recursive child shapes

A two-level recursive decomposition does not consist of four unrelated leaf shapes.  It first
chooses an outer left child inside a fixed parent, then chooses one inner left child inside each
of the two complementary outer children.  The other two leaves are forced by complementation.

This module packages that dependency as `TwoStageRecursiveChildShape`.  Its visible coordinate
address consists of four ordered digits on each tensor leg.  The main finite facts say that every
leaf triple has the prescribed total, adjacent pairs recover the outer children, all four digits
recover the parent, and the visible address determines the complete nested split tree.

The abstraction is paper-independent.  It formalizes the nested split underlying Definition
`def:split-hatI` of [alman2025more],
`papers/sources/2404.16349/prelim.tex:225-269`.  Its first client is the level-two quotient forced
by `hyp:quotient-count` and `rem:granularity-forced` of the Total-Weight manuscript,
`better_bound/paper.tex:1729-1801`.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity

open Tensor

/-- A two-stage binary recursive split inside one parent shape.

`outer` is the left outer child.  `left` is the left inner child inside `outer`, and `right` is
the left inner child inside the complementary outer child.  The type keeps these parent-child
bounds dependent, so four locally legal but mutually inconsistent leaves cannot be represented.
-/
structure TwoStageRecursiveChildShape (parent : Leg → ℕ) (leafTotal : ℕ) where
  outer : RecursiveChildShape parent (2 * leafTotal)
  left : RecursiveChildShape outer.get leafTotal
  right : RecursiveChildShape (fun c ↦ parent c - outer.get c) leafTotal
  deriving DecidableEq

namespace TwoStageRecursiveChildShape

variable {parent : Leg → ℕ} {leafTotal : ℕ}

/-- The dependent split record is the corresponding finite dependent sum. -/
private def finiteModelEquiv (parent : Leg → ℕ) (leafTotal : ℕ) :
    TwoStageRecursiveChildShape parent leafTotal ≃
      Σ outer : RecursiveChildShape parent (2 * leafTotal),
        RecursiveChildShape outer.get leafTotal ×
          RecursiveChildShape (fun c ↦ parent c - outer.get c) leafTotal where
  toFun shape := ⟨shape.outer, (shape.left, shape.right)⟩
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv shape := by cases shape; rfl
  right_inv data := by rcases data with ⟨outer, left, right⟩; rfl

/-- There are finitely many recursively coherent two-stage child shapes. -/
noncomputable instance instFintype (parent : Leg → ℕ) (leafTotal : ℕ) :
    Fintype (TwoStageRecursiveChildShape parent leafTotal) := by
  exact Fintype.ofEquiv
    (Σ outer : RecursiveChildShape parent (2 * leafTotal),
      RecursiveChildShape outer.get leafTotal ×
        RecursiveChildShape (fun c ↦ parent c - outer.get c) leafTotal)
    (finiteModelEquiv parent leafTotal).symm

/-- Every coordinate of a child shape is at most its total. -/
private theorem child_get_le_total {upper : Leg → ℕ} {total : ℕ}
    (child : RecursiveChildShape upper total) (c : Leg) :
    child.get c ≤ total := by
  have htotal := child.total_eq
  cases c <;>
    simp only [RecursiveChildShape.get_X, RecursiveChildShape.get_Y,
      RecursiveChildShape.get_Z] at * <;>
    omega

/-- The complementary inner child in the left outer branch. -/
def leftComplement (shape : TwoStageRecursiveChildShape parent leafTotal) :
    RecursiveChildShape shape.outer.get leafTotal :=
  shape.left.complement shape.outer.total_eq

/-- Coordinate bounds of the complementary outer branch. -/
def rightParent (shape : TwoStageRecursiveChildShape parent leafTotal) : Leg → ℕ :=
  fun c ↦ parent c - shape.outer.get c

/-- If the original parent has four leaf totals, the complementary outer branch has two. -/
theorem rightParent_total (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) :
    shape.rightParent .X + shape.rightParent .Y + shape.rightParent .Z =
      2 * leafTotal := by
  have hx := shape.outer.get_le_parent .X
  have hy := shape.outer.get_le_parent .Y
  have hz := shape.outer.get_le_parent .Z
  have houter := shape.outer.total_eq
  unfold rightParent
  omega

/-- The complementary inner child in the right outer branch. -/
def rightComplement (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) :
    RecursiveChildShape shape.rightParent leafTotal :=
  shape.right.complement (shape.rightParent_total hparent)

/-- Natural-number coordinate of one of the four ordered leaves.

The outer index chooses the left or right outer branch; the inner index chooses its left child or
the derived complementary child. -/
def leafCoordinate (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal)
    (outerSide innerSide : Fin 2) (c : Leg) : ℕ :=
  if outerSide = 0 then
    if innerSide = 0 then shape.left.get c else shape.leftComplement.get c
  else if innerSide = 0 then shape.right.get c else (shape.rightComplement hparent).get c

/-- Bounded visible digit of one of the four ordered leaves. -/
def coordinate (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal)
    (c : Leg) (outerSide innerSide : Fin 2) : Fin (leafTotal + 1) :=
  ⟨shape.leafCoordinate hparent outerSide innerSide c,
    Nat.lt_succ_iff.mpr (by
      fin_cases outerSide <;> fin_cases innerSide
      · simpa [leafCoordinate] using child_get_le_total shape.left c
      · simpa [leafCoordinate] using child_get_le_total shape.leftComplement c
      · simpa [leafCoordinate] using child_get_le_total shape.right c
      · simpa [leafCoordinate] using
          child_get_le_total (shape.rightComplement hparent) c)⟩

/-- The visible four-digit coordinate word on each of the three tensor legs. -/
def coordinateAddress (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) :
    Leg → Fin 2 → Fin 2 → Fin (leafTotal + 1) :=
  fun c outerSide innerSide ↦ shape.coordinate hparent c outerSide innerSide

@[simp] theorem coordinate_val (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal)
    (c : Leg) (outerSide innerSide : Fin 2) :
    (shape.coordinate hparent c outerSide innerSide : ℕ) =
      shape.leafCoordinate hparent outerSide innerSide c :=
  rfl

/-- Every one of the four visible leaf triples has total `leafTotal`.

Proof sketch: each branch is either one of the two stored inner child shapes or its complement
inside an outer shape of total `2 * leafTotal`; all four cases therefore reduce to
`RecursiveChildShape.total_eq`. -/
theorem coordinate_sum (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal)
    (outerSide innerSide : Fin 2) :
    (shape.coordinate hparent .X outerSide innerSide : ℕ) +
        (shape.coordinate hparent .Y outerSide innerSide : ℕ) +
      (shape.coordinate hparent .Z outerSide innerSide : ℕ) = leafTotal := by
  fin_cases outerSide <;> fin_cases innerSide
  · simpa [coordinate, leafCoordinate] using shape.left.total_eq
  · simpa [coordinate, leafCoordinate] using shape.leftComplement.total_eq
  · simpa [coordinate, leafCoordinate] using shape.right.total_eq
  · simpa [coordinate, leafCoordinate] using (shape.rightComplement hparent).total_eq

/-- The first adjacent pair of leaf digits recovers the stored outer-left coordinate. -/
theorem coordinate_left_pair_sum
    (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) (c : Leg) :
    (shape.coordinate hparent c 0 0 : ℕ) +
        (shape.coordinate hparent c 0 1 : ℕ) = shape.outer.get c := by
  simpa [coordinate, leafCoordinate, leftComplement] using
    RecursiveChildShape.get_add_complement_get shape.outer.total_eq shape.left c

/-- The second adjacent pair recovers the complementary outer coordinate. -/
theorem coordinate_right_pair_sum
    (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) (c : Leg) :
    (shape.coordinate hparent c 1 0 : ℕ) +
        (shape.coordinate hparent c 1 1 : ℕ) = shape.rightParent c := by
  have hrightParent :
      (parent .X - shape.outer.get .X) +
          (parent .Y - shape.outer.get .Y) +
        (parent .Z - shape.outer.get .Z) = 2 * leafTotal := by
    simpa only [rightParent] using shape.rightParent_total hparent
  have hcomplement := RecursiveChildShape.complement_get
    (parent := fun d ↦ parent d - shape.outer.get d) hrightParent shape.right c
  change shape.right.get c + (shape.right.complement hrightParent).get c =
    parent c - shape.outer.get c
  rw [hcomplement]
  exact Nat.add_sub_of_le (shape.right.get_le_parent c)

/-- All four ordered leaf coordinates add back to the fixed parent coordinate.

Proof sketch: collapse each adjacent pair by the preceding two theorems.  The two resulting outer
coordinates are `u` and `parent - u`; their sum is the parent because `u` is bounded by it. -/
theorem coordinate_total (shape : TwoStageRecursiveChildShape parent leafTotal)
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) (c : Leg) :
    ((shape.coordinate hparent c 0 0 : ℕ) +
        (shape.coordinate hparent c 0 1 : ℕ)) +
      ((shape.coordinate hparent c 1 0 : ℕ) +
        (shape.coordinate hparent c 1 1 : ℕ)) = parent c := by
  rw [shape.coordinate_left_pair_sum hparent c,
    shape.coordinate_right_pair_sum hparent c]
  exact Nat.add_sub_of_le (shape.outer.get_le_parent c)

/-- The four visible coordinate triples determine the entire two-stage split tree.

Proof sketch: the first adjacent pair recovers `outer`.  Once that dependent field is identified,
the first leaf of each adjacent pair recovers the stored `left` and `right` inner shapes. -/
theorem coordinateAddress_injective
    (hparent : parent .X + parent .Y + parent .Z = 4 * leafTotal) :
    Function.Injective
      (fun shape : TwoStageRecursiveChildShape parent leafTotal ↦
        shape.coordinateAddress hparent) := by
  intro left right haddress
  change left.coordinateAddress hparent = right.coordinateAddress hparent at haddress
  have hcoordinate (c : Leg) (outerSide innerSide : Fin 2) :
      left.coordinate hparent c outerSide innerSide =
        right.coordinate hparent c outerSide innerSide := by
    have hpoint := congrFun (congrFun (congrFun haddress c) outerSide) innerSide
    simpa only [coordinateAddress] using hpoint
  have houter : left.outer = right.outer := by
    apply RecursiveChildShape.ext
    intro c
    calc
      left.outer.get c =
          (left.coordinate hparent c 0 0 : ℕ) +
            (left.coordinate hparent c 0 1 : ℕ) :=
        (left.coordinate_left_pair_sum hparent c).symm
      _ = (right.coordinate hparent c 0 0 : ℕ) +
            (right.coordinate hparent c 0 1 : ℕ) := by
        rw [hcoordinate c 0 0, hcoordinate c 0 1]
      _ = right.outer.get c := right.coordinate_left_pair_sum hparent c
  rcases left with ⟨leftOuter, leftInner, rightInner⟩
  rcases right with ⟨rightOuter, leftInner', rightInner'⟩
  change leftOuter = rightOuter at houter
  subst rightOuter
  have hleft : leftInner = leftInner' := by
    apply RecursiveChildShape.ext
    intro c
    have hvalue := congrArg Fin.val (hcoordinate c 0 0)
    simpa [coordinate, leafCoordinate] using hvalue
  subst leftInner'
  have hright : rightInner = rightInner' := by
    apply RecursiveChildShape.ext
    intro c
    have hvalue := congrArg Fin.val (hcoordinate c 1 0)
    simpa [coordinate, leafCoordinate] using hvalue
  subst rightInner'
  rfl

end TwoStageRecursiveChildShape

end AlgebraicComplexity
