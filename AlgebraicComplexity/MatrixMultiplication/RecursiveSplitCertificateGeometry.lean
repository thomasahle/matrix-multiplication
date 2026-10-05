/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildShapeGeometry
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildType

set_option autoImplicit false

/-!
# Recursive certificate slots as exact ordered child types

Recursive certificate files store an ordered split law on a padded finite slot list.  The tensor
theorem instead uses the intrinsic alphabet of bounded child shapes.  This module gives the
lossless bridge between those representations at levels three and four.

Only valid slots occur in the source alphabet.  Pushing their integral counts to intrinsic child
shapes automatically combines duplicate labels, so neither injectivity nor full support is an
assumption.  The construction is equivariant under an arbitrary tensor-leg orientation.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace LevelFourReconstruction

open Tensor MoreAsymmetryCompatibility

/-! ## Level-three parents -/

/-- Genuine slots in the padded level-three ordered-split row of one parent. -/
abbrev LevelThreeValidSlot (node : Fin PositiveLevelThreeData.nodeCount) :=
  {slot : Fin PositiveLevelThreeData.splitSlotCount //
    PositiveLevelThreeData.splitSlotValid node slot}

/-- Intrinsic child shape represented by one valid level-three certificate slot. -/
def levelThreeChildShape
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) :
    RecursiveChildShape
      ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4 :=
  let geometry := PositiveLevelThreeData.splitShape_geometry node slot.1 slot.2
  Shape.toRecursiveChildShape sigma geometry.1 geometry.2.1

@[simp] theorem levelThreeChildShape_get
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    (levelThreeChildShape node sigma slot).get c =
      (PositiveLevelThreeData.splitShape node slot.1).orientedLeg sigma c := by
  simp [levelThreeChildShape]

/-- The padded slot occupied by the coordinatewise complementary level-three child.  Its
validity is derived from the parent/split geometry, not supplied by a certificate mask. -/
def levelThreeComplementSlot
    (node : Fin PositiveLevelThreeData.nodeCount)
    (slot : LevelThreeValidSlot node) : LevelThreeValidSlot node := by
  let complement :=
    (PositiveLevelThreeData.nodeShape node).complement
      (PositiveLevelThreeData.splitShape node slot.1)
  have hmem : complement ∈
      levelThreeSplits (PositiveLevelThreeData.nodeShape node) :=
    mem_levelThreeSplits_iff.mpr
      ⟨(PositiveLevelThreeData.splitShape_geometry node slot.1 slot.2).2.2,
        Shape.complement_le _ _⟩
  have hindex :
      (levelThreeSplits (PositiveLevelThreeData.nodeShape node)).idxOf complement <
        (levelThreeSplits (PositiveLevelThreeData.nodeShape node)).length :=
    List.idxOf_lt_length_of_mem hmem
  exact
    ⟨⟨(levelThreeSplits (PositiveLevelThreeData.nodeShape node)).idxOf complement,
      hindex.trans_le
        (levelThreeSplits_length_le_ten
          (PositiveLevelThreeData.nodeShape_mem_positiveShapes node))⟩,
      hindex⟩

/-- Reading the complementary slot recovers the literal coordinatewise complement. -/
theorem levelThreeComplementSlot_shape
    (node : Fin PositiveLevelThreeData.nodeCount)
    (slot : LevelThreeValidSlot node) :
    PositiveLevelThreeData.splitShape node (levelThreeComplementSlot node slot).1 =
      (PositiveLevelThreeData.nodeShape node).complement
        (PositiveLevelThreeData.splitShape node slot.1) := by
  let complement :=
    (PositiveLevelThreeData.nodeShape node).complement
      (PositiveLevelThreeData.splitShape node slot.1)
  have hmem : complement ∈
      levelThreeSplits (PositiveLevelThreeData.nodeShape node) :=
    mem_levelThreeSplits_iff.mpr
      ⟨(PositiveLevelThreeData.splitShape_geometry node slot.1 slot.2).2.2,
        Shape.complement_le _ _⟩
  have hindex := List.idxOf_lt_length_of_mem hmem
  change
    (levelThreeSplits (PositiveLevelThreeData.nodeShape node))[
      (levelThreeSplits (PositiveLevelThreeData.nodeShape node)).idxOf complement]?.getD default =
      complement
  rw [List.getElem?_eq_getElem hindex, Option.getD_some]
  exact List.idxOf_get hindex

/-- The executable enumeration of total-four shapes has no duplicate entries. -/
private theorem shapes_four_nodup : (shapes 4).Nodup := by
  decide

/-- Every parent-specific level-three split list is duplicate-free. -/
private theorem levelThreeSplits_nodup (parent : Shape) :
    (levelThreeSplits parent).Nodup := by
  exact shapes_four_nodup.filter _

/-- Valid padded slots are determined uniquely by their reconstructed split shape. -/
theorem levelThreeSplitShape_injective
    (node : Fin PositiveLevelThreeData.nodeCount) :
    Function.Injective (fun slot : LevelThreeValidSlot node ↦
      PositiveLevelThreeData.splitShape node slot.1) := by
  intro left right heq
  have hval : left.1.val = right.1.val := by
    unfold PositiveLevelThreeData.splitShape at heq
    simp only [List.getElem?_eq_getElem left.2,
      List.getElem?_eq_getElem right.2, Option.getD_some] at heq
    exact (levelThreeSplits_nodup
      (PositiveLevelThreeData.nodeShape node)).getElem_inj_iff.mp heq
  exact Subtype.ext (Fin.ext hval)

/-- Coordinatewise complementation inside a containing natural-valued shape is involutive. -/
private theorem shape_complement_complement_of_le {parent child : Shape}
    (hchild : child ≤ parent) :
    parent.complement (parent.complement child) = child := by
  rcases parent with ⟨px, py, pz⟩
  rcases child with ⟨cx, cy, cz⟩
  change cx ≤ px ∧ cy ≤ py ∧ cz ≤ pz at hchild
  simp only [Shape.complement, Shape.mk.injEq]
  omega

/-- Complementing a valid level-three slot twice returns the original labelled slot. -/
theorem levelThreeComplementSlot_involutive
    (node : Fin PositiveLevelThreeData.nodeCount) :
    Function.Involutive (levelThreeComplementSlot node) := by
  intro slot
  apply levelThreeSplitShape_injective node
  calc
    PositiveLevelThreeData.splitShape node
        (levelThreeComplementSlot node (levelThreeComplementSlot node slot)).1 =
      (PositiveLevelThreeData.nodeShape node).complement
        (PositiveLevelThreeData.splitShape node
          (levelThreeComplementSlot node slot).1) :=
      levelThreeComplementSlot_shape node (levelThreeComplementSlot node slot)
    _ = (PositiveLevelThreeData.nodeShape node).complement
        ((PositiveLevelThreeData.nodeShape node).complement
          (PositiveLevelThreeData.splitShape node slot.1)) := by
      rw [levelThreeComplementSlot_shape]
    _ = PositiveLevelThreeData.splitShape node slot.1 :=
      shape_complement_complement_of_le
        (PositiveLevelThreeData.splitShape_geometry node slot.1 slot.2).2.1

/-- The permutation of valid level-three slots induced by swapping the two labelled children. -/
def levelThreeComplementSlotPerm
    (node : Fin PositiveLevelThreeData.nodeCount) : Equiv.Perm (LevelThreeValidSlot node) :=
  (levelThreeComplementSlot_involutive node).toPerm (levelThreeComplementSlot node)

@[simp] theorem levelThreeComplementSlotPerm_apply
    (node : Fin PositiveLevelThreeData.nodeCount) (slot : LevelThreeValidSlot node) :
    levelThreeComplementSlotPerm node slot = levelThreeComplementSlot node slot :=
  rfl

@[simp] theorem levelThreeComplementSlotPerm_symm
    (node : Fin PositiveLevelThreeData.nodeCount) :
    (levelThreeComplementSlotPerm node).symm = levelThreeComplementSlotPerm node :=
  (levelThreeComplementSlot_involutive node).toPerm_symm

/-- Complementary valid slots represent complementary intrinsic child shapes in every
orientation. -/
theorem levelThreeChildShape_complement
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) :
    levelThreeChildShape node sigma (levelThreeComplementSlot node slot) =
      RecursiveChildShape.complement
        (by
          rw [(PositiveLevelThreeData.nodeShape node).orientedLeg_total,
            (PositiveLevelThreeData.nodeShape_geometry node).2])
        (levelThreeChildShape node sigma slot) := by
  apply RecursiveChildShape.ext
  intro c
  simp only [levelThreeChildShape_get, levelThreeComplementSlot_shape,
    RecursiveChildShape.complement_get]
  cases hs : sigma c <;>
    simp [Shape.orientedLeg, Shape.leg, Shape.complement, hs]

/-- Any normalized integral level-three slot row is an exact ordered recursive split type. -/
noncomputable def levelThreeExactSplitType
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (samples : ℕ) (count : LevelThreeValidSlot node → ℕ)
    (htotal : ∑ slot, count slot = samples) :
    ExactRecursiveSplitType
      ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4 samples :=
  ExactRecursiveSplitType.ofMappedCounts
    (levelThreeChildShape node sigma) count htotal

@[simp] theorem levelThreeExactSplitType_count
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (samples : ℕ) (count : LevelThreeValidSlot node → ℕ)
    (htotal : ∑ slot, count slot = samples)
    (child : RecursiveChildShape
      ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4) :
    (levelThreeExactSplitType node sigma samples count htotal).count child =
      WordType.mappedType (levelThreeChildShape node sigma) count child :=
  rfl

/-! ## Level-four parents -/

/-- Genuine slots in the padded level-four ordered-pair row of one positive parent. -/
abbrev LevelFourValidSlot (parent : Fin positiveLevelFourShapeCount) :=
  {slot : Fin levelFourPairSlotCount // levelFourPairSlotValid parent slot}

/-- Geometry of the left child represented by a valid level-four parent-local slot. -/
theorem levelFourLeftChild_geometry
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    (levelFourPairAtSlot parent slot.1 slot.2).1.total = 8 ∧
      (levelFourPairAtSlot parent slot.1 slot.2).1 ≤ positiveLevelFourShape parent := by
  have geometry := levelFourPairAtSlot_geometry parent slot.1 slot.2
  have support := mem_levelFourPairs_iff.mp geometry.1
  refine ⟨support.1, ?_⟩
  rw [← geometry.2]
  exact Shape.le_add_left _ _

/-- In a valid parent-local level-four slot, the stored right child is literally the
coordinatewise complement of the stored left child. -/
theorem levelFourRightChild_eq_complement
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    (positiveLevelFourShape parent).complement
        (levelFourPairAtSlot parent slot.1 slot.2).1 =
      (levelFourPairAtSlot parent slot.1 slot.2).2 := by
  rw [← (levelFourPairAtSlot_geometry parent slot.1 slot.2).2]
  exact Shape.add_complement_left _ _

/-- Geometry of the stored right child.  It is another legal total-eight left-child candidate
for the same parent. -/
theorem levelFourRightChild_geometry
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    (levelFourPairAtSlot parent slot.1 slot.2).2.total = 8 ∧
      (levelFourPairAtSlot parent slot.1 slot.2).2 ≤ positiveLevelFourShape parent := by
  have geometry := levelFourPairAtSlot_geometry parent slot.1 slot.2
  have support := mem_levelFourPairs_iff.mp geometry.1
  refine ⟨support.2.1, ?_⟩
  rw [← geometry.2]
  change
    (levelFourPairAtSlot parent slot.1 slot.2).2.x ≤
          (levelFourPairAtSlot parent slot.1 slot.2).1.x +
            (levelFourPairAtSlot parent slot.1 slot.2).2.x ∧
      (levelFourPairAtSlot parent slot.1 slot.2).2.y ≤
          (levelFourPairAtSlot parent slot.1 slot.2).1.y +
            (levelFourPairAtSlot parent slot.1 slot.2).2.y ∧
      (levelFourPairAtSlot parent slot.1 slot.2).2.z ≤
          (levelFourPairAtSlot parent slot.1 slot.2).1.z +
            (levelFourPairAtSlot parent slot.1 slot.2).2.z
  omega

/-- Parent-local slot whose left child is the stored right child of `slot`.  The construction
uses the exact reconstructed child list; no padded-slot or certificate-support hypothesis is
accepted. -/
def levelFourComplementSlot
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) : LevelFourValidSlot parent := by
  let children :=
    levelThreeShapes.filter fun child ↦ decide (child ≤ positiveLevelFourShape parent)
  let right := (levelFourPairAtSlot parent slot.1 slot.2).2
  have hright : right ∈ children := by
    rw [show children = levelThreeShapes.filter
      (fun child ↦ decide (child ≤ positiveLevelFourShape parent)) by rfl,
      List.mem_filter, decide_eq_true_eq]
    exact ⟨mem_shapes_iff_total.mpr (levelFourRightChild_geometry parent slot).1,
      (levelFourRightChild_geometry parent slot).2⟩
  have hindex : children.idxOf right < children.length :=
    List.idxOf_lt_length_of_mem hright
  have hlength : children.length ≤ levelFourPairSlotCount := by
    simpa [children, levelFourPairsForParent] using
      levelFourPairsForParent_length_le parent
  refine ⟨⟨children.idxOf right, hindex.trans_le hlength⟩, ?_⟩
  change children.idxOf right <
    (levelFourPairsForParent (positiveLevelFourShape parent)).length
  simpa [children, levelFourPairsForParent] using hindex

/-- Looking up the complementary slot recovers the original stored right child as its left
child. -/
theorem levelFourComplementSlot_leftChild
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    (levelFourPairAtSlot parent (levelFourComplementSlot parent slot).1
        (levelFourComplementSlot parent slot).2).1 =
      (levelFourPairAtSlot parent slot.1 slot.2).2 := by
  let children :=
    levelThreeShapes.filter fun child ↦ decide (child ≤ positiveLevelFourShape parent)
  let right := (levelFourPairAtSlot parent slot.1 slot.2).2
  have hright : right ∈ children := by
    rw [show children = levelThreeShapes.filter
      (fun child ↦ decide (child ≤ positiveLevelFourShape parent)) by rfl,
      List.mem_filter, decide_eq_true_eq]
    exact ⟨mem_shapes_iff_total.mpr (levelFourRightChild_geometry parent slot).1,
      (levelFourRightChild_geometry parent slot).2⟩
  have hindex : children.idxOf right < children.length :=
    List.idxOf_lt_length_of_mem hright
  change
    ((children.map fun left ↦
      (left, (positiveLevelFourShape parent).complement left))[
        children.idxOf right]'(by simpa using hindex)).1 = right
  rw [List.getElem_map]
  exact List.getElem_idxOf hindex

/-- The right child of the complementary slot is the original left child. -/
theorem levelFourComplementSlot_rightChild
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    (levelFourPairAtSlot parent (levelFourComplementSlot parent slot).1
        (levelFourComplementSlot parent slot).2).2 =
      (levelFourPairAtSlot parent slot.1 slot.2).1 := by
  rw [← levelFourRightChild_eq_complement parent (levelFourComplementSlot parent slot),
    levelFourComplementSlot_leftChild]
  rw [← levelFourRightChild_eq_complement parent slot]
  exact shape_complement_complement_of_le (levelFourLeftChild_geometry parent slot).2

/-- Complementing a parent-local ordered pair swaps its two labelled children. -/
theorem levelFourPairAtSlot_complement
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    levelFourPairAtSlot parent (levelFourComplementSlot parent slot).1
        (levelFourComplementSlot parent slot).2 =
      ((levelFourPairAtSlot parent slot.1 slot.2).2,
        (levelFourPairAtSlot parent slot.1 slot.2).1) := by
  apply Prod.ext
  · exact levelFourComplementSlot_leftChild parent slot
  · exact levelFourComplementSlot_rightChild parent slot

/-- Parent-local pair lookup is injective on genuine slots. -/
theorem levelFourPairAtSlot_injective
    (parent : Fin positiveLevelFourShapeCount) :
    Function.Injective (fun slot : LevelFourValidSlot parent ↦
      levelFourPairAtSlot parent slot.1 slot.2) := by
  intro left right heq
  have hindices :
      (⟨left.1.val, left.2⟩ :
          Fin (levelFourPairsForParent (positiveLevelFourShape parent)).length) =
        ⟨right.1.val, right.2⟩ :=
    (levelFourPairsForParent_nodup (positiveLevelFourShape parent)).injective_get heq
  have hval : left.1.val = right.1.val :=
    congrArg
      (fun index : Fin
        (levelFourPairsForParent (positiveLevelFourShape parent)).length ↦ index.val)
      hindices
  exact Subtype.ext (Fin.ext hval)

/-- Parent-local complementation is an involution, including at self-complementary slots. -/
theorem levelFourComplementSlot_involutive
    (parent : Fin positiveLevelFourShapeCount) :
    Function.Involutive (levelFourComplementSlot parent) := by
  intro slot
  apply levelFourPairAtSlot_injective parent
  calc
    levelFourPairAtSlot parent
        (levelFourComplementSlot parent (levelFourComplementSlot parent slot)).1
        (levelFourComplementSlot parent (levelFourComplementSlot parent slot)).2 =
      ((levelFourPairAtSlot parent (levelFourComplementSlot parent slot).1
          (levelFourComplementSlot parent slot).2).2,
        (levelFourPairAtSlot parent (levelFourComplementSlot parent slot).1
          (levelFourComplementSlot parent slot).2).1) :=
      levelFourPairAtSlot_complement parent (levelFourComplementSlot parent slot)
    _ = levelFourPairAtSlot parent slot.1 slot.2 := by
      rw [levelFourPairAtSlot_complement]

/-- The permutation of valid level-four slots induced by swapping the labelled children. -/
def levelFourComplementSlotPerm
    (parent : Fin positiveLevelFourShapeCount) : Equiv.Perm (LevelFourValidSlot parent) :=
  (levelFourComplementSlot_involutive parent).toPerm (levelFourComplementSlot parent)

@[simp] theorem levelFourComplementSlotPerm_apply
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    levelFourComplementSlotPerm parent slot = levelFourComplementSlot parent slot :=
  rfl

@[simp] theorem levelFourComplementSlotPerm_symm
    (parent : Fin positiveLevelFourShapeCount) :
    (levelFourComplementSlotPerm parent).symm = levelFourComplementSlotPerm parent :=
  (levelFourComplementSlot_involutive parent).toPerm_symm

/-- Intrinsic child shape represented by one valid level-four certificate slot. -/
def levelFourChildShape
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    RecursiveChildShape ((positiveLevelFourShape parent).orientedLeg sigma) 8 :=
  Shape.toRecursiveChildShape sigma
    (levelFourLeftChild_geometry parent slot).1
    (levelFourLeftChild_geometry parent slot).2

@[simp] theorem levelFourChildShape_get
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) :
    (levelFourChildShape parent sigma slot).get c =
      (levelFourPairAtSlot parent slot.1 slot.2).1.orientedLeg sigma c := by
  simp [levelFourChildShape]

/-- Complementary valid slots represent complementary intrinsic child shapes in every
orientation. -/
theorem levelFourChildShape_complement
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    levelFourChildShape parent sigma (levelFourComplementSlot parent slot) =
      RecursiveChildShape.complement
        (by
          rw [(positiveLevelFourShape parent).orientedLeg_total,
            (positiveLevelFourShape_geometry parent).2])
        (levelFourChildShape parent sigma slot) := by
  apply RecursiveChildShape.ext
  intro c
  simp only [levelFourChildShape_get, levelFourComplementSlot_leftChild,
    RecursiveChildShape.complement_get]
  rw [← levelFourRightChild_eq_complement]
  cases hs : sigma c <;>
    simp [Shape.orientedLeg, Shape.leg, Shape.complement, hs]

/-- Any normalized integral level-four slot row is an exact ordered recursive split type. -/
noncomputable def levelFourExactSplitType
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (samples : ℕ) (count : LevelFourValidSlot parent → ℕ)
    (htotal : ∑ slot, count slot = samples) :
    ExactRecursiveSplitType ((positiveLevelFourShape parent).orientedLeg sigma) 8 samples :=
  ExactRecursiveSplitType.ofMappedCounts
    (levelFourChildShape parent sigma) count htotal

@[simp] theorem levelFourExactSplitType_count
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (samples : ℕ) (count : LevelFourValidSlot parent → ℕ)
    (htotal : ∑ slot, count slot = samples)
    (child : RecursiveChildShape ((positiveLevelFourShape parent).orientedLeg sigma) 8) :
    (levelFourExactSplitType parent sigma samples count htotal).count child =
      WordType.mappedType (levelFourChildShape parent sigma) count child :=
  rfl

end LevelFourReconstruction
end AlgebraicComplexity
