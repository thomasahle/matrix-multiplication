/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeGeometry
import Mathlib.Data.List.FinRange

/-!
# Ordered-pair geometry for level-four recursive certificates

The level-four optimizer stores one row for every ordered pair of level-three shapes whose
coordinatewise sum is a positive level-four shape.  This module reconstructs that finite geometry
from first principles.  In particular, the constants `45`, `105`, `1785`, and `30` are theorems
about the reconstructed lists rather than trusted properties of generated arrays.

The ordering agrees with the certificate generator: level-three shapes are lexicographic, the
left shape is the outer loop, the right shape is the inner loop, and inadmissible pairs are
discarded.  For a fixed positive parent, local slots retain this global pair order.

This is paper-independent finite geometry.  It contains no probabilities, tensor constructions,
or floating-point data.
-/

namespace AlgebraicComplexity.LevelFourReconstruction

namespace Shape

/-- Coordinatewise addition of constituent shapes. -/
def add (u v : Shape) : Shape :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

@[simp] theorem add_x (u v : Shape) : (u.add v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Shape) : (u.add v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Shape) : (u.add v).z = u.z + v.z := rfl

/-- Totals add under coordinatewise addition. -/
theorem add_total (u v : Shape) : (u.add v).total = u.total + v.total := by
  simp only [add, total]
  omega

/-- The left summand is coordinatewise contained in the sum. -/
theorem le_add_left (u v : Shape) : u ≤ u.add v := by
  exact ⟨by simp, by simp, by simp⟩

/-- Adding a contained shape to its coordinatewise complement recovers the parent. -/
theorem add_complement_of_le {u parent : Shape} (h : u ≤ parent) :
    u.add (parent.complement u) = parent := by
  rcases u with ⟨ux, uy, uz⟩
  rcases parent with ⟨px, py, pz⟩
  change ux ≤ px ∧ uy ≤ py ∧ uz ≤ pz at h
  change Shape.mk (ux + (px - ux)) (uy + (py - uy)) (uz + (pz - uz)) =
    Shape.mk px py pz
  congr 1
  · exact Nat.add_sub_of_le h.1
  · exact Nat.add_sub_of_le h.2.1
  · exact Nat.add_sub_of_le h.2.2

/-- Complementing the sum by its left summand recovers the right summand. -/
@[simp] theorem add_complement_left (u v : Shape) :
    (u.add v).complement u = v := by
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  simp [add, complement]

end Shape

/-- The forty-five lexicographically ordered level-three shapes. -/
abbrev levelThreeShapes : List Shape := shapes 8

/-- The 105 positive level-four parent shapes. -/
abbrev positiveLevelFourShapes : List Shape := positiveShapes 16

/-- Ordered pairs of level-three shapes with positive coordinatewise sum.

`List.product` uses its first argument as the outer loop, exactly matching the Python generator.
-/
def levelFourPairs : List (Shape × Shape) :=
  (levelThreeShapes.product levelThreeShapes).filter fun pair ↦
    decide (pair.1.add pair.2).IsPositive

/-- Number of level-three shapes. -/
def levelThreeShapeCount : ℕ := 45

/-- Number of positive level-four parent shapes. -/
def positiveLevelFourShapeCount : ℕ := 105

/-- Number of admissible ordered level-four pairs. -/
def levelFourPairCount : ℕ := 1785

/-- Maximum number of admissible ordered pairs belonging to one positive parent. -/
def levelFourPairSlotCount : ℕ := 30

theorem levelThreeShapes_length : levelThreeShapes.length = levelThreeShapeCount := by
  decide

theorem positiveLevelFourShapes_length :
    positiveLevelFourShapes.length = positiveLevelFourShapeCount := by
  decide

theorem levelFourPairs_length : levelFourPairs.length = levelFourPairCount := by
  set_option maxRecDepth 100000 in
    decide

/-- The concrete level-three enumeration has no repeated shape. -/
theorem levelThreeShapes_nodup : levelThreeShapes.Nodup := by
  decide

/-- The concrete positive-parent enumeration has no repeated shape. -/
theorem positiveLevelFourShapes_nodup : positiveLevelFourShapes.Nodup := by
  decide

/-- No ordered pair occurs twice in the flat certificate geometry. -/
theorem levelFourPairs_nodup : levelFourPairs.Nodup := by
  exact (levelThreeShapes_nodup.product levelThreeShapes_nodup).filter _

/-- Exact, order-independent characterization of the admissible pair support. -/
theorem mem_levelFourPairs_iff {u v : Shape} :
    (u, v) ∈ levelFourPairs ↔
      u.total = 8 ∧ v.total = 8 ∧ (u.add v).IsPositive := by
  rw [levelFourPairs, List.mem_filter, List.pair_mem_product]
  simp only [decide_eq_true_eq, mem_shapes_iff_total, levelThreeShapes]
  tauto

/-- The pair stored at a flat certificate index. -/
def levelFourPair (index : Fin levelFourPairCount) : Shape × Shape :=
  levelFourPairs.get ⟨index.val, by
    rw [levelFourPairs_length]
    exact index.isLt⟩

/-- Every indexed pair belongs to the reconstructed admissible-pair list. -/
theorem levelFourPair_mem (index : Fin levelFourPairCount) :
    levelFourPair index ∈ levelFourPairs := by
  exact List.get_mem levelFourPairs _

/-- Flat pair lookup is injective because the reconstructed list has no duplicates. -/
theorem levelFourPair_injective : Function.Injective levelFourPair := by
  intro left right h
  apply Fin.ext
  apply levelFourPairs_nodup.getElem_inj_iff.mp
  exact h

/-- Positive parent of a flat ordered pair. -/
def levelFourPairParent (index : Fin levelFourPairCount) : Shape :=
  (levelFourPair index).1.add (levelFourPair index).2

/-- Every flat pair consists of two total-eight children with a positive total-sixteen parent;
the second child is exactly the complement of the first in that parent. -/
theorem levelFourPair_geometry (index : Fin levelFourPairCount) :
    (levelFourPair index).1.total = 8 ∧
      (levelFourPair index).2.total = 8 ∧
      (levelFourPairParent index).IsPositive ∧
      (levelFourPairParent index).total = 16 ∧
      (levelFourPairParent index).complement (levelFourPair index).1 =
        (levelFourPair index).2 := by
  have h := mem_levelFourPairs_iff.mp (levelFourPair_mem index)
  have hx : (levelFourPair index).1.total = 8 := h.1
  have hy : (levelFourPair index).2.total = 8 := h.2.1
  refine ⟨hx, hy, h.2.2, ?_, ?_⟩
  · rw [levelFourPairParent, Shape.add_total, hx, hy]
  · exact Shape.add_complement_left _ _

/-- The parent of every flat pair occurs in the positive level-four parent enumeration. -/
theorem levelFourPairParent_mem (index : Fin levelFourPairCount) :
    levelFourPairParent index ∈ positiveLevelFourShapes := by
  rw [show positiveLevelFourShapes = positiveShapes 16 by rfl]
  simp only [positiveShapes, List.mem_filter, decide_eq_true_eq, mem_shapes_iff_total]
  exact ⟨(levelFourPair_geometry index).2.2.2.1,
    (levelFourPair_geometry index).2.2.1⟩

/-- Positive level-four parent occupying a certificate parent index. -/
def positiveLevelFourShape (parent : Fin positiveLevelFourShapeCount) : Shape :=
  positiveLevelFourShapes.get ⟨parent.val, by
    rw [positiveLevelFourShapes_length]
    exact parent.isLt⟩

theorem positiveLevelFourShape_mem (parent : Fin positiveLevelFourShapeCount) :
    positiveLevelFourShape parent ∈ positiveLevelFourShapes := by
  exact List.get_mem positiveLevelFourShapes _

/-- Parent-segment index stored alongside each flat pair by the certificate generator. -/
def levelFourPairParentIndex (index : Fin levelFourPairCount) :
    Fin positiveLevelFourShapeCount :=
  ⟨positiveLevelFourShapes.idxOf (levelFourPairParent index), by
    rw [← positiveLevelFourShapes_length]
    exact List.idxOf_lt_length_of_mem (levelFourPairParent_mem index)⟩

/-- Looking up the reconstructed parent-segment index returns the pair's actual sum. -/
theorem positiveLevelFourShape_parentIndex (index : Fin levelFourPairCount) :
    positiveLevelFourShape (levelFourPairParentIndex index) =
      levelFourPairParent index := by
  unfold positiveLevelFourShape levelFourPairParentIndex
  exact List.idxOf_get _

/-- Ordered level-three pairs belonging to one parent.  Since the right child is forced to be the
coordinatewise complement, this scans only the 45 possible left children.  Its ordering is the
same as filtering the global left-major/right-minor pair list by `parent`. -/
def levelFourPairsForParent (parent : Shape) : List (Shape × Shape) :=
  (levelThreeShapes.filter fun left ↦ decide (left ≤ parent)).map fun left ↦
    (left, parent.complement left)

/-- Every positive parent index denotes a positive shape of total sixteen. -/
theorem positiveLevelFourShape_geometry (parent : Fin positiveLevelFourShapeCount) :
    (positiveLevelFourShape parent).IsPositive ∧
      (positiveLevelFourShape parent).total = 16 := by
  exact mem_positiveShapes (positiveLevelFourShape_mem parent)

/-- Every locally enumerated pair is an admissible global pair with the advertised parent. -/
theorem mem_levelFourPairsForParent_geometry
    {parent : Fin positiveLevelFourShapeCount} {pair : Shape × Shape}
    (hpair : pair ∈ levelFourPairsForParent (positiveLevelFourShape parent)) :
    pair ∈ levelFourPairs ∧
      pair.1.add pair.2 = positiveLevelFourShape parent := by
  simp only [levelFourPairsForParent, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hpair
  obtain ⟨left, ⟨hleft, hle⟩, rfl⟩ := hpair
  have hleftTotal : left.total = 8 := mem_shapes_total hleft
  have hparentTotal : (positiveLevelFourShape parent).total = 16 :=
    (positiveLevelFourShape_geometry parent).2
  have hrightTotal :
      ((positiveLevelFourShape parent).complement left).total = 8 := by
    rw [Shape.complement_total_of_le hle, hparentTotal, hleftTotal]
  have hsum := Shape.add_complement_of_le hle
  constructor
  · rw [mem_levelFourPairs_iff]
    exact ⟨hleftTotal, hrightTotal, hsum.symm ▸
      (positiveLevelFourShape_geometry parent).1⟩
  · exact hsum

/-- A global flat pair occurs in the local list of its reconstructed parent. -/
theorem levelFourPair_mem_parentPairs (index : Fin levelFourPairCount) :
    levelFourPair index ∈
      levelFourPairsForParent
        (positiveLevelFourShape (levelFourPairParentIndex index)) := by
  rw [positiveLevelFourShape_parentIndex]
  let pair := levelFourPair index
  have hpair := levelFourPair_geometry index
  change pair ∈ levelFourPairsForParent (levelFourPairParent index)
  simp only [levelFourPairsForParent, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  refine ⟨pair.1, ⟨?_, ?_⟩, ?_⟩
  · exact mem_shapes_iff_total.mpr hpair.1
  · exact Shape.le_add_left pair.1 pair.2
  · change (pair.1, (pair.1.add pair.2).complement pair.1) = pair
    exact Prod.ext rfl (Shape.add_complement_left pair.1 pair.2)

/-- Parent-local pair lists contain no duplicates. -/
theorem levelFourPairsForParent_nodup (parent : Shape) :
    (levelFourPairsForParent parent).Nodup := by
  apply (levelThreeShapes_nodup.filter _).map
  intro left right h
  exact congrArg Prod.fst h

/-- Thirty padded slots suffice for every positive level-four parent.  This concrete decision
checks only `105 * 45` possible parent/left-child incidences. -/
theorem levelFourPairsForParent_length_le
    (parent : Fin positiveLevelFourShapeCount) :
    (levelFourPairsForParent (positiveLevelFourShape parent)).length ≤
      levelFourPairSlotCount := by
  set_option maxRecDepth 100000 in
    decide +revert

/-- Whether a padded parent-local slot names a genuine ordered pair. -/
def levelFourPairSlotValid (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) : Prop :=
  slot.val < (levelFourPairsForParent (positiveLevelFourShape parent)).length

instance (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) :
    Decidable (levelFourPairSlotValid parent slot) := by
  unfold levelFourPairSlotValid
  infer_instance

/-- Ordered pair occupying a valid parent-local slot. -/
def levelFourPairAtSlot (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) (hslot : levelFourPairSlotValid parent slot) :
    Shape × Shape :=
  (levelFourPairsForParent (positiveLevelFourShape parent)).get ⟨slot.val, hslot⟩

/-- A valid local slot always points to a pair with the advertised parent. -/
theorem levelFourPairAtSlot_geometry
    (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) (hslot : levelFourPairSlotValid parent slot) :
    levelFourPairAtSlot parent slot hslot ∈ levelFourPairs ∧
      (levelFourPairAtSlot parent slot hslot).1.add
        (levelFourPairAtSlot parent slot hslot).2 = positiveLevelFourShape parent := by
  apply mem_levelFourPairsForParent_geometry
  exact List.get_mem _ _

/-- Convert any proved member of the flat pair list to its canonical flat index. -/
def levelFourPairIndexOf (pair : Shape × Shape) (hpair : pair ∈ levelFourPairs) :
    Fin levelFourPairCount :=
  ⟨levelFourPairs.idxOf pair, by
    rw [← levelFourPairs_length]
    exact List.idxOf_lt_length_of_mem hpair⟩

/-- Looking up a pair at its canonical flat index recovers that pair. -/
theorem levelFourPair_indexOf (pair : Shape × Shape) (hpair : pair ∈ levelFourPairs) :
    levelFourPair (levelFourPairIndexOf pair hpair) = pair := by
  unfold levelFourPair levelFourPairIndexOf
  exact List.idxOf_get _

/-- Global flat index occupying a valid parent-local slot. -/
def levelFourPairIndexAtSlot (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) (hslot : levelFourPairSlotValid parent slot) :
    Fin levelFourPairCount :=
  levelFourPairIndexOf (levelFourPairAtSlot parent slot hslot)
    (levelFourPairAtSlot_geometry parent slot hslot).1

theorem levelFourPair_indexAtSlot
    (parent : Fin positiveLevelFourShapeCount)
    (slot : Fin levelFourPairSlotCount) (hslot : levelFourPairSlotValid parent slot) :
    levelFourPair (levelFourPairIndexAtSlot parent slot hslot) =
      levelFourPairAtSlot parent slot hslot :=
  levelFourPair_indexOf _ _

/-- Unique local-slot number of a flat pair inside its parent segment. -/
def levelFourPairLocalSlot (index : Fin levelFourPairCount) : ℕ :=
  (levelFourPairsForParent
    (positiveLevelFourShape (levelFourPairParentIndex index))).idxOf
      (levelFourPair index)

theorem levelFourPairLocalSlot_lt_length (index : Fin levelFourPairCount) :
    levelFourPairLocalSlot index <
      (levelFourPairsForParent
        (positiveLevelFourShape (levelFourPairParentIndex index))).length := by
  exact List.idxOf_lt_length_of_mem (levelFourPair_mem_parentPairs index)

/-- The local slot of a flat pair lies inside the common thirty-slot padding. -/
theorem levelFourPairLocalSlot_lt_slotCount (index : Fin levelFourPairCount) :
    levelFourPairLocalSlot index < levelFourPairSlotCount :=
  lt_of_lt_of_le (levelFourPairLocalSlot_lt_length index)
    (levelFourPairsForParent_length_le (levelFourPairParentIndex index))

/-- Reading a pair back from its reconstructed parent and local slot recovers the original flat
index. -/
theorem levelFourPairIndexAtSlot_localSlot (index : Fin levelFourPairCount) :
    levelFourPairIndexAtSlot (levelFourPairParentIndex index)
      ⟨levelFourPairLocalSlot index, levelFourPairLocalSlot_lt_slotCount index⟩
      (levelFourPairLocalSlot_lt_length index) = index := by
  let parent := levelFourPairParentIndex index
  let slot : Fin levelFourPairSlotCount :=
    ⟨levelFourPairLocalSlot index, levelFourPairLocalSlot_lt_slotCount index⟩
  have hslot : levelFourPairSlotValid parent slot := by
    exact levelFourPairLocalSlot_lt_length index
  have hlocal :
      levelFourPairAtSlot parent slot hslot = levelFourPair index := by
    let entries := levelFourPairsForParent
      (positiveLevelFourShape (levelFourPairParentIndex index))
    change entries.get
        ⟨entries.idxOf (levelFourPair index), levelFourPairLocalSlot_lt_length index⟩ =
      levelFourPair index
    exact List.idxOf_get _
  apply levelFourPair_injective
  exact (levelFourPair_indexAtSlot parent slot hslot).trans hlocal

end AlgebraicComplexity.LevelFourReconstruction
