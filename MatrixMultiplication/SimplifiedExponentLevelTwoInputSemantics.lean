/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelTwoInput
import MatrixMultiplication.SimplifiedExponentRecurrence

/-!
# Semantic bridge for the lightweight level-two input recurrence

`SimplifiedExponentLevelTwoInput` duplicates only the executable natural-number fragment of the
older full recurrence so generated input certificates do not import real entropy or unrelated
primary-table families.  This module proves that the lightweight computation is not a second
semantics: after projecting a full primary table to its three relevant families, every edge record
is definitionally the same record produced by `SimplifiedExponentRecurrence.Chunked`.

The bridge is generic in the primary tables, cached mass vector, and edge address.  Result-specific
certificates therefore check sparse arithmetic through the lightweight implementation once and
transport it to the real-valued recurrence without re-running the large computation.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelTwoInput

/-- Forget the four primary-table families that the positive level-two recurrence never reads. -/
def ofPrimaryTables
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables) : InputTables where
  pos3A := data.pos3A
  pos3Alpha := data.pos3Alpha
  mu := data.mu

/-! ## Lookup equivalence -/

/-- The two parallel-list lookup implementations agree. -/
theorem zipLookup_eq (indices values : List Nat) (target : Nat) :
    zipLookup indices values target =
      MatrixMultiplication.SimplifiedVolumeReconstruction.zipLookup indices values target := by
  induction indices generalizing values with
  | nil => rfl
  | cons index indices ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          by_cases h : index = target
          · simp [zipLookup,
              MatrixMultiplication.SimplifiedVolumeReconstruction.zipLookup, h]
          · simp [zipLookup,
              MatrixMultiplication.SimplifiedVolumeReconstruction.zipLookup, h, ih]

/-- The two sparse-row searches agree. -/
theorem findSparseRow_eq (rows : List Nat) (supports numerators : List (Array Nat))
    (target : Nat) :
    findSparseRow rows supports numerators target =
      MatrixMultiplication.SimplifiedVolumeReconstruction.findSparseRow
        rows supports numerators target := by
  induction rows generalizing supports numerators with
  | nil => rfl
  | cons row rows ih =>
      cases supports with
      | nil => rfl
      | cons support supports =>
          cases numerators with
          | nil => rfl
          | cons numerator numerators =>
              by_cases h : row = target
              · simp [findSparseRow,
                  MatrixMultiplication.SimplifiedVolumeReconstruction.findSparseRow, h]
              · simp [findSparseRow,
                  MatrixMultiplication.SimplifiedVolumeReconstruction.findSparseRow, h, ih]

/-- Sparse dyadic lookup agrees on one chunk. -/
theorem sparseDyadicNumeratorAt_eq
    (data : MatrixMultiplication.Generated.SimplifiedVolume.SparseDyadicChunk)
    (row symbol : Nat) :
    sparseDyadicNumeratorAt data row symbol =
      MatrixMultiplication.SimplifiedVolumeReconstruction.sparseDyadicNumeratorAt
        data row symbol := by
  unfold sparseDyadicNumeratorAt
    MatrixMultiplication.SimplifiedVolumeReconstruction.sparseDyadicNumeratorAt
    MatrixMultiplication.SimplifiedVolumeReconstruction.sparseDyadicRowEntries
  rw [findSparseRow_eq, zipLookup_eq]

/-- Sparse dyadic lookup agrees across a chunk family. -/
theorem dyadicNumeratorAt_eq
    (chunks : Array MatrixMultiplication.Generated.SimplifiedVolume.SparseDyadicChunk)
    (row symbol : Nat) :
    dyadicNumeratorAt chunks row symbol =
      MatrixMultiplication.SimplifiedVolumeReconstruction.dyadicNumeratorAt
        chunks row symbol := by
  unfold dyadicNumeratorAt
    MatrixMultiplication.SimplifiedVolumeReconstruction.dyadicNumeratorAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro chunk _
  exact sparseDyadicNumeratorAt_eq chunk row symbol

/-- Sparse scalar lookup agrees on one chunk. -/
theorem sparseScalarNumeratorAt_eq
    (data : MatrixMultiplication.Generated.SimplifiedVolume.SparseScalarChunk)
    (index : Nat) :
    sparseScalarNumeratorAt data index =
      MatrixMultiplication.SimplifiedVolumeReconstruction.sparseScalarNumeratorAt
        data index := by
  unfold sparseScalarNumeratorAt
    MatrixMultiplication.SimplifiedVolumeReconstruction.sparseScalarNumeratorAt
  exact zipLookup_eq _ _ _

/-- Sparse scalar lookup agrees across a chunk family. -/
theorem scalarNumeratorAt_eq
    (chunks : Array MatrixMultiplication.Generated.SimplifiedVolume.SparseScalarChunk)
    (index : Nat) :
    scalarNumeratorAt chunks index =
      MatrixMultiplication.SimplifiedVolumeReconstruction.scalarNumeratorAt chunks index := by
  unfold scalarNumeratorAt
    MatrixMultiplication.SimplifiedVolumeReconstruction.scalarNumeratorAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro chunk _
  exact sparseScalarNumeratorAt_eq chunk index

/-! ## Geometry equivalence -/

/-- Both implementations assign the same positive parent shape to a node. -/
theorem nodeShapeAt_eq (node : Nat) :
    nodeShapeAt node = MatrixMultiplication.SimplifiedVolumeReconstruction.nodeShapeAt node := by
  rfl

/-- Both implementations assign the same child shape to a padded split slot. -/
theorem splitShapeAt_eq (node slot : Nat) :
    splitShapeAt node slot =
      MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt node slot := by
  unfold splitShapeAt MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
  rw [nodeShapeAt_eq]

/-- Both implementations recognize the same valid split slots. -/
theorem splitSlotIsValid_eq (node slot : Nat) :
    splitSlotIsValid node slot =
      MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid node slot := by
  unfold splitSlotIsValid MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid
  rw [nodeShapeAt_eq]

/-- Both implementations find the same complementary split slot. -/
theorem complementSlotAt_eq (node slot : Nat) :
    complementSlotAt node slot =
      MatrixMultiplication.SimplifiedVolumeReconstruction.complementSlotAt node slot := by
  unfold complementSlotAt MatrixMultiplication.SimplifiedVolumeReconstruction.complementSlotAt
  rw [nodeShapeAt_eq, splitShapeAt_eq]

/-- Both implementations use the same ambient cached-mass row. -/
theorem positiveNodeGlobalRow_eq (node : Nat) :
    positiveNodeGlobalRow node =
      MatrixMultiplication.SimplifiedVolumeReconstruction.positiveNodeGlobalRow node := by
  unfold positiveNodeGlobalRow
    MatrixMultiplication.SimplifiedVolumeReconstruction.positiveNodeGlobalRow shapeEightIndex
    MatrixMultiplication.SimplifiedVolumeReconstruction.shapeEightIndex
  rw [nodeShapeAt_eq]
  rfl

/-- Both implementations decode the same node address. -/
theorem edgeNode_eq (edge : Nat) :
    edgeNode edge = MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge := by
  rfl

/-- Both implementations decode the same region address. -/
theorem edgeRegion_eq (edge : Nat) :
    edgeRegion edge = MatrixMultiplication.SimplifiedVolumeReconstruction.edgeRegion edge := by
  rfl

/-- Both implementations decode the same split-slot address. -/
theorem edgeSlot_eq (edge : Nat) :
    edgeSlot edge = MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge := by
  rfl

/-- Both implementations recognize the same active edges. -/
theorem edgeActive_eq (edge : Nat) :
    edgeActive edge = MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeActive edge := by
  unfold edgeActive MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeActive
  simp only [edgeNode_eq, edgeSlot_eq, splitSlotIsValid_eq, splitShapeAt_eq]

/-- Both implementations identify the same heavy coordinate. -/
theorem edgeHeavyCoordinate_eq (edge : Nat) :
    edgeHeavyCoordinate edge =
      (MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeHeavyCoordinate edge).val := by
  unfold edgeHeavyCoordinate
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeHeavyCoordinate
    MatrixMultiplication.SimplifiedExponentRecurrence.levelTwoHeavyCoordinate
  rw [edgeNode_eq, edgeSlot_eq, splitShapeAt_eq]
  by_cases hx :
      (MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge)
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge)).x = 2
  · simp [hx]
  · by_cases hy :
        (MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
          (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge)
          (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge)).y = 2
    · simp [hx, hy]
    · simp [hx, hy]

/-- The lightweight checker enumerates exactly the semantic recurrence's active edges.

Proof sketch: both lists filter the same finite range, and `edgeActive_eq` identifies the Boolean
predicate pointwise. -/
theorem activeEdges_eq :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges = activeEdges := by
  unfold MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.activeEdges activeEdges
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeCount
    MatrixMultiplication.SimplifiedVolumeReconstruction.edgeCount edgeCount nodeCount regionCount
    splitSlotCount
  rfl

/-- The lightweight and full recurrences compute the same exact occurrence numerator. -/
theorem edgeOccurrenceNumeratorWithMassThree_eq
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array Nat) (edge : Nat) :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeOccurrenceNumeratorWithMassThree
        data massThree edge =
      edgeOccurrenceNumeratorWithMassThree (ofPrimaryTables data) massThree edge := by
  unfold MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeOccurrenceNumeratorWithMassThree
    edgeOccurrenceNumeratorWithMassThree
  rw [edgeActive_eq]
  unfold MatrixMultiplication.SimplifiedVolumeReconstruction.levelTwoMassNumeratorWithMass3
  simp only [ofPrimaryTables, regionCount, positiveNodeGlobalRow_eq, edgeNode_eq,
    edgeRegion_eq, edgeSlot_eq, complementSlotAt_eq, dyadicNumeratorAt_eq]

/-- The lightweight and full recurrences read the same exact `mu` numerator. -/
theorem edgeMuNumerator_eq
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (edge : Nat) :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeMuNumerator data edge =
      edgeMuNumerator (ofPrimaryTables data) edge := by
  unfold MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeMuNumerator
    edgeMuNumerator ofPrimaryTables
  exact (scalarNumeratorAt_eq data.mu edge).symm

/-- The lightweight and full recurrences compute the same exact record at every edge.

Proof sketch: unfold the two executable paths.  Their sparse lookups and shape arithmetic are
definitionally identical; `ofPrimaryTables` supplies exactly the three fields that occur. -/
theorem edgeInputWithMassThree_eq
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array Nat) (edge : Nat) :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputWithMassThree
        data massThree edge =
      edgeInputWithMassThree (ofPrimaryTables data) massThree edge := by
  unfold MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputWithMassThree
    edgeInputWithMassThree
  rw [edgeOccurrenceNumeratorWithMassThree_eq, edgeMuNumerator_eq,
    edgeHeavyCoordinate_eq]

/-- The two implementations consequently agree on every explicit finite edge list. -/
theorem edgeInputsWithMassThree_eq
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array Nat) (edges : List Nat) :
    edges.map
        (MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputWithMassThree
          data massThree) =
      edgeInputsWithMassThree (ofPrimaryTables data) massThree edges := by
  unfold edgeInputsWithMassThree
  apply List.map_congr_left
  intro edge _
  exact edgeInputWithMassThree_eq data massThree edge

/-- The two implementations agree on every consecutive edge-list range. -/
theorem edgeInputRangeWithMassThree_eq
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array Nat) (edges : List Nat) (start count : Nat) :
    MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputRangeWithMassThree
        data massThree edges start count =
      edgeInputRangeWithMassThree (ofPrimaryTables data) massThree edges start count := by
  unfold MatrixMultiplication.SimplifiedExponentRecurrence.Chunked.edgeInputRangeWithMassThree
    edgeInputRangeWithMassThree
  apply List.map_congr_left
  intro edge _
  exact edgeInputWithMassThree_eq data massThree edge

end MatrixMultiplication.SimplifiedExponentLevelTwoInput
