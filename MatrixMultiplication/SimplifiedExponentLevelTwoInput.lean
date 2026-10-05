/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeDefs
import MatrixMultiplication.Generated.SimplifiedVolumeSchemaDefs
import MatrixMultiplication.SimplifiedExponentRecurrenceInput

/-!
# Lightweight exact reconstruction of level-two recurrence inputs

The full simplified-volume reconstruction also develops real logarithms, entropy identities, and
the level-four scalar recurrence.  A generated level-two checker needs none of that while reading
the three sparse primary families that determine an edge.  This module is the narrow executable
boundary:

* `InputTables` retains only the `pos3A`, `pos3Alpha`, and `mu` families;
* the static split geometry reconstructs every candidate edge;
* `edgeInputWithMassThree` produces the exact three-natural-number semantic record; and
* range functions support independently checked proof slices.

No optimizer, floating-point value, real logarithm, or paper endpoint is imported here.  A later
semantic adapter proves that this reconstruction agrees with the established real-valued
recurrence.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelTwoInput

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

/-! ## Sparse exact lookup -/

/-- Lookup a target in parallel index and value lists, returning zero when it is absent. -/
def zipLookup : List Nat → List Nat → Nat → Nat
  | index :: indices, value :: values, target =>
      if index = target then value else zipLookup indices values target
  | _, _, _ => 0

/-- Recover the sparse `(ambient symbol, numerator)` row at an ambient row index. -/
def findSparseRow : List Nat → List (Array Nat) → List (Array Nat) → Nat →
    List (Nat × Nat)
  | row :: rows, support :: supports, numerator :: numerators, target =>
      if row = target then support.toList.zip numerator.toList
      else findSparseRow rows supports numerators target
  | _, _, _, _ => []

/-- Read one numerator from a sparse dyadic chunk. -/
def sparseDyadicNumeratorAt (data : SparseDyadicChunk) (row symbol : Nat) : Nat :=
  let entries := findSparseRow data.rowIndices.toList data.supportRows.toList
    data.numeratorRows.toList row
  zipLookup entries.unzip.1 entries.unzip.2 symbol

/-- Read one numerator from a family of sparse dyadic chunks. -/
def dyadicNumeratorAt (chunks : Array SparseDyadicChunk) (row symbol : Nat) : Nat :=
  (chunks.toList.map fun chunk => sparseDyadicNumeratorAt chunk row symbol).sum

/-- Read one numerator from a sparse scalar chunk. -/
def sparseScalarNumeratorAt (data : SparseScalarChunk) (index : Nat) : Nat :=
  zipLookup data.scalarIndices.toList data.numerators.toList index

/-- Read one numerator from a family of sparse scalar chunks. -/
def scalarNumeratorAt (chunks : Array SparseScalarChunk) (index : Nat) : Nat :=
  (chunks.toList.map fun chunk => sparseScalarNumeratorAt chunk index).sum

/-! ## Minimal primary tables -/

/-- The three sparse primary families needed by the positive level-two recurrence.

All other volume-certificate families are intentionally absent from this structure. -/
structure InputTables where
  pos3A : Array SparseDyadicChunk
  pos3Alpha : Array SparseDyadicChunk
  mu : Array SparseScalarChunk

/-! ## Static edge geometry -/

/-- Number of positive-level-three nodes, including the six region copies. -/
def nodeCount : Nat := 126

/-- Number of decomposition regions at each node. -/
def regionCount : Nat := 6

/-- Padded number of split slots at each node. -/
def splitSlotCount : Nat := 10

/-- Total number of padded level-two edges before positivity filtering. -/
def edgeCount : Nat := nodeCount * regionCount * splitSlotCount

/-- The total-eight positive shape belonging to a node. -/
def nodeShapeAt (node : Nat) : Shape :=
  (positiveShapes 8)[node / regionCount]?.getD default

/-- The total-four child occupying one padded split slot. -/
def splitShapeAt (node slot : Nat) : Shape :=
  (levelThreeSplits (nodeShapeAt node))[slot]?.getD default

/-- Whether a padded split slot names a genuine child. -/
def splitSlotIsValid (node slot : Nat) : Bool :=
  decide (slot < (levelThreeSplits (nodeShapeAt node)).length)

/-- Index of a shape in the certificate's total-eight enumeration. -/
def shapeEightIndex (shape : Shape) : Nat :=
  (shapes 8).idxOf shape

/-- Slot of the complementary total-four child. -/
def complementSlotAt (node slot : Nat) : Nat :=
  (levelThreeSplits (nodeShapeAt node)).idxOf
    ((nodeShapeAt node).complement (splitShapeAt node slot))

/-- Ambient cached-mass row occupied by a node. -/
def positiveNodeGlobalRow (node : Nat) : Nat :=
  shapeEightIndex (nodeShapeAt node) * regionCount + node % regionCount

/-- Node component of the flat padded edge address. -/
def edgeNode (edge : Nat) : Nat := edge / (regionCount * splitSlotCount)

/-- Region component of the flat padded edge address. -/
def edgeRegion (edge : Nat) : Nat := edge / splitSlotCount % regionCount

/-- Split-slot component of the flat padded edge address. -/
def edgeSlot (edge : Nat) : Nat := edge % splitSlotCount

/-- Whether a padded edge is a genuine positive total-four split. -/
def edgeActive (edge : Nat) : Bool :=
  let node := edgeNode edge
  let slot := edgeSlot edge
  splitSlotIsValid node slot && (splitShapeAt node slot).IsPositive

/-- The coordinate carrying the nontrivial three-letter entropy at a positive `112` leaf. -/
def edgeHeavyCoordinate (edge : Nat) : Nat :=
  let shape := splitShapeAt (edgeNode edge) (edgeSlot edge)
  if shape.x = 2 then 0 else if shape.y = 2 then 1 else 2

/-! ## Exact edge inputs -/

/-- Exact occurrence numerator of one padded edge, using an independently sealed mass-three
array.  Inactive edges have numerator zero. -/
def edgeOccurrenceNumeratorWithMassThree
    (data : InputTables) (massThree : Array Nat) (edge : Nat) : Nat :=
  if edgeActive edge then
    let node := edgeNode edge
    let region := edgeRegion edge
    let slot := edgeSlot edge
    (massThree[positiveNodeGlobalRow node]?.getD 0) *
      dyadicNumeratorAt data.pos3A node region *
      (dyadicNumeratorAt data.pos3Alpha (node * regionCount + region) slot +
        dyadicNumeratorAt data.pos3Alpha (node * regionCount + region)
          (complementSlotAt node slot))
  else 0

/-- Exact `mu` numerator attached to one flat edge. -/
def edgeMuNumerator (data : InputTables) (edge : Nat) : Nat :=
  scalarNumeratorAt data.mu edge

/-- Reconstruct the complete exact semantic record for one edge. -/
def edgeInputWithMassThree
    (data : InputTables) (massThree : Array Nat) (edge : Nat) : EdgeInput :=
  { occurrenceNumerator := edgeOccurrenceNumeratorWithMassThree data massThree edge
    muNumerator := edgeMuNumerator data edge
    heavyCoordinate := edgeHeavyCoordinate edge }

/-- All geometrically positive edges, in certificate order. -/
def activeEdges : List Nat :=
  (List.range edgeCount).filter edgeActive

/-- Reconstruct the exact semantic records of an explicit edge list. -/
def edgeInputsWithMassThree
    (data : InputTables) (massThree : Array Nat) (edges : List Nat) : List EdgeInput :=
  edges.map (edgeInputWithMassThree data massThree)

/-- Reconstruct a consecutive slice of an explicit edge list. -/
def edgeInputRangeWithMassThree
    (data : InputTables) (massThree : Array Nat) (edges : List Nat)
    (start count : Nat) : List EdgeInput :=
  ((edges.drop start).take count).map (edgeInputWithMassThree data massThree)

/-- A range starting at zero and at least as long as its edge list reconstructs the whole list.

Proof sketch: dropping zero is the identity and `List.take` is the identity under the supplied
length bound. -/
theorem edgeInputRangeWithMassThree_eq_all
    (data : InputTables) (massThree : Array Nat) (edges : List Nat) (count : Nat)
    (hlength : edges.length ≤ count) :
    edgeInputRangeWithMassThree data massThree edges 0 count =
      edgeInputsWithMassThree data massThree edges := by
  simp [edgeInputRangeWithMassThree, edgeInputsWithMassThree,
    List.take_of_length_le hlength]

/-- Splitting a consecutive range splits its exact input list by concatenation.

Proof sketch: `List.take_add` splits the prefix and `List.drop_drop` advances the starting offset;
mapping distributes over the resulting append. -/
theorem edgeInputRangeWithMassThree_add
    (data : InputTables) (massThree : Array Nat) (edges : List Nat)
    (start left right : Nat) :
    edgeInputRangeWithMassThree data massThree edges start (left + right) =
      edgeInputRangeWithMassThree data massThree edges start left ++
        edgeInputRangeWithMassThree data massThree edges (start + left) right := by
  unfold edgeInputRangeWithMassThree
  rw [List.take_add, List.map_append]
  simp only [List.drop_drop]

/-- Consecutive exact edge-input ranges with the supplied lengths. -/
def edgeInputRangesWithMassThree
    (data : InputTables) (massThree : Array Nat) (edges : List Nat) :
    Nat → List Nat → List (List EdgeInput)
  | _, [] => []
  | start, count :: counts =>
      edgeInputRangeWithMassThree data massThree edges start count ::
        edgeInputRangesWithMassThree data massThree edges (start + count) counts

/-- Flattening consecutive slices reconstructs the single slice with their total length.

Proof sketch: induction reduces the successor case to
`edgeInputRangeWithMassThree_add`. -/
theorem edgeInputRangeWithMassThree_sum_eq_flatten
    (data : InputTables) (massThree : Array Nat) (edges : List Nat)
    (start : Nat) (counts : List Nat) :
    edgeInputRangeWithMassThree data massThree edges start counts.sum =
      (edgeInputRangesWithMassThree data massThree edges start counts).flatten := by
  induction counts generalizing start with
  | nil => simp [edgeInputRangesWithMassThree, edgeInputRangeWithMassThree]
  | cons count counts ih =>
      simp only [List.sum_cons, edgeInputRangesWithMassThree, List.flatten_cons]
      rw [edgeInputRangeWithMassThree_add, ih]

end MatrixMultiplication.SimplifiedExponentLevelTwoInput
