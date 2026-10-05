/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
import MatrixMultiplication.SimplifiedExponentLevelFourRowDefs

/-!
# Exact level-four retained-exponent recurrence

This module is the certificate-independent semantic recurrence for positive level-four
constituents.  It deliberately separates two exact layers:

* `reconstructedBetaThreeRows` reconstructs every global depth-three complete-split row from the
  primary dyadic tables, including the positive regional mixture and the nonpositive zero laws;
* `localRowsFrom` consumes any serialized copy of those rows to build the level-four constituent
  data.  Generated clients prove their compact serialization equal to
  `reconstructedBetaThreeRows` once, then reuse it for every parent.

The ordered top split has denominator `2^20`, a depth-three child row has denominator `2^48`, and
the level-four parent row has denominator `2^(20+48+48) = 2^116`.  Boundary and compatibility-cell
rows are represented homogeneously at that same denominator.  In particular, the first-row
numerators are literally `split * child * 2^48`; after extracting powers of two this is the
`weighted_entropy(split * child, 68)` representation used by the numerical evaluator.

The positive beta-three reconstruction is parameterized by the quotient slot map.  Historical
declarations remain sorted-pair specializations; generated certificate families must use the
explicit `For` constructors when their quotient differs.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

def outerBits : ℕ := 0
def referenceBits : ℕ := 20
def compatibilityExtraBits : ℕ := 96
def coordinateCount : ℕ := 9
def parentCount : ℕ := positiveLevelFourShapeCount
def pairSlotCount : ℕ := levelFourPairSlotCount
def childSupportWidth : ℕ := levelThreeSupportWidth
def parentSupportWidth : ℕ := 1107
def parentWordLength : ℕ := 8
def childRowRescale : ℕ := 2 ^ childBits
def betaThreeZeroRescale : ℕ := 2 ^ 36

/-- Physical coordinates assigned to the three logical tensor roles in one region. -/
structure CoordinateOrder where
  x : Fin 3
  y : Fin 3
  z : Fin 3
  deriving DecidableEq, Repr

/-- The three physical coordinates in an order are pairwise distinct. -/
def CoordinateOrder.IsPermutation (order : CoordinateOrder) : Prop :=
  order.x ≠ order.y ∧ order.x ≠ order.z ∧ order.y ≠ order.z

/-- Positive integer factors for one level-four maximum-entropy dual. -/
structure DualWeights where
  x : Fin coordinateCount → ℕ
  y : Fin coordinateCount → ℕ
  z : Fin coordinateCount → ℕ

namespace DualWeights

/-- Select the factor row belonging to one physical coordinate. -/
def forCoordinate (weights : DualWeights) (coordinate : Fin 3) :
    Fin coordinateCount → ℕ :=
  if coordinate = 0 then weights.x else if coordinate = 1 then weights.y else weights.z

end DualWeights

/-! ## Exact global depth-three complete-split rows -/

/-- The positive-node index attached to a positive global `(shape, incoming-region)` row.
For nonpositive shapes the value is harmless and is never selected. -/
def positiveNodeAtGlobalRow (row : ℕ) : ℕ :=
  (positiveShapes 8).idxOf (zeroThreeShapeAt row) * regionCount + row % regionCount

/-- A nonpositive depth-three row before the exact `2^36` lift to denominator `2^48`.

The complement branch is a target-side lookup through the digitwise-complement involution.  The
explicit support guard prevents a padded slot from being mapped back to a genuine atom. -/
def zeroBetaThreeBaseNumerator (data : PrimaryTables)
    (row coordinate symbol : ℕ) : ℕ :=
  let shape := zeroThreeShapeAt row
  if coordinate = zeroCoordinate shape then
    if symbol = 0 then
      MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localDenominator
    else 0
  else if coordinate = primaryZeroLawCoordinate shape then
    dyadicNumeratorAt data.zero3 row symbol
  else if coordinate = complementZeroLawCoordinate shape then
    if symbol <
        (ternarySupportCodes levelThreeWordLength
          (shapeCoordinate shape coordinate)).length then
      dyadicNumeratorAt data.zero3 row
        (ternaryComplementSlot levelThreeWordLength
          (shapeCoordinate shape coordinate) symbol)
    else 0
  else 0

/-- Exact quotient-parametric global depth-three numerator at denominator `2^48`.

Positive rows mix the six `2^36` conditional regional rows with the `2^12` `A_3` law.
Nonpositive rows lift the supplied `2^12` zero law by `2^36`. -/
def betaThreeGlobalNumeratorFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (row coordinate symbol : ℕ) : ℕ :=
  let shape := zeroThreeShapeAt row
  if shape.IsPositive then
    ((List.range regionCount).map fun outputRegion ↦
      dyadicNumeratorAt data.pos3A (positiveNodeAtGlobalRow row) outputRegion *
        quotientBetaThreeRegionNumerator supportSlot data
          (positiveNodeAtGlobalRow row) outputRegion coordinate symbol).sum
  else
    zeroBetaThreeBaseNumerator data row coordinate symbol * betaThreeZeroRescale

/-- Sorted-pair specialization of the global depth-three numerator. -/
def betaThreeGlobalNumerator (data : PrimaryTables)
    (row coordinate symbol : ℕ) : ℕ :=
  betaThreeGlobalNumeratorFor sortedPairSupportSlot data row coordinate symbol

/-- Scatter one quotient-pushed depth-two word pair into its depth-three support slot. -/
def addBetaThreeRegionContributionFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate slot leftSymbol rightSymbol : ℕ)
    (row : Array ℕ) : Array ℕ :=
  if splitSlotIsValid node slot then
    let alpha := dyadicNumeratorAt data.pos3Alpha
      (node * regionCount + outputRegion) slot
    if alpha = 0 then row
    else
      let leftShape := splitShapeAt node slot
      let rightSlot := complementSlotAt node slot
      let rightShape := splitShapeAt node rightSlot
      let leftCode := ternarySupportCodeAt levelTwoWordLength
        (shapeCoordinate leftShape coordinate) leftSymbol
      let rightCode := ternarySupportCodeAt levelTwoWordLength
        (shapeCoordinate rightShape coordinate) rightSymbol
      let parentSlot := (ternarySupportCodes levelThreeWordLength
        (shapeCoordinate (nodeShapeAt node) coordinate)).idxOf
          (leftCode * 3 ^ levelTwoWordLength + rightCode)
      let numerator := alpha *
          quotientBetaTwoNumerator supportSlot data
            node outputRegion slot coordinate leftSymbol *
          quotientBetaTwoNumerator supportSlot data
            node outputRegion rightSlot coordinate rightSymbol
      if parentSlot < row.size then row.modify parentSlot (· + numerator) else row
  else row

/-- Sorted-pair specialization of one sparse regional contribution. -/
def addBetaThreeRegionContribution (data : PrimaryTables)
    (node outputRegion coordinate slot leftSymbol rightSymbol : ℕ)
    (row : Array ℕ) : Array ℕ :=
  addBetaThreeRegionContributionFor sortedPairSupportSlot data
    node outputRegion coordinate slot leftSymbol rightSymbol row

/-- The quotient-parametric positive regional recurrence, evaluated by sparse scatter. -/
def betaThreeRegionRowByScatterFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) : Array ℕ :=
  ((List.range 10).foldl (fun row slot ↦
    (List.range levelTwoSupportWidth).foldl (fun row leftSymbol ↦
      (List.range levelTwoSupportWidth).foldl (fun row rightSymbol ↦
        addBetaThreeRegionContributionFor supportSlot data node outputRegion coordinate slot
          leftSymbol rightSymbol row) row) row)
    (Array.replicate childSupportWidth 0))

/-- Apply all depth-two symbol-pair contributions belonging to one split slot.

This is the reusable checkpoint boundary inside the regional sparse scatter.  It is definitionally
the body of one iteration of `betaThreeRegionRowByScatterFor`'s outer fold. -/
def addBetaThreeRegionSlotFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) (row : Array ℕ) (slot : ℕ) : Array ℕ :=
  (List.range levelTwoSupportWidth).foldl (fun row leftSymbol ↦
    (List.range levelTwoSupportWidth).foldl (fun row rightSymbol ↦
      addBetaThreeRegionContributionFor supportSlot data node outputRegion coordinate slot
        leftSymbol rightSymbol row) row) row

/-- Sparse child row after split slots `0,…,4`. -/
def betaThreeRegionRowByScatterFirstSlotsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node outputRegion coordinate : ℕ) : Array ℕ :=
  (List.range 5).foldl
    (addBetaThreeRegionSlotFor supportSlot data node outputRegion coordinate)
    (Array.replicate childSupportWidth 0)

/-- Continue a sparse child row through split slots `5,…,9`. -/
def betaThreeRegionRowByScatterRemainingSlotsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node outputRegion coordinate : ℕ)
    (initial : Array ℕ) : Array ℕ :=
  (List.range 5).foldl (fun row offset ↦
    addBetaThreeRegionSlotFor supportSlot data node outputRegion coordinate row (offset + 5))
    initial

/-- The ten-slot sparse scatter is the remaining-slot fold applied to the first-slot fold.

Proof sketch: unfold all three folds.  `List.range 10` and the concatenation of the two shifted
five-element ranges reduce to the same nested slot updates in order. -/
theorem betaThreeRegionRowByScatterFor_eq_slotHalves
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) :
    betaThreeRegionRowByScatterFor supportSlot data node outputRegion coordinate =
      betaThreeRegionRowByScatterRemainingSlotsFor supportSlot data node outputRegion coordinate
        (betaThreeRegionRowByScatterFirstSlotsFor supportSlot data node outputRegion coordinate) := by
  rfl

/-- Assemble a regional child row from independently checked five-slot halves.

Proof sketch: rewrite the semantic ten-slot scatter as the two five-slot folds, then substitute
the submitted midpoint and final-row equalities. -/
theorem betaThreeRegionRowByScatterFor_eq_of_slotHalves
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) (middle expected : Array ℕ)
    (hfirst :
      betaThreeRegionRowByScatterFirstSlotsFor supportSlot data node outputRegion coordinate =
        middle)
    (hsecond :
      betaThreeRegionRowByScatterRemainingSlotsFor supportSlot data node outputRegion coordinate
        middle = expected) :
    betaThreeRegionRowByScatterFor supportSlot data node outputRegion coordinate = expected := by
  rw [betaThreeRegionRowByScatterFor_eq_slotHalves, hfirst, hsecond]

/-- Sorted-pair sparse-scatter regional row. -/
def betaThreeRegionRowByScatter (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) : Array ℕ :=
  betaThreeRegionRowByScatterFor sortedPairSupportSlot data node outputRegion coordinate

/-- Add one quotient-pushed, `A_3`-scaled conditional row to a positive global row. -/
def addPositiveBetaThreeRegionFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node coordinate : ℕ)
    (row : Array ℕ) (outputRegion : ℕ) : Array ℕ :=
  let scale := dyadicNumeratorAt data.pos3A node outputRegion
  if scale = 0 then row
  else
    let child := betaThreeRegionRowByScatterFor supportSlot data node outputRegion coordinate
    (List.range childSupportWidth).foldl (fun row symbol ↦
      row.modify symbol (· + scale * (child[symbol]?.getD 0))) row

/-- Add an already reconstructed child row with the region's `A₃` scale.

Generated certificates use this definition to keep sparse child reconstruction and the final
nineteen-symbol update in different kernel modules. -/
def addPositiveBetaThreeRegionFromChildFor (data : PrimaryTables) (node _coordinate : ℕ)
    (row child : Array ℕ) (outputRegion : ℕ) : Array ℕ :=
  let scale := dyadicNumeratorAt data.pos3A node outputRegion
  if scale = 0 then row
  else
    (List.range childSupportWidth).foldl (fun row symbol ↦
      row.modify symbol (· + scale * (child[symbol]?.getD 0))) row

/-- Supplying the exact sparse child row recovers the original positive regional update.

Proof sketch: unfold both update definitions.  After substituting the child-row equality, their
scale test and symbol fold are definitionally identical. -/
theorem addPositiveBetaThreeRegionFor_eq_fromChildFor
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) (row child : Array ℕ)
    (hchild :
      betaThreeRegionRowByScatterFor supportSlot data node outputRegion coordinate = child) :
    addPositiveBetaThreeRegionFor supportSlot data node coordinate row outputRegion =
      addPositiveBetaThreeRegionFromChildFor data node coordinate row child outputRegion := by
  unfold addPositiveBetaThreeRegionFor addPositiveBetaThreeRegionFromChildFor
  rw [hchild]

/-- Assemble a positive regional update from separate child-row and scaled-update certificates. -/
theorem addPositiveBetaThreeRegionFor_eq_of_child
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node outputRegion coordinate : ℕ) (row child expected : Array ℕ)
    (hchild :
      betaThreeRegionRowByScatterFor supportSlot data node outputRegion coordinate = child)
    (hscaled :
      addPositiveBetaThreeRegionFromChildFor data node coordinate row child outputRegion =
        expected) :
    addPositiveBetaThreeRegionFor supportSlot data node coordinate row outputRegion = expected := by
  calc
    addPositiveBetaThreeRegionFor supportSlot data node coordinate row outputRegion =
        addPositiveBetaThreeRegionFromChildFor data node coordinate row child outputRegion :=
      addPositiveBetaThreeRegionFor_eq_fromChildFor supportSlot data node outputRegion coordinate
        row child hchild
    _ = expected := hscaled

/-- Sorted-pair specialization of the positive regional accumulator. -/
def addPositiveBetaThreeRegion (data : PrimaryTables) (node coordinate : ℕ)
    (row : Array ℕ) (outputRegion : ℕ) : Array ℕ :=
  addPositiveBetaThreeRegionFor sortedPairSupportSlot data node coordinate row outputRegion

/-- Exact quotient-parametric positive coordinate row from six regional scatters. -/
def positiveBetaThreeCoordinateRowFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (globalRow coordinate : ℕ) : Array ℕ :=
  ((List.range regionCount).foldl
    (addPositiveBetaThreeRegionFor supportSlot data
      (positiveNodeAtGlobalRow globalRow) coordinate)
    (Array.replicate childSupportWidth 0))

/-- First three regional contributions to one positive depth-three coordinate row.

This bounded checkpoint is intended for generated certificates.  It exposes a midpoint in the
six-region fold without changing the semantic definition `positiveBetaThreeCoordinateRowFor`. -/
def positiveBetaThreeCoordinateFirstHalfFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (globalRow coordinate : ℕ) : Array ℕ :=
  ((List.range 3).foldl
    (addPositiveBetaThreeRegionFor supportSlot data
      (positiveNodeAtGlobalRow globalRow) coordinate)
    (Array.replicate childSupportWidth 0))

/-- Last three regional contributions, starting from a certified midpoint row.

The local range `0,1,2` is shifted to the semantic output regions `3,4,5`. -/
def positiveBetaThreeCoordinateSecondHalfFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (globalRow coordinate : ℕ) (initial : Array ℕ) : Array ℕ :=
  ((List.range 3).foldl
    (fun row outputRegion ↦
      addPositiveBetaThreeRegionFor supportSlot data
        (positiveNodeAtGlobalRow globalRow) coordinate row (outputRegion + 3))
    initial)

/-- The original six-region coordinate recurrence is the second half applied to the first half.

Proof sketch: both sides reduce to the same six nested calls of
`addPositiveBetaThreeRegionFor`, in output-region order `0,1,2,3,4,5`. -/
theorem positiveBetaThreeCoordinateRowFor_eq_halves
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (globalRow coordinate : ℕ) :
    positiveBetaThreeCoordinateRowFor supportSlot data globalRow coordinate =
      positiveBetaThreeCoordinateSecondHalfFor supportSlot data globalRow coordinate
        (positiveBetaThreeCoordinateFirstHalfFor supportSlot data globalRow coordinate) := by
  rfl

/-- Assemble a positive coordinate row from independently checked first- and second-half rows.

Generated clients use this theorem to keep every exact kernel reduction below a fixed memory
budget: the first certificate computes regions `0..2`, and the second computes regions `3..5`
from the submitted midpoint. -/
theorem positiveBetaThreeCoordinateRowFor_eq_of_halves
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (globalRow coordinate : ℕ) (middle expected : Array ℕ)
    (hfirst :
      positiveBetaThreeCoordinateFirstHalfFor supportSlot data globalRow coordinate = middle)
    (hsecond :
      positiveBetaThreeCoordinateSecondHalfFor supportSlot data globalRow coordinate middle =
        expected) :
    positiveBetaThreeCoordinateRowFor supportSlot data globalRow coordinate = expected := by
  rw [positiveBetaThreeCoordinateRowFor_eq_halves, hfirst, hsecond]

/-- Sorted-pair specialization of a positive global coordinate row. -/
def positiveBetaThreeCoordinateRow (data : PrimaryTables)
    (globalRow coordinate : ℕ) : Array ℕ :=
  positiveBetaThreeCoordinateRowFor sortedPairSupportSlot data globalRow coordinate

/-- One quotient-parametric serialized global row, padded to width nineteen. -/
def betaThreeGlobalRowFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (row : ℕ) : Array (Array ℕ) :=
  let shape := zeroThreeShapeAt row
  if shape.IsPositive then
    ((List.range 3).map (positiveBetaThreeCoordinateRowFor supportSlot data row)).toArray
  else
    ((List.range 3).map fun coordinate ↦
      ((List.range childSupportWidth).map fun symbol ↦
        zeroBetaThreeBaseNumerator data row coordinate symbol * betaThreeZeroRescale).toArray).toArray

/-- A positive global row can be certified one coordinate at a time.

This is the compositional boundary used by generated checkers.  Recomputing all eighteen
coordinates of a six-row shape in one `decide` expression creates a large interpreter term;
sealing the three coordinate equalities separately keeps both memory and rebuild cost bounded.

Proof sketch: the positivity hypothesis selects the positive branch of `betaThreeGlobalRowFor`;
the concrete enumeration `List.range 3 = [0, 1, 2]` then exposes exactly the three supplied
coordinate equalities. -/
theorem betaThreeGlobalRowFor_eq_of_positive
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables) (row : ℕ)
    (expectedX expectedY expectedZ : Array ℕ)
    (hpositive : (zeroThreeShapeAt row).IsPositive)
    (hx : positiveBetaThreeCoordinateRowFor supportSlot data row 0 = expectedX)
    (hy : positiveBetaThreeCoordinateRowFor supportSlot data row 1 = expectedY)
    (hz : positiveBetaThreeCoordinateRowFor supportSlot data row 2 = expectedZ) :
    betaThreeGlobalRowFor supportSlot data row = #[expectedX, expectedY, expectedZ] := by
  unfold betaThreeGlobalRowFor
  rw [if_pos hpositive]
  change #[positiveBetaThreeCoordinateRowFor supportSlot data row 0,
    positiveBetaThreeCoordinateRowFor supportSlot data row 1,
    positiveBetaThreeCoordinateRowFor supportSlot data row 2] = _
  rw [hx, hy, hz]

/-- Sorted-pair specialization of one serialized global row. -/
def betaThreeGlobalRow (data : PrimaryTables) (row : ℕ) : Array (Array ℕ) :=
  betaThreeGlobalRowFor sortedPairSupportSlot data row

/-- Number of global `(shape, incoming-region)` depth-three rows. -/
def betaThreeGlobalRowCount : ℕ := 45 * regionCount

/-- Six quotient-parametric incoming-region rows of one fixed depth-three shape. -/
def reconstructedBetaThreeShapeRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (shapeIndex : ℕ) :
    List (Array (Array ℕ)) :=
  (List.range regionCount).map fun incomingRegion ↦
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + incomingRegion)

/-- Assemble one shape cache from six independently certified incoming-region rows.

Proof sketch: unfold the fixed six-element map and rewrite each row with its submitted equality.
No primary table is evaluated by this assembly lemma. -/
theorem reconstructedBetaThreeShapeRowsFor_eq_of_rows
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables) (shapeIndex : ℕ)
    (row0 row1 row2 row3 row4 row5 : Array (Array ℕ))
    (h0 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 0) = row0)
    (h1 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 1) = row1)
    (h2 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 2) = row2)
    (h3 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 3) = row3)
    (h4 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 4) = row4)
    (h5 : betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 5) = row5) :
    reconstructedBetaThreeShapeRowsFor supportSlot data shapeIndex =
      [row0, row1, row2, row3, row4, row5] := by
  unfold reconstructedBetaThreeShapeRowsFor
  change [betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 0),
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 1),
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 2),
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 3),
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 4),
    betaThreeGlobalRowFor supportSlot data (shapeIndex * regionCount + 5)] = _
  rw [h0, h1, h2, h3, h4, h5]

/-- Sorted-pair specialization of a fixed shape's six incoming-region rows. -/
def reconstructedBetaThreeShapeRows (data : PrimaryTables) (shapeIndex : ℕ) :
    List (Array (Array ℕ)) :=
  reconstructedBetaThreeShapeRowsFor sortedPairSupportSlot data shapeIndex

/-- A generated or reconstructed constant-time cache of the global depth-three rows. -/
abbrev BetaThreeRows := Array (Array (Array ℕ))

/-- Exact quotient-parametric serialization of all global depth-three rows. -/
def reconstructedBetaThreeRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) : BetaThreeRows :=
  ((List.range 45).flatMap (reconstructedBetaThreeShapeRowsFor supportSlot data)).toArray

/-- Sorted-pair specialization of the complete global beta-three serialization. -/
def reconstructedBetaThreeRows (data : PrimaryTables) : BetaThreeRows :=
  reconstructedBetaThreeRowsFor sortedPairSupportSlot data

/-- Total lookup in a serialized depth-three table. -/
def betaThreeNumeratorFrom (rows : BetaThreeRows)
    (row coordinate symbol : ℕ) : ℕ :=
  ((rows[row]?.getD #[])[coordinate]?.getD #[])[symbol]?.getD 0

/-! ## Level-four ordered-pair geometry and top masses -/

/-- Number of serialized positive top-branch atoms. -/
def topBranchFlatCount : ℕ := regionCount * regionCount * topPairCount

/-- Number of `(root, region)` rows in the positive top cache. -/
def topBranchRowCount : ℕ := regionCount * regionCount

/-- Number of padded leaf chunks in one positive top row. -/
def topBranchChunkCount : ℕ := (topPairCount + topBranchChunkSize - 1) / topBranchChunkSize

/-- Scatter one sparse ambient top entry into the dense positive-branch cache. -/
def addTopBranchEntry (rows : TopBranchRows) (entry : ℕ × ℕ) : TopBranchRows :=
  if topZeroAtomCount ≤ entry.1 then
    let flat := entry.1 - topZeroAtomCount
    let row := flat / topPairCount
    let pair := flat % topPairCount
    let chunk := pair / topBranchChunkSize
    let offset := pair % topBranchChunkSize
    if row < rows.size then
      rows.modify row fun chunks ↦
        if chunk < chunks.size then
          chunks.modify chunk fun values ↦
            if offset < values.size then values.modify offset (· + entry.2) else values
        else chunks
    else rows
  else rows

/-- Exact dense positive top table reconstructed in one pass from the sparse primary mass. -/
def reconstructedTopBranchRows (data : PrimaryTables) : TopBranchRows :=
  ((massEntries data.top).foldl addTopBranchEntry
    (Array.replicate topBranchRowCount
      (Array.replicate topBranchChunkCount (Array.replicate topBranchChunkSize 0))))

/-- Certificate-order valid local pair slots for a positive parent. -/
def validSlots (parent : ℕ) : List ℕ :=
  (List.range pairSlotCount).filter fun slot ↦
    decide (slot < (levelFourPairsForParent (parentShapeAt parent)).length)

/-- Global flat index of the reversed ordered split. -/
def reversePairIndexAt (parent slot : ℕ) : ℕ :=
  levelFourPairs.idxOf ((pairAt parent slot).2, (pairAt parent slot).1)

/-- Ordered split numerator plus the numerator of its reversed occurrence. -/
def orderedTopSplitNumerator (top : TopBranchRows)
    (root region parent slot : ℕ) : ℕ :=
  topSplitNumerator top root region parent slot +
    topNumeratorFrom top root region (reversePairIndexAt parent slot)

/-- Structural split support in logical coordinate order. -/
def splitSupport (order : CoordinateOrder) (parent : ℕ) :
    List (CoordinateTriple coordinateCount) :=
  (validSlots parent).map fun slot ↦
    let shape := (pairAt parent slot).1
    { x := ⟨shapeCoordinate shape order.x % coordinateCount, Nat.mod_lt _ (by decide)⟩
      y := ⟨shapeCoordinate shape order.y % coordinateCount, Nat.mod_lt _ (by decide)⟩
      z := ⟨shapeCoordinate shape order.z % coordinateCount, Nat.mod_lt _ (by decide)⟩ }

/-- Ordered reference-law row for one level-four parent. -/
def referenceNumerators (top : TopBranchRows)
    (root region parent : ℕ) : List ℕ :=
  (validSlots parent).map (topSplitNumerator top root region parent)

/-- Exact logical-X marginal of the ordered top-split law. -/
def marginalXNumerators (top : TopBranchRows) (order : CoordinateOrder)
    (root region parent : ℕ) : List ℕ :=
  (List.range coordinateCount).map fun value ↦
    ((validSlots parent).map fun slot ↦
      if shapeCoordinate (pairAt parent slot).1 order.x = value then
        topSplitNumerator top root region parent slot
      else 0).sum

/-! ## Exact parent concatenation and compatibility rows -/

/-- Add an exact numerator to a padded array when the target slot is in range. -/
def addNumeratorAt (row : Array ℕ) (slot numerator : ℕ) : Array ℕ :=
  if slot < row.size then row.modify slot (· + numerator) else row

/-- Parent support slot obtained by concatenating two length-four complete-split words. -/
def concatenatedParentSlot (parent coordinate slot leftSymbol rightSymbol : ℕ) : ℕ :=
  let pair := pairAt parent slot
  let leftCode := ternarySupportCodeAt levelThreeWordLength
    (shapeCoordinate pair.1 coordinate) leftSymbol
  let rightCode := ternarySupportCodeAt levelThreeWordLength
    (shapeCoordinate pair.2 coordinate) rightSymbol
  (ternarySupportCodes parentWordLength
    (shapeCoordinate (parentShapeAt parent) coordinate)).idxOf
      (leftCode * 3 ^ levelThreeWordLength + rightCode)

/-- Concatenated parent slot when the ordered child pair has already been decoded. -/
def concatenatedParentSlotForPair (parent coordinate : ℕ) (pair : Shape × Shape)
    (leftSymbol rightSymbol : ℕ) : ℕ :=
  let leftCode := ternarySupportCodeAt levelThreeWordLength
    (shapeCoordinate pair.1 coordinate) leftSymbol
  let rightCode := ternarySupportCodeAt levelThreeWordLength
    (shapeCoordinate pair.2 coordinate) rightSymbol
  (ternarySupportCodes parentWordLength
    (shapeCoordinate (parentShapeAt parent) coordinate)).idxOf
      (leftCode * 3 ^ levelThreeWordLength + rightCode)

/-- Scatter one pair of depth-three symbols into its concatenated depth-four slot. -/
def addBetaFourContribution (betaThree : BetaThreeRows)
    (parent coordinate splitNumerator leftRow rightRow : ℕ) (pair : Shape × Shape)
    (leftSymbol rightSymbol : ℕ)
    (row : Array ℕ) : Array ℕ :=
  let leftNumerator := betaThreeNumeratorFrom betaThree leftRow coordinate leftSymbol
  if leftNumerator = 0 then row
  else
    let rightNumerator := betaThreeNumeratorFrom betaThree rightRow coordinate rightSymbol
    if rightNumerator = 0 then row
    else
      let numerator := splitNumerator * leftNumerator * rightNumerator
      addNumeratorAt row
        (concatenatedParentSlotForPair parent coordinate pair leftSymbol rightSymbol) numerator

/-! ### Zero-sparse evaluation

The exact certificate rows are highly sparse.  Evaluating the dense recurrence nevertheless walks
every padded top slot and every pair of padded child symbols.  The definitions below remove entries
whose numerator is structurally zero before running those folds.  Their soundness theorem later in
this section proves that this is only an evaluation optimization: the resulting row is exactly
`betaFourParentRow`.
-/

/-- Filtering elements on which a fold step is the identity does not change the fold.

This small list lemma is kept private because it is an implementation detail of the sparse
recurrence evaluator.

Proof sketch: induct on the list.  A retained head is processed on both sides; a discarded head is
removed on the left and acts as the identity on the right. -/
private theorem foldl_filter_eq_of_false_step {α β : Type*}
    (keep : β → Bool) (step : α → β → α)
    (hstep : ∀ accumulator value, keep value = false →
      step accumulator value = accumulator)
    (values : List β) (initial : α) :
    (values.filter keep).foldl step initial = values.foldl step initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      cases hkeep : keep value with
      | false =>
          simp only [List.filter_cons, hkeep, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
          rw [hstep initial value hkeep]
          exact ih initial
      | true =>
          simp only [List.filter_cons, hkeep, ↓reduceIte, List.foldl_cons]
          exact ih (step initial value)

/-- A fold whose step is always the identity returns its initial accumulator. -/
private theorem foldl_eq_self_of_step {α β : Type*}
    (step : α → β → α) (hstep : ∀ accumulator value, step accumulator value = accumulator)
    (values : List β) (initial : α) : values.foldl step initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      rw [List.foldl_cons, hstep initial value]
      exact ih initial

/-- Nonzero symbols in one depth-three child row.

The order is inherited from `List.range`, so filtering does not alter the deterministic scatter
order used by the dense recurrence. -/
def nonzeroBetaThreeSymbols (betaThree : BetaThreeRows) (row coordinate : ℕ) : List ℕ :=
  (List.range childSupportWidth).filter fun symbol ↦
    decide (betaThreeNumeratorFrom betaThree row coordinate symbol ≠ 0)

/-- Top-split slots carrying nonzero exact mass for one parent. -/
def nonzeroTopSlots (top : TopBranchRows) (root region parent : ℕ) : List ℕ :=
  (validSlots parent).filter fun slot ↦
    decide (topSplitNumerator top root region parent slot ≠ 0)

/-- Fold all child-symbol products belonging to one ordered split into a parent row. -/
def addBetaFourSlot (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) (row : Array ℕ) (slot : ℕ) : Array ℕ :=
  if topSplitNumerator top root region parent slot = 0 then row
  else
    let splitNumerator := topSplitNumerator top root region parent slot
    let pair := pairAt parent slot
    let leftRow := shapeEightIndex pair.1 * regionCount + region
    let rightRow := shapeEightIndex pair.2 * regionCount + region
    (List.range childSupportWidth).foldl (fun row leftSymbol ↦
      (List.range childSupportWidth).foldl (fun row rightSymbol ↦
        addBetaFourContribution betaThree parent coordinate splitNumerator leftRow rightRow pair
          leftSymbol rightSymbol row) row) row

/-- Sparse version of `addBetaFourSlot`, iterating only over nonzero child symbols. -/
def addBetaFourSlotSparse (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) (row : Array ℕ) (slot : ℕ) : Array ℕ :=
  if topSplitNumerator top root region parent slot = 0 then row
  else
    let splitNumerator := topSplitNumerator top root region parent slot
    let pair := pairAt parent slot
    let leftRow := shapeEightIndex pair.1 * regionCount + region
    let rightRow := shapeEightIndex pair.2 * regionCount + region
    (nonzeroBetaThreeSymbols betaThree leftRow coordinate).foldl (fun row leftSymbol ↦
      (nonzeroBetaThreeSymbols betaThree rightRow coordinate).foldl (fun row rightSymbol ↦
        addBetaFourContribution betaThree parent coordinate splitNumerator leftRow rightRow pair
          leftSymbol rightSymbol row) row) row

/-- Removing zero child symbols leaves the contribution of one top slot unchanged.

Proof sketch: a discarded right symbol is an identity step by the second zero guard in
`addBetaFourContribution`.  A discarded left symbol makes every inner step an identity by the
first guard.  Applying `foldl_filter_eq_of_false_step` to the two nested folds gives the result. -/
theorem addBetaFourSlotSparse_eq_addBetaFourSlot (top : TopBranchRows)
    (betaThree : BetaThreeRows) (root region parent coordinate : ℕ)
    (row : Array ℕ) (slot : ℕ) :
    addBetaFourSlotSparse top betaThree root region parent coordinate row slot =
      addBetaFourSlot top betaThree root region parent coordinate row slot := by
  unfold addBetaFourSlotSparse addBetaFourSlot
  by_cases hsplit : topSplitNumerator top root region parent slot = 0
  · simp [hsplit]
  · simp only [hsplit, ↓reduceIte]
    let splitNumerator := topSplitNumerator top root region parent slot
    let pair := pairAt parent slot
    let leftRow := shapeEightIndex pair.1 * regionCount + region
    let rightRow := shapeEightIndex pair.2 * regionCount + region
    let contribution := fun (leftSymbol rightSymbol : ℕ) (accumulator : Array ℕ) ↦
      addBetaFourContribution betaThree parent coordinate splitNumerator leftRow rightRow pair
        leftSymbol rightSymbol accumulator
    change
      (nonzeroBetaThreeSymbols betaThree leftRow coordinate).foldl
          (fun accumulator leftSymbol ↦
            (nonzeroBetaThreeSymbols betaThree rightRow coordinate).foldl
              (fun inner rightSymbol ↦ contribution leftSymbol rightSymbol inner) accumulator) row =
        (List.range childSupportWidth).foldl
          (fun accumulator leftSymbol ↦
            (List.range childSupportWidth).foldl
              (fun inner rightSymbol ↦ contribution leftSymbol rightSymbol inner) accumulator) row
    have hright (leftSymbol : ℕ) (initial : Array ℕ) :
        (nonzeroBetaThreeSymbols betaThree rightRow coordinate).foldl
            (fun accumulator rightSymbol ↦ contribution leftSymbol rightSymbol accumulator) initial =
          (List.range childSupportWidth).foldl
            (fun accumulator rightSymbol ↦ contribution leftSymbol rightSymbol accumulator) initial := by
      apply foldl_filter_eq_of_false_step
      intro accumulator rightSymbol hkeep
      have hzero : betaThreeNumeratorFrom betaThree rightRow coordinate rightSymbol = 0 := by
        simpa [Bool.decide_eq_false] using hkeep
      simp [contribution, addBetaFourContribution, hzero]
    simp_rw [hright]
    apply foldl_filter_eq_of_false_step
    intro accumulator leftSymbol hkeep
    have hzero : betaThreeNumeratorFrom betaThree leftRow coordinate leftSymbol = 0 := by
      simpa [Bool.decide_eq_false] using hkeep
    apply foldl_eq_self_of_step
    intro inner rightSymbol
    simp [contribution, addBetaFourContribution, hzero]

/-- Exact `2^116` complete-split parent row obtained by top-weighted independent concatenation. -/
def betaFourParentRow (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) : List ℕ :=
  ((validSlots parent).foldl
    (addBetaFourSlot top betaThree root region parent coordinate)
    (Array.replicate parentSupportWidth 0)).toList

/-- Zero-sparse evaluator for the exact level-four parent row.

Only nonzero top slots and child symbols are visited.  This definition is intended for generated
certificate checkers; semantic theorems should continue to state their conclusions using
`betaFourParentRow`. -/
def betaFourParentRowSparse (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) : List ℕ :=
  ((nonzeroTopSlots top root region parent).foldl
    (addBetaFourSlotSparse top betaThree root region parent coordinate)
    (Array.replicate parentSupportWidth 0)).toList

/-- The sparse level-four evaluator is exactly equal to the dense semantic recurrence.

Proof sketch: first replace every sparse slot step by the equal dense step.  A top slot removed by
`nonzeroTopSlots` has zero split numerator, so the dense step is the identity.  The generic
filter-fold lemma then restores all discarded slots. -/
theorem betaFourParentRowSparse_eq_betaFourParentRow (top : TopBranchRows)
    (betaThree : BetaThreeRows) (root region parent coordinate : ℕ) :
    betaFourParentRowSparse top betaThree root region parent coordinate =
      betaFourParentRow top betaThree root region parent coordinate := by
  unfold betaFourParentRowSparse betaFourParentRow
  have hstep :
      addBetaFourSlotSparse top betaThree root region parent coordinate =
        addBetaFourSlot top betaThree root region parent coordinate := by
    funext row slot
    exact addBetaFourSlotSparse_eq_addBetaFourSlot
      top betaThree root region parent coordinate row slot
  rw [hstep]
  congr 1
  apply foldl_filter_eq_of_false_step
  intro accumulator slot hkeep
  have hzero : topSplitNumerator top root region parent slot = 0 := by
    simpa [Bool.decide_eq_false] using hkeep
  simp [addBetaFourSlot, hzero]

/-- Child row weighted by both ordered occurrences and represented at denominator `2^116`. -/
def weightedChildRow (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent slot coordinate : ℕ) : List ℕ :=
  let pair := pairAt parent slot
  let childRow := shapeEightIndex pair.1 * regionCount + region
  (List.range childSupportWidth).map fun symbol ↦
    orderedTopSplitNumerator top root region parent slot *
      betaThreeNumeratorFrom betaThree childRow coordinate symbol * childRowRescale

/-- Whether a split belongs to the individually charged logical-Y boundary cell. -/
def yFirstSlot (order : CoordinateOrder) (parent slot : ℕ) : Bool :=
  decide (shapeCoordinate (pairAt parent slot).1 order.z = 0)

/-- Whether a split belongs to the individually charged logical-Z boundary cell. -/
def zFirstSlot (order : CoordinateOrder) (parent slot : ℕ) : Bool :=
  decide (shapeCoordinate (pairAt parent slot).1 order.x = 0 ∨
    shapeCoordinate (pairAt parent slot).1 order.y = 0)

/-- Individually charged logical-Y boundary rows. -/
def yFirstRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : List (List ℕ) :=
  ((validSlots parent).filter (yFirstSlot order parent)).map fun slot ↦
    weightedChildRow top betaThree root region parent slot order.y

/-- Individually charged logical-Z boundary rows. -/
def zFirstRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : List (List ℕ) :=
  ((validSlots parent).filter (zFirstSlot order parent)).map fun slot ↦
    weightedChildRow top betaThree root region parent slot order.z

/-- Pool non-boundary child rows satisfying a fixed split-coordinate value. -/
def pooledChildRow (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent childCoordinate groupCoordinate group : ℕ)
    (first : ℕ → Bool) : List ℕ :=
  (List.range childSupportWidth).map fun symbol ↦
    ((validSlots parent).map fun slot ↦
      if first slot = false ∧
          shapeCoordinate (pairAt parent slot).1 groupCoordinate = group then
        let pair := pairAt parent slot
        let childRow := shapeEightIndex pair.1 * regionCount + region
        orderedTopSplitNumerator top root region parent slot *
          betaThreeNumeratorFrom betaThree childRow childCoordinate symbol * childRowRescale
      else 0).sum

/-- Logical-Y compatibility cells pool non-boundary rows by the logical-Y split coordinate. -/
def yGroupRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : List (List ℕ) :=
  (List.range coordinateCount).map fun group ↦
    pooledChildRow top betaThree root region parent order.y order.y group
      (yFirstSlot order parent)

/-- Logical-Z compatibility cells pool non-boundary rows by the logical-Z split coordinate. -/
def zGroupRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : List (List ℕ) :=
  (List.range coordinateCount).map fun group ↦
    pooledChildRow top betaThree root region parent order.z order.z group
      (zFirstSlot order parent)

/-- Complete parent, boundary, and pooled-cell rows for logical Y after the regional XZY
orientation.  The published pre-orientation `Z` formula is transported to logical `Y`. -/
def logicalYRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : CompatibilityRows :=
  { pooled := betaFourParentRow top betaThree root region parent order.z
    first := zFirstRows top betaThree order root region parent
    groups := zGroupRows top betaThree order root region parent }

/-- Complete parent, boundary, and pooled-cell rows for logical Z after the regional XZY
orientation.  The published pre-orientation `Y` formula is transported to logical `Z`. -/
def logicalZRows (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : CompatibilityRows :=
  { pooled := betaFourParentRow top betaThree root region parent order.y
    first := yFirstRows top betaThree order root region parent
    groups := yGroupRows top betaThree order root region parent }

/-- The pooled component of the logical-Y compatibility record is the parent row on physical Z.

This projection lemma keeps generated semantic adapters from unfolding the boundary and grouping
fields when they need only the pooled row. -/
@[simp] theorem logicalYRows_pooled (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) :
    (logicalYRows top betaThree order root region parent).pooled =
      betaFourParentRow top betaThree root region parent order.z := rfl

/-- The pooled component of the logical-Z compatibility record is the parent row on physical Y.

As with `logicalYRows_pooled`, this is a definitional projection exposed as a stable public law so
clients do not unfold the rest of a compatibility record. -/
@[simp] theorem logicalZRows_pooled (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) :
    (logicalZRows top betaThree order root region parent).pooled =
      betaFourParentRow top betaThree root region parent order.y := rfl

/-- Exact rows for one positive level-four parent, using an explicit checked beta-three cache. -/
def localRowsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (weights : DualWeights)
    (root region parent : ℕ) : LocalRows coordinateCount :=
  { support := splitSupport order parent
    referenceNumerators := referenceNumerators top root region parent
    marginalXNumerators := marginalXNumerators top order root region parent
    weightX := weights.forCoordinate order.x
    weightY := weights.forCoordinate order.y
    weightZ := weights.forCoordinate order.z
    logicalY := logicalYRows top betaThree order root region parent
    logicalZ := logicalZRows top betaThree order root region parent }

/-- One level-four parent contributes directly, so its separate outer numerator is one. -/
def weightedLocalRowsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (weights : DualWeights)
    (root region parent : ℕ) : WeightedLocalRows coordinateCount :=
  { outerNumerator := 1
    rows := localRowsFrom top betaThree order weights root region parent }

/-- Active parent list for the diagonal `(root = region)` family of one output region. -/
def activeParents (top : TopBranchRows) (region : ℕ) : List ℕ :=
  (List.range parentCount).filter fun parent ↦
    decide (0 < (referenceNumerators top region region parent).sum)

/-- Exact level-four entries of one output region. -/
def regionEntriesFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    List (WeightedLocalRows coordinateCount) :=
  (activeParents top region).map fun parent ↦
    weightedLocalRowsFrom top betaThree (orders region) (weights parent)
      region region parent

/-- Explicit-parent form of one regional entry family. -/
def regionEntriesOnParentsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) : List (WeightedLocalRows coordinateCount) :=
  parents.map fun parent ↦
    weightedLocalRowsFrom top betaThree (orders region) (weights parent)
      region region parent

theorem regionEntriesFrom_eq_onParents (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    regionEntriesFrom top betaThree orders weights region =
      regionEntriesOnParentsFrom top betaThree orders weights region
        (activeParents top region) := by
  rfl

/-- Semantic branch rate over an explicitly serialized parent subfamily. -/
noncomputable def branchRateOnParentsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) (branch : Fin 3) : ℝ :=
  weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
    (regionEntriesOnParentsFrom top betaThree orders weights region parents) branch

/-- Exact signed-log form over an explicitly serialized parent subfamily. -/
def branchFormOnParentsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) (branch : Fin 3) :=
  weightedFamilyBranchForm referenceBits compatibilityExtraBits
    (regionEntriesOnParentsFrom top betaThree orders weights region parents) branch

theorem branchFormOnParentsFrom_eval (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval 116
        (branchFormOnParentsFrom top betaThree orders weights region parents branch) =
      branchRateOnParentsFrom top betaThree orders weights region parents branch := by
  exact weightedFamilyBranchForm_eval outerBits referenceBits compatibilityExtraBits
    (regionEntriesOnParentsFrom top betaThree orders weights region parents) branch

/-- Explicit parent chunks add exactly to the flattened family rate. -/
theorem branchRateOnParentsFrom_flatten (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (chunks : List (List ℕ)) (branch : Fin 3) :
    branchRateOnParentsFrom top betaThree orders weights region chunks.flatten branch =
      (chunks.map fun parents ↦
        branchRateOnParentsFrom top betaThree orders weights region parents branch).sum := by
  unfold branchRateOnParentsFrom regionEntriesOnParentsFrom
  induction chunks with
  | nil => rfl
  | cons parents chunks ih =>
      simp only [List.flatten_cons, List.map_append, List.map_cons, List.sum_cons]
      rw [weightedFamilyBranchRate_append, ih]

/-- Semantic branch rate of one complete level-four region. -/
noncomputable def regionBranchRateFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) : ℝ :=
  weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
    (regionEntriesFrom top betaThree orders weights region) branch

theorem regionBranchRateFrom_eq_onParents (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    regionBranchRateFrom top betaThree orders weights region branch =
      branchRateOnParentsFrom top betaThree orders weights region
        (activeParents top region) branch := by
  rfl

/-- Exact common-denominator form for one complete regional branch. -/
def regionBranchFormFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :=
  weightedFamilyBranchForm referenceBits compatibilityExtraBits
    (regionEntriesFrom top betaThree orders weights region) branch

theorem regionBranchFormFrom_eval (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval 116
        (regionBranchFormFrom top betaThree orders weights region branch) =
      regionBranchRateFrom top betaThree orders weights region branch := by
  exact weightedFamilyBranchForm_eval outerBits referenceBits compatibilityExtraBits
    (regionEntriesFrom top betaThree orders weights region) branch

/-! ## Six-region family endpoint -/

/-- Sum of six exact regional retained exponents on explicitly supplied parent lists.  Generated
clients use this monotone selected-family form, so proving that omitted zero rows are *exactly*
the full active support is unnecessary for soundness. -/
noncomputable def familyRetainedExponentOnParentsFrom
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights)
    (parents : ℕ → List ℕ) : ℝ :=
  ((List.range regionCount).map fun region ↦
    weightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits
      (regionEntriesOnParentsFrom top betaThree orders (weights region) region
        (parents region))).sum

/-- Corresponding mathematical exponent on the same explicit parent lists. -/
noncomputable def mathematicalFamilyRetainedExponentOnParentsFrom
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights)
    (parents : ℕ → List ℕ) : ℝ :=
  ((List.range regionCount).map fun region ↦
    mathematicalWeightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits
      (regionEntriesOnParentsFrom top betaThree orders (weights region) region
        (parents region))).sum

/-- Pointwise validity proves the six-region bound for any explicitly selected parent family. -/
theorem familyRetainedExponentOnParentsFrom_le_mathematical
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights)
    (parents : ℕ → List ℕ)
    (hvalid : ∀ region < regionCount,
      ∀ entry ∈ regionEntriesOnParentsFrom top betaThree orders (weights region) region
          (parents region), entry.rows.IsValid) :
    familyRetainedExponentOnParentsFrom top betaThree orders weights parents ≤
      mathematicalFamilyRetainedExponentOnParentsFrom top betaThree orders weights parents := by
  unfold familyRetainedExponentOnParentsFrom
    mathematicalFamilyRetainedExponentOnParentsFrom
  apply List.sum_le_sum
  intro region hregion
  exact weightedFamilyRetainedExponent_le_mathematical _ _ _ _
    (hvalid region (List.mem_range.mp hregion))

/-- Sum of the six exact integer-dual regional retained exponents. -/
noncomputable def familyRetainedExponentFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights) : ℝ :=
  ((List.range regionCount).map fun region ↦
    weightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits
      (regionEntriesFrom top betaThree orders (weights region) region)).sum

/-- Corresponding mathematical fixed-marginal exponent of the same six families. -/
noncomputable def mathematicalFamilyRetainedExponentFrom
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights) : ℝ :=
  ((List.range regionCount).map fun region ↦
    mathematicalWeightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits
      (regionEntriesFrom top betaThree orders (weights region) region)).sum

/-- Pointwise-valid integer duals give a conservative exact exponent for all six regions. -/
theorem familyRetainedExponentFrom_le_mathematical
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → ℕ → DualWeights)
    (hvalid : ∀ region < regionCount,
      ∀ entry ∈ regionEntriesFrom top betaThree orders (weights region) region,
        entry.rows.IsValid) :
    familyRetainedExponentFrom top betaThree orders weights ≤
      mathematicalFamilyRetainedExponentFrom top betaThree orders weights := by
  unfold familyRetainedExponentFrom mathematicalFamilyRetainedExponentFrom
  apply List.sum_le_sum
  intro region hregion
  exact weightedFamilyRetainedExponent_le_mathematical _ _ _ _
    (hvalid region (List.mem_range.mp hregion))

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
