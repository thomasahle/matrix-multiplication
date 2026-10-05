/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-!
# Direct gathering of level-four parent convolutions

The original level-four evaluator scatters every pair of nonzero child symbols into a padded
1107-cell array.  That representation is convenient for executable reconstruction, but a closed
kernel proof retains many successive persistent-array updates.

This module provides the dual pointwise formulation.  For a requested parent word, it splits the
word into its two length-four halves and sums the contribution of every ordered top slot.  Each
output numerator is independent, so generated checkers can verify bounded groups of symbols in
separate declarations without rebuilding a large intermediate array.

The definitions here are certificate-independent.  The central semantic obligation is to prove
that gathering agrees with the existing scatter evaluator; downstream certificates must not use
the gather representation until that theorem is available.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Contribution of one ordered top slot to one requested parent-support symbol.

The requested length-eight ternary word is split into its first and last four digits.  An absent
half-word has `idxOf` equal to the child support length, where the padded beta-three lookup returns
zero. -/
def betaFourGatherSlotNumerator (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate symbol slot : ℕ) : ℕ :=
  let pair := pairAt parent slot
  let parentTotal := shapeCoordinate (parentShapeAt parent) coordinate
  let parentCode := ternarySupportCodeAt parentWordLength parentTotal symbol
  let leftCode := parentCode / 3 ^ levelThreeWordLength
  let rightCode := parentCode % 3 ^ levelThreeWordLength
  let leftSupport := ternarySupportCodes levelThreeWordLength
    (shapeCoordinate pair.1 coordinate)
  let rightSupport := ternarySupportCodes levelThreeWordLength
    (shapeCoordinate pair.2 coordinate)
  let leftSymbol := leftSupport.idxOf leftCode
  let rightSymbol := rightSupport.idxOf rightCode
  let leftRow := shapeEightIndex pair.1 * regionCount + region
  let rightRow := shapeEightIndex pair.2 * regionCount + region
  topSplitNumerator top root region parent slot *
    betaThreeNumeratorFrom betaThree leftRow coordinate leftSymbol *
      betaThreeNumeratorFrom betaThree rightRow coordinate rightSymbol

/-- Pointwise level-four numerator obtained by gathering all ordered top-slot contributions. -/
def betaFourParentNumeratorGather (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate symbol : ℕ) : ℕ :=
  if symbol <
      (ternarySupportCodes parentWordLength
        (shapeCoordinate (parentShapeAt parent) coordinate)).length then
    ((validSlots parent).map fun slot ↦
      betaFourGatherSlotNumerator top betaThree root region parent coordinate symbol slot).sum
  else 0

/-- Gather selected parent-support symbols in the supplied order.

This is the bounded evaluation interface for generated certificates: a producer can divide
`List.range parentSupportWidth` into small shards while the checker recomputes every numerator in
each shard from the primary top and beta-three tables. -/
def betaFourParentRowGatherOn (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) (symbols : List ℕ) : List ℕ :=
  symbols.map (betaFourParentNumeratorGather top betaThree root region parent coordinate)

/-- Gather evaluation respects concatenation of symbol shards.

Proof sketch: `betaFourParentRowGatherOn` is a list map, and mapping over an appended list is the
append of the two maps.  Generated clients use this law to assemble independently checked shards.
-/
theorem betaFourParentRowGatherOn_append (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) (left right : List ℕ) :
    betaFourParentRowGatherOn top betaThree root region parent coordinate (left ++ right) =
      betaFourParentRowGatherOn top betaThree root region parent coordinate left ++
        betaFourParentRowGatherOn top betaThree root region parent coordinate right := by
  simp [betaFourParentRowGatherOn]

/-- A gather shard has exactly as many entries as its requested symbol list. -/
@[simp] theorem length_betaFourParentRowGatherOn (top : TopBranchRows)
    (betaThree : BetaThreeRows) (root region parent coordinate : ℕ) (symbols : List ℕ) :
    (betaFourParentRowGatherOn top betaThree root region parent coordinate symbols).length =
      symbols.length := by
  simp [betaFourParentRowGatherOn]

/-- Full padded parent row in the direct gather representation. -/
def betaFourParentRowGather (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) : List ℕ :=
  betaFourParentRowGatherOn top betaThree root region parent coordinate
    (List.range parentSupportWidth)

/-- The full gather row is the bounded gather interface applied to the padded support range. -/
theorem betaFourParentRowGather_eq_on_range (top : TopBranchRows)
    (betaThree : BetaThreeRows) (root region parent coordinate : ℕ) :
    betaFourParentRowGather top betaThree root region parent coordinate =
      betaFourParentRowGatherOn top betaThree root region parent coordinate
        (List.range parentSupportWidth) := by
  rfl

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
