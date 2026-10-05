/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOccurrenceClients
import MatrixMultiplication.SimplifiedRecursiveLevelThreeOccurrences
import MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences

/-!
# Total-weight clients for the simplified recursive occurrence packages

This module supplies the coordinate-support premise of the generic occurrence client for the
committed level-three and level-four labelled occurrence laws.  A nonzero occurrence count has a
nonzero guarded child-row count; the corresponding child-profile support theorem then identifies
its split-word weight with the occurrence's coarse coordinate.

The two final constructors are local occurrence adapters.  They scale the empirical full-cell
equality by an explicit repetition factor `k`, but deliberately retain the local validity and
boundary premises used to construct their occurrence packages.  Certificate-facing clients should
consume a fully constructed `RecursiveOccurrenceTargetData` when those checks have already been
packaged upstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveChildProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelThreeOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-! ## Coordinate support -/

/-- A nonzero left level-three child-row count has the intrinsic child coordinate. -/
private theorem levelThreeLeftChildWordCount_supported
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1)
    (hcount : levelThreeLeftChildWordCount data node region sigma slot c word ≠ 0) :
    splitWordWeight word = (levelThreeChildShape node sigma slot).get c := by
  apply levelTwoWordCountAtFor_supported sortedPairSupportSlot data node.val region.val
    slot.1.val (coordinateOfLeg (sigma c)).val
      ((levelThreeChildShape node sigma slot).get c) word
  exact hcount

/-- A nonzero right level-three child-row count has the complementary child coordinate. -/
private theorem levelThreeRightChildWordCount_supported
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1)
    (hcount : levelThreeRightChildWordCount data node region sigma slot c word ≠ 0) :
    splitWordWeight word =
      (RecursiveChildShape.complement (levelThreeParentIndex_total_twice node sigma)
        (levelThreeChildShape node sigma slot)).get c := by
  have hsupported := levelTwoWordCountAtFor_supported sortedPairSupportSlot data node.val
    region.val (levelThreeComplementSlot node slot).1.val
      (coordinateOfLeg (sigma c)).val
      ((levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c)
      word hcount
  rw [levelThreeChildShape_complement] at hsupported
  exact hsupported

/-- Every nonzero labelled level-three occurrence row has the coordinate advertised by its
coarse occurrence cell. -/
theorem cwTotalWeightLevelThreeOccurrenceLaw_supported
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node))
    (word : SplitWord 1)
    (hcount : (levelThreeOccurrenceLaw data node region sigma hvalid c).count
      occurrence word ≠ 0) :
    splitWordWeight word = (levelThreeOccurrenceCoarseIndex node sigma occurrence).get c := by
  obtain ⟨slot, side⟩ := occurrence
  cases side with
  | left =>
      have hchild : levelThreeLeftChildWordCount data node region sigma slot c word ≠ 0 := by
        intro hzero
        exact hcount (by simp [hzero])
      change splitWordWeight word = (levelThreeChildShape node sigma slot).get c
      exact levelThreeLeftChildWordCount_supported data node region sigma slot c word hchild
  | right =>
      have hchild : levelThreeRightChildWordCount data node region sigma slot c word ≠ 0 := by
        intro hzero
        exact hcount (by simp [hzero])
      change splitWordWeight word =
        (RecursiveChildShape.complement (levelThreeParentIndex_total_twice node sigma)
          (levelThreeChildShape node sigma slot)).get c
      exact levelThreeRightChildWordCount_supported data node region sigma slot c word hchild

/-- A nonzero left level-four child-row count has the intrinsic child coordinate. -/
private theorem levelFourLeftChildWordCount_supported
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2)
    (hcount : levelFourLeftChildWordCount betaThree region parent sigma slot c word ≠ 0) :
    splitWordWeight word = (levelFourChildShape parent sigma slot).get c := by
  apply levelThreeWordCountAt_supported betaThree
    (shapeEightIndex (levelFourPairAtSlot parent slot.1 slot.2).1 * 6 + region.val)
    (coordinateOfLeg (sigma c)).val ((levelFourChildShape parent sigma slot).get c) word
  exact hcount

/-- A nonzero right level-four child-row count has the complementary child coordinate. -/
private theorem levelFourRightChildWordCount_supported
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2)
    (hcount : levelFourRightChildWordCount betaThree region parent sigma slot c word ≠ 0) :
    splitWordWeight word =
      (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot)).get c := by
  apply levelThreeWordCountAt_supported betaThree
    (shapeEightIndex (levelFourPairAtSlot parent slot.1 slot.2).2 * 6 + region.val)
    (coordinateOfLeg (sigma c)).val
    ((RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
      (levelFourChildShape parent sigma slot)).get c) word
  exact hcount

/-- Every nonzero labelled level-four occurrence row has the coordinate advertised by its
coarse occurrence cell. -/
theorem cwTotalWeightLevelFourOccurrenceLaw_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent))
    (word : SplitWord 2)
    (hcount : (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
      occurrence word ≠ 0) :
    splitWordWeight word = (levelFourOccurrenceCoarseIndex parent sigma occurrence).get c := by
  obtain ⟨slot, side⟩ := occurrence
  cases side with
  | left =>
      have hchild : levelFourLeftChildWordCount betaThree region parent sigma slot c word ≠ 0 := by
        intro hzero
        exact hcount (by simp [hzero])
      change splitWordWeight word = (levelFourChildShape parent sigma slot).get c
      exact levelFourLeftChildWordCount_supported betaThree region parent sigma slot c word hchild
  | right =>
      have hchild : levelFourRightChildWordCount betaThree region parent sigma slot c word ≠ 0 := by
        intro hzero
        exact hcount (by simp [hzero])
      change splitWordWeight word =
        (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
          (levelFourChildShape parent sigma slot)).get c
      exact levelFourRightChildWordCount_supported betaThree region parent sigma slot c word hchild

/-! ## Reference-profile constructors -/

/-- The level-three occurrence target package satisfies all four total-weight reference profile
equations at every proportional repetition of its full occurrence cell type.  This is a local
semantic adapter; `hvalid` and `hboundary` are not certificate checks performed here. -/
theorem cwTotalWeightLevelThreeReferenceProfiles
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (hboundary : LevelThreeOccurrenceBoundaryValid data node region sigma hvalid)
    (k n : ℕ) (partAt : Fin (n + 1) → PUnit)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 1 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 1
          (fun slot ↦ levelThreeSlotNumerator data node region slot *
            (levelTwoChildDenominator * levelTwoChildDenominator))
          (levelThreeOccurrenceCoarseIndex node sigma)
          (levelThreeOccurrenceCoarseIndex_total node sigma)) k) :
    CWTotalWeightReferenceProfiles 1 n partAt
      (cwProportionalRecursiveOccurrenceTargetData
        (levelThreeOccurrenceTargetData data node region sigma hvalid hboundary)
        k).toCompatibilityTargets reference := by
  apply cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData_proportionalCounts
    1 n partAt
    (fun slot ↦ levelThreeSlotNumerator data node region slot *
      (levelTwoChildDenominator * levelTwoChildDenominator))
    (levelThreeOccurrenceCoarseIndex node sigma)
    (levelThreeOccurrenceTargetData data node region sigma hvalid hboundary)
    (levelThreeOccurrenceCoarseIndex_total node sigma)
    _ k reference hreference
  intro c occurrence word hcount
  exact cwTotalWeightLevelThreeOccurrenceLaw_supported
    data node region sigma hvalid c occurrence word hcount

/-- The level-four occurrence target package satisfies all four total-weight reference profile
equations at every proportional repetition of its full occurrence cell type.  This depth-two
theorem is local per-stage occurrence semantics only; its validity, boundary, and order premises
are not discharged here. -/
theorem cwTotalWeightLevelFourReferenceProfiles
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (k n : ℕ) (partAt : Fin (n + 1) → PUnit)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 2) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 2 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 2
          (fun slot ↦ levelFourSlotNumerator top root region parent slot *
            (levelFourChildSamples * levelFourChildSamples))
          (levelFourOccurrenceCoarseIndex parent sigma)
          (levelFourOccurrenceCoarseIndex_total parent sigma)) k) :
    CWTotalWeightReferenceProfiles 2 n partAt
      (cwProportionalRecursiveOccurrenceTargetData
        (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
          hvalid hboundary) k).toCompatibilityTargets reference := by
  apply cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData_proportionalCounts
    2 n partAt
    (fun slot ↦ levelFourSlotNumerator top root region parent slot *
      (levelFourChildSamples * levelFourChildSamples))
    (levelFourOccurrenceCoarseIndex parent sigma)
    (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
      hvalid hboundary)
    (levelFourOccurrenceCoarseIndex_total parent sigma)
    _ k reference hreference
  intro c occurrence word hcount
  exact cwTotalWeightLevelFourOccurrenceLaw_supported
    top betaThree root region parent sigma hvalid c occurrence word hcount

end AlgebraicComplexity.Examples
