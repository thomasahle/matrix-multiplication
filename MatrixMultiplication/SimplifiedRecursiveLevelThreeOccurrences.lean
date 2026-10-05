/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveCompleteSplitOccurrenceLaw
import MatrixMultiplication.SimplifiedRecursiveChildProfiles

/-!
# Labelled level-three child occurrences in the simplified certificate

This module reconstructs the compatibility tables of a positive level-three node from the raw
ordered `pos3Alpha` row.  An ordered slot contributes one labelled left occurrence and one
labelled right occurrence.  Reindexing the right occurrences by the canonical complement-slot
permutation produces the evaluator coefficient

`alpha(u) + alpha(parent - u)`.

The raw law is retained until that finite reindexing theorem is applied.  Thus a
self-complementary slot contributes two labelled summands, and the symmetrized evaluator row is
derived rather than used as a semantic premise.  No hashing, competitor estimate, tensor
restriction, hole repair, or numerical inequality is assumed here.
-/

namespace MatrixMultiplication.SimplifiedRecursiveLevelThreeOccurrences

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedRecursiveChildProfiles
open MatrixMultiplication.SimplifiedRecursiveParentTerms
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- The evaluator's explicit child-row rescaling factor is the semantic child-profile
denominator.  Naming this bridge keeps subsequent occurrence identities symbolic. -/
theorem childRowRescale_eq_levelTwoChildDenominator :
    childRowRescale = levelTwoChildDenominator := by
  norm_num [childRowRescale, levelTwoChildDenominator,
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localDenominator,
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localBits]

/-- Intrinsic child shape carried by one labelled occurrence of a raw ordered level-three slot. -/
def levelThreeOccurrenceChildShape
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node)) :
    RecursiveChildShape ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4 :=
  match occurrence.2 with
  | .left => levelThreeChildShape node sigma occurrence.1
  | .right =>
      RecursiveChildShape.complement (levelThreeParentIndex_total_twice node sigma)
        (levelThreeChildShape node sigma occurrence.1)

@[simp] theorem levelThreeOccurrenceChildShape_left
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) :
    levelThreeOccurrenceChildShape node sigma (slot, .left) =
      levelThreeChildShape node sigma slot :=
  rfl

@[simp] theorem levelThreeOccurrenceChildShape_right
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) :
    levelThreeOccurrenceChildShape node sigma (slot, .right) =
      RecursiveChildShape.complement (levelThreeParentIndex_total_twice node sigma)
        (levelThreeChildShape node sigma slot) :=
  rfl

/-- Logical coarse index of one intrinsic recursive child shape. -/
def recursiveChildShapeCoarseIndex
    {parentCount : Leg → ℕ} {childTotal : ℕ}
    (child : RecursiveChildShape parentCount childTotal) : CoarseIndex PUnit where
  part := PUnit.unit
  x := child.get .X
  y := child.get .Y
  z := child.get .Z

/-- Logical coarse index observed at one labelled child occurrence. -/
def levelThreeOccurrenceCoarseIndex
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node)) :
    CoarseIndex PUnit :=
  recursiveChildShapeCoarseIndex (levelThreeOccurrenceChildShape node sigma occurrence)

/-- Every labelled level-three occurrence is a tight depth-one child constituent. -/
theorem levelThreeOccurrenceCoarseIndex_total
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node)) :
    (levelThreeOccurrenceCoarseIndex node sigma occurrence).x +
        (levelThreeOccurrenceCoarseIndex node sigma occurrence).y +
        (levelThreeOccurrenceCoarseIndex node sigma occurrence).z = coarseTotal 1 := by
  simpa [levelThreeOccurrenceCoarseIndex, recursiveChildShapeCoarseIndex,
    coarseTotal] using (levelThreeOccurrenceChildShape node sigma occurrence).total_eq

/-- Logical coarse index attached to the ordered left child of one valid slot. -/
def levelThreeSlotCoarseIndex
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) : CoarseIndex PUnit :=
  recursiveChildShapeCoarseIndex (levelThreeChildShape node sigma slot)

/-- The explicit labelled-side map agrees with transport by the canonical slot complement. -/
theorem levelThreeOccurrenceChildShape_eq_childState
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node)) :
    levelThreeOccurrenceChildShape node sigma occurrence =
      levelThreeChildShape node sigma
        (occurrence.childState (levelThreeComplementSlotPerm node)) := by
  obtain ⟨slot, side⟩ := occurrence
  cases side with
  | left => rfl
  | right => exact (levelThreeChildShape_complement node sigma slot).symm

/-- Coarse occurrence lookup is equivalently slot lookup after complementary-state transport. -/
theorem levelThreeOccurrenceCoarseIndex_eq_childState
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelThreeValidSlot node)) :
    levelThreeOccurrenceCoarseIndex node sigma occurrence =
      levelThreeSlotCoarseIndex node sigma
        (occurrence.childState (levelThreeComplementSlotPerm node)) := by
  rw [levelThreeOccurrenceCoarseIndex, levelThreeSlotCoarseIndex,
    levelThreeOccurrenceChildShape_eq_childState]

/-- Exact complete-split law on both labelled occurrences of every raw ordered split slot. -/
def levelThreeOccurrenceLaw
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma) (c : Leg) :
    ComplementaryOccurrenceLaw
      (fun slot ↦ levelThreeSlotNumerator data node region slot *
        (levelTwoChildDenominator * levelTwoChildDenominator))
      (SplitWord 1) :=
  RecursiveSplitProfileComponent.occurrenceLaw
    (levelThreeSlotNumerator data node region)
    (levelThreeProfileComponent data node region sigma hvalid c)

@[simp] theorem levelThreeOccurrenceLaw_count_left
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (slot : LevelThreeValidSlot node) (word : SplitWord 1) :
    (levelThreeOccurrenceLaw data node region sigma hvalid c).count (slot, .left) word =
      levelThreeSlotNumerator data node region slot * levelTwoChildDenominator *
        levelThreeLeftChildWordCount data node region sigma slot c word :=
  rfl

@[simp] theorem levelThreeOccurrenceLaw_count_right
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (slot : LevelThreeValidSlot node) (word : SplitWord 1) :
    (levelThreeOccurrenceLaw data node region sigma hvalid c).count (slot, .right) word =
      levelThreeSlotNumerator data node region slot * levelTwoChildDenominator *
        levelThreeRightChildWordCount data node region sigma slot c word :=
  rfl

/-- The right-child row at the complementary slot is the original slot's left-child row. -/
theorem levelThreeRightChildWordCount_eq_left_complementSlot
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    levelThreeRightChildWordCount data node region sigma
        (levelThreeComplementSlot node slot) c word =
      levelThreeLeftChildWordCount data node region sigma slot c word := by
  unfold levelThreeRightChildWordCount levelThreeLeftChildWordCount
    levelThreeRightChildWordCountFor levelThreeLeftChildWordCountFor
  rw [levelThreeComplementSlot_involutive node slot]

/-- Raw alpha mass at the complementary slot is the proof-free complement-slot lookup. -/
theorem levelThreeSlotNumerator_complement
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (slot : LevelThreeValidSlot node) :
    levelThreeSlotNumerator data node region (levelThreeComplementSlot node slot) =
      dyadicNumeratorAt data.pos3Alpha (node.val * 6 + region.val)
        (complementSlotAt node.val slot.1.val) := by
  unfold levelThreeSlotNumerator
  rw [levelThreeComplementSlot_val]
  simp [PositiveLevelThreeData.regionCount]

/-- Reindexing a right occurrence exposes the left-child row of the original slot. -/
theorem levelThreeOccurrenceLaw_count_complement_right
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (slot : LevelThreeValidSlot node) (word : SplitWord 1) :
    (levelThreeOccurrenceLaw data node region sigma hvalid c).count
        (levelThreeComplementSlot node slot, .right) word =
      levelThreeSlotNumerator data node region (levelThreeComplementSlot node slot) *
        levelTwoChildDenominator *
          levelThreeLeftChildWordCount data node region sigma slot c word := by
  rw [levelThreeOccurrenceLaw_count_right,
    levelThreeRightChildWordCount_eq_left_complementSlot]

/-- Word-indexed form of the evaluator's symmetrized child-row contribution. -/
def levelThreeSymmetrizedSlotWordCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) : ℕ :=
  orderedSplitNumerator data node.val region.val slot.1.val *
    levelThreeLeftChildWordCount data node region sigma slot c word * childRowRescale

/-- The evaluator's symmetrized word row is exactly the raw left occurrence plus the canonically
reindexed raw right occurrence.  At a fixed point these remain two labelled summands. -/
theorem levelThreeSymmetrizedSlotWordCount_eq_labelled_occurrence_pair
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    levelThreeSymmetrizedSlotWordCount data node region sigma slot c word =
      (levelThreeOccurrenceLaw data node region sigma hvalid c).count
          (slot, .left) word +
        (levelThreeOccurrenceLaw data node region sigma hvalid c).count
          (levelThreeComplementSlot node slot, .right) word := by
  rw [levelThreeOccurrenceLaw_count_left,
    levelThreeOccurrenceLaw_count_complement_right]
  unfold levelThreeSymmetrizedSlotWordCount orderedSplitNumerator
  rw [← levelThreeSlotNumerator_complement data node region slot]
  rw [childRowRescale_eq_levelTwoChildDenominator]
  simp only [levelThreeSlotNumerator, PositiveLevelThreeData.regionCount]
  ring

/-- Exact complete-split table on one concrete child constituent. -/
noncomputable def levelThreeOccurrenceExactCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 1) : ℕ :=
  recursiveOccurrenceExactProfile (levelThreeOccurrenceCoarseIndex node sigma)
    (levelThreeOccurrenceLaw data node region sigma hvalid c) q word

/-- The exact raw-occurrence table is the sum of symmetrized evaluator rows over child slots. -/
theorem levelThreeOccurrenceExactCount_eq_sum_symmetrized
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 1) :
    levelThreeOccurrenceExactCount data node region sigma hvalid c q word =
      ∑ slot : LevelThreeValidSlot node,
        if levelThreeSlotCoarseIndex node sigma slot = q then
          levelThreeSymmetrizedSlotWordCount data node region sigma slot c word
        else 0 := by
  unfold levelThreeOccurrenceExactCount
  rw [show recursiveOccurrenceExactProfile (levelThreeOccurrenceCoarseIndex node sigma)
      (levelThreeOccurrenceLaw data node region sigma hvalid c) q word =
      recursiveComplementaryOccurrencePooledProfile
        (levelThreeComplementSlotPerm node) (levelThreeSlotCoarseIndex node sigma)
        (levelThreeOccurrenceLaw data node region sigma hvalid c) q word by
    unfold recursiveOccurrenceExactProfile recursiveComplementaryOccurrencePooledProfile
      recursiveOccurrencePooledProfile
    apply Finset.sum_congr rfl
    intro occurrence _
    rw [levelThreeOccurrenceCoarseIndex_eq_childState]]
  rw [recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
  apply Finset.sum_congr rfl
  intro slot _
  rw [levelThreeComplementSlotPerm_symm]
  change
    (if levelThreeSlotCoarseIndex node sigma slot = q then
        (levelThreeOccurrenceLaw data node region sigma hvalid c).count
            (slot, .left) word +
          (levelThreeOccurrenceLaw data node region sigma hvalid c).count
            (levelThreeComplementSlot node slot, .right) word
      else 0) = _
  rw [← levelThreeSymmetrizedSlotWordCount_eq_labelled_occurrence_pair
    data node region sigma hvalid slot c word]

/-- Positive logical-`Y` pooled occurrence table. -/
noncomputable def levelThreeOccurrenceYPooledCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (part : PUnit) (y : ℕ) (word : SplitWord 1) : ℕ :=
  recursiveOccurrenceYPooledProfile (levelThreeOccurrenceCoarseIndex node sigma)
    (levelThreeOccurrenceLaw data node region sigma hvalid .Y) part y word

/-- The positive `Y` occurrence table is the sum of the evaluator's symmetrized rows in the
requested compatibility cell. -/
theorem levelThreeOccurrenceYPooledCount_eq_sum_symmetrized
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (part : PUnit) (y : ℕ) (word : SplitWord 1) :
    levelThreeOccurrenceYPooledCount data node region sigma hvalid part y word =
      ∑ slot : LevelThreeValidSlot node,
        if yCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot) = .pooled part y then
          levelThreeSymmetrizedSlotWordCount data node region sigma slot .Y word
        else 0 := by
  calc
    levelThreeOccurrenceYPooledCount data node region sigma hvalid part y word =
      recursiveComplementaryOccurrencePooledProfile
        (levelThreeComplementSlotPerm node)
        (fun slot ↦ yCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot))
        (levelThreeOccurrenceLaw data node region sigma hvalid .Y)
        (.pooled part y) word := by
          unfold levelThreeOccurrenceYPooledCount recursiveOccurrenceYPooledProfile
            recursiveComplementaryOccurrencePooledProfile recursiveOccurrencePooledProfile
          apply Finset.sum_congr rfl
          intro occurrence _
          simp only [levelThreeOccurrenceCoarseIndex_eq_childState]
    _ = _ := by
      rw [recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
      apply Finset.sum_congr rfl
      intro slot _
      rw [levelThreeComplementSlotPerm_symm]
      change
        (if yCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot) = .pooled part y then
            (levelThreeOccurrenceLaw data node region sigma hvalid .Y).count
                (slot, .left) word +
              (levelThreeOccurrenceLaw data node region sigma hvalid .Y).count
                (levelThreeComplementSlot node slot, .right) word
          else 0) = _
      rw [← levelThreeSymmetrizedSlotWordCount_eq_labelled_occurrence_pair
        data node region sigma hvalid slot .Y word]

/-- Positive logical-`Z` pooled occurrence table. -/
noncomputable def levelThreeOccurrenceZPooledCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (part : PUnit) (z : ℕ) (word : SplitWord 1) : ℕ :=
  recursiveOccurrenceZPooledProfile (levelThreeOccurrenceCoarseIndex node sigma)
    (levelThreeOccurrenceLaw data node region sigma hvalid .Z) part z word

/-- The positive `Z` occurrence table is the sum of the evaluator's symmetrized rows in the
requested compatibility cell. -/
theorem levelThreeOccurrenceZPooledCount_eq_sum_symmetrized
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (part : PUnit) (z : ℕ) (word : SplitWord 1) :
    levelThreeOccurrenceZPooledCount data node region sigma hvalid part z word =
      ∑ slot : LevelThreeValidSlot node,
        if zCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot) = .pooled part z then
          levelThreeSymmetrizedSlotWordCount data node region sigma slot .Z word
        else 0 := by
  calc
    levelThreeOccurrenceZPooledCount data node region sigma hvalid part z word =
      recursiveComplementaryOccurrencePooledProfile
        (levelThreeComplementSlotPerm node)
        (fun slot ↦ zCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot))
        (levelThreeOccurrenceLaw data node region sigma hvalid .Z)
        (.pooled part z) word := by
          unfold levelThreeOccurrenceZPooledCount recursiveOccurrenceZPooledProfile
            recursiveComplementaryOccurrencePooledProfile recursiveOccurrencePooledProfile
          apply Finset.sum_congr rfl
          intro occurrence _
          simp only [levelThreeOccurrenceCoarseIndex_eq_childState]
    _ = _ := by
      rw [recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
      apply Finset.sum_congr rfl
      intro slot _
      rw [levelThreeComplementSlotPerm_symm]
      change
        (if zCompatibilityCell (levelThreeSlotCoarseIndex node sigma slot) = .pooled part z then
            (levelThreeOccurrenceLaw data node region sigma hvalid .Z).count
                (slot, .left) word +
              (levelThreeOccurrenceLaw data node region sigma hvalid .Z).count
                (levelThreeComplementSlot node slot, .right) word
          else 0) = _
      rw [← levelThreeSymmetrizedSlotWordCount_eq_labelled_occurrence_pair
        data node region sigma hvalid slot .Z word]

/-- Finite boundary symmetries needed to turn the raw occurrence tables into compatibility
targets.  Generated clients check only these local equalities. -/
def LevelThreeOccurrenceBoundaryValid
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma) : Prop :=
  (∀ q : CoarseIndex PUnit.{1}, q.z = 0 → ∀ word,
    levelThreeOccurrenceExactCount data node region sigma hvalid .Y q word =
      levelThreeOccurrenceExactCount data node region sigma hvalid .X q
        (complementSplitWord word)) ∧
  (∀ q : CoarseIndex PUnit.{1}, q.y = 0 → ∀ word,
    levelThreeOccurrenceExactCount data node region sigma hvalid .Z q word =
      levelThreeOccurrenceExactCount data node region sigma hvalid .X q
        (complementSplitWord word)) ∧
  (∀ q : CoarseIndex PUnit.{1}, q.x = 0 → ∀ word,
    levelThreeOccurrenceExactCount data node region sigma hvalid .Z q word =
      levelThreeOccurrenceExactCount data node region sigma hvalid .Y q
        (complementSplitWord word))

/-- Complete level-three semantic target package derived from raw labelled occurrences. -/
noncomputable def levelThreeOccurrenceTargetData
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (hboundary : LevelThreeOccurrenceBoundaryValid data node region sigma hvalid) :
    RecursiveOccurrenceTargetData (depth := 1) (levelThreeOccurrenceCoarseIndex node sigma)
      (fun slot ↦ levelThreeSlotNumerator data node region slot *
        (levelTwoChildDenominator * levelTwoChildDenominator)) where
  law c := levelThreeOccurrenceLaw data node region sigma hvalid c
  yBoundary := hboundary.1
  zBoundaryOfX := hboundary.2.1
  zBoundaryOfY := hboundary.2.2

end MatrixMultiplication.SimplifiedRecursiveLevelThreeOccurrences
