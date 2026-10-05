/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactCompleteSplitRecursion
import MatrixMultiplication.SimplifiedRecursiveParentTerms

/-!
# Exact level-two child profiles in the simplified recursive certificate

This module turns quotient-pushed level-two rows into exact complete-split profiles and uses them
to construct a level-three parent interface term by the finite recursive-profile theorem.  The
quotient slot map is explicit throughout the semantic API; the historical public names are thin
sorted-pair specializations.  The parent row total is therefore derived from child normalization
and the ordered split subtotal; it is not a semantic hypothesis.

The remaining certificate-facing predicate is deliberately finite and local: every level-two
child row used by one parent must sum to `2^12`.  Generated clients can discharge it directly
from the checked sparse row dictionaries.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveChildProfiles

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedRecursiveParentTerms

/-- Common denominator of every exact level-two child row.  The qualified alias records that
these rows come from the complete-split recurrence, while avoiding a collision with the volume
reconstruction module's definitionally equal denominator. -/
abbrev levelTwoChildDenominator : ℕ :=
  MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localDenominator

/-- Big-endian ternary code of one depth-one complete-split word. -/
def splitWordOneCode (word : SplitWord 1) : ℕ :=
  (word ⟨0, by decide⟩ : ℕ) * 3 + (word ⟨1, by decide⟩ : ℕ)

/-- Exact quotient count attached to a depth-one word for a supplied slot map.

The explicit total guard prevents `List.idxOf`'s fallback slot from receiving mass outside the
advertised coordinate.  Passing the quotient map explicitly is important: the sorted-pair and
total-weight certificates use the same primary-table type but different pushforwards.
-/
def levelTwoWordCountAtFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node region slot coordinate total : ℕ)
    (word : SplitWord 1) : ℕ :=
  if splitWordWeight word = total then
    quotientBetaTwoNumerator supportSlot data node region slot coordinate
      ((ternarySupportCodes levelTwoWordLength total).idxOf (splitWordOneCode word))
  else 0

/-- Sorted-pair specialization of the guarded depth-one word count. -/
def levelTwoWordCountAt
    (data : PrimaryTables) (node region slot coordinate total : ℕ)
    (word : SplitWord 1) : ℕ :=
  levelTwoWordCountAtFor sortedPairSupportSlot data node region slot coordinate total word

/-- A nonzero quotient-parametric child count has its advertised aggregate coordinate. -/
theorem levelTwoWordCountAtFor_supported
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node region slot coordinate total : ℕ)
    (word : SplitWord 1)
    (hcount : levelTwoWordCountAtFor supportSlot data node region slot coordinate total word ≠ 0) :
    splitWordWeight word = total := by
  by_contra hweight
  exact hcount (by simp [levelTwoWordCountAtFor, hweight])

/-- Every nonzero guarded child count has its advertised aggregate coordinate. -/
theorem levelTwoWordCountAt_supported
    (data : PrimaryTables) (node region slot coordinate total : ℕ)
    (word : SplitWord 1)
    (hcount : levelTwoWordCountAt data node region slot coordinate total word ≠ 0) :
    splitWordWeight word = total := by
  exact levelTwoWordCountAtFor_supported sortedPairSupportSlot
    data node region slot coordinate total word hcount

/-- The canonical complement slot agrees definitionally with the evaluator's proof-free lookup. -/
theorem levelThreeComplementSlot_val
    (node : Fin PositiveLevelThreeData.nodeCount)
    (slot : LevelThreeValidSlot node) :
    (levelThreeComplementSlot node slot).1.val = complementSlotAt node.val slot.1.val := by
  rfl

/-- Exact left-child row count for a supplied quotient in an arbitrary logical orientation. -/
def levelThreeLeftChildWordCountFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) : ℕ :=
  levelTwoWordCountAtFor supportSlot data node.val region.val slot.1.val
    (coordinateOfLeg (sigma c)).val ((levelThreeChildShape node sigma slot).get c) word

/-- Sorted-pair specialization of the ordered left-child row. -/
def levelThreeLeftChildWordCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) : ℕ :=
  levelThreeLeftChildWordCountFor sortedPairSupportSlot
    data node region sigma slot c word

/-- Exact right-child row count for a supplied quotient, read from the complementary slot. -/
def levelThreeRightChildWordCountFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) : ℕ :=
  let right := levelThreeComplementSlot node slot
  levelTwoWordCountAtFor supportSlot data node.val region.val right.1.val
    (coordinateOfLeg (sigma c)).val ((levelThreeChildShape node sigma right).get c) word

/-- Sorted-pair specialization of the labelled complementary-child row. -/
def levelThreeRightChildWordCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) : ℕ :=
  levelThreeRightChildWordCountFor sortedPairSupportSlot
    data node region sigma slot c word

/-- The left intrinsic coordinate is exactly the physical coordinate used by the evaluator. -/
theorem levelThreeLeftChild_evaluatorTotal
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    shapeCoordinate (splitShapeAt node.val slot.1.val) (coordinateOfLeg (sigma c)).val =
      (levelThreeChildShape node sigma slot).get c := by
  rw [levelThreeChildShape_get, shapeCoordinate_coordinateOfLeg]
  rfl

/-- The right intrinsic coordinate is the evaluator coordinate at the canonical complement
slot. -/
theorem levelThreeRightChild_evaluatorTotal
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    shapeCoordinate (splitShapeAt node.val (levelThreeComplementSlot node slot).1.val)
        (coordinateOfLeg (sigma c)).val =
      (levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c := by
  rw [levelThreeChildShape_get, shapeCoordinate_coordinateOfLeg]
  rfl

/-- Finite normalization check for every labelled child row of a supplied quotient. -/
def LevelThreeChildRowsValidFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  ∀ slot c,
    (∑ word, levelThreeLeftChildWordCountFor supportSlot data node region sigma slot c word =
        levelTwoChildDenominator) ∧
      (∑ word, levelThreeRightChildWordCountFor supportSlot data node region sigma slot c word =
        levelTwoChildDenominator)

/-- Sorted-pair specialization of labelled child-row normalization. -/
def LevelThreeChildRowsValid
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  LevelThreeChildRowsValidFor sortedPairSupportSlot data node region sigma

/-- Exact complete-split profile of one ordered left child for a supplied quotient. -/
def levelThreeLeftChildProfileFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    CompleteSplitProfile 1 ((levelThreeChildShape node sigma slot).get c)
      levelTwoChildDenominator :=
  CompleteSplitProfile.ofCounts
    (levelThreeLeftChildWordCountFor supportSlot data node region sigma slot c)
    (hvalid slot c).1
    (levelTwoWordCountAtFor_supported supportSlot data node.val region.val slot.1.val
      (coordinateOfLeg (sigma c)).val ((levelThreeChildShape node sigma slot).get c))

/-- Sorted-pair specialization of the ordered left-child profile. -/
def levelThreeLeftChildProfile
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    CompleteSplitProfile 1 ((levelThreeChildShape node sigma slot).get c)
      levelTwoChildDenominator :=
  levelThreeLeftChildProfileFor sortedPairSupportSlot
    data node region sigma hvalid slot c

/-- Reading a quotient-parametric left profile returns its guarded count table. -/
@[simp] theorem levelThreeLeftChildProfileFor_counts
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    (levelThreeLeftChildProfileFor supportSlot data node region sigma hvalid slot c).counts word =
      levelThreeLeftChildWordCountFor supportSlot data node region sigma slot c word :=
  rfl

/-- Reading the constructed left profile returns the evaluator's guarded count table. -/
@[simp] theorem levelThreeLeftChildProfile_counts
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    (levelThreeLeftChildProfile data node region sigma hvalid slot c).counts word =
      levelThreeLeftChildWordCount data node region sigma slot c word :=
  rfl

/-- Exact complementary-child profile for a supplied quotient. -/
def levelThreeRightChildProfileFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    CompleteSplitProfile 1
      ((levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c)
      levelTwoChildDenominator :=
  CompleteSplitProfile.ofCounts
    (levelThreeRightChildWordCountFor supportSlot data node region sigma slot c)
    (hvalid slot c).2
    (levelTwoWordCountAtFor_supported supportSlot data node.val region.val
      (levelThreeComplementSlot node slot).1.val (coordinateOfLeg (sigma c)).val
      ((levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c))

/-- Sorted-pair specialization of the labelled complementary-child profile. -/
def levelThreeRightChildProfile
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) :
    CompleteSplitProfile 1
      ((levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c)
      levelTwoChildDenominator :=
  levelThreeRightChildProfileFor sortedPairSupportSlot
    data node region sigma hvalid slot c

/-- Reading a quotient-parametric right profile returns its complementary count table. -/
@[simp] theorem levelThreeRightChildProfileFor_counts
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    (levelThreeRightChildProfileFor supportSlot data node region sigma hvalid slot c).counts word =
      levelThreeRightChildWordCountFor supportSlot data node region sigma slot c word :=
  rfl

/-- Reading the constructed right profile returns the complementary guarded count table. -/
@[simp] theorem levelThreeRightChildProfile_counts
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (slot : LevelThreeValidSlot node) (c : Leg) (word : SplitWord 1) :
    (levelThreeRightChildProfile data node region sigma hvalid slot c).counts word =
      levelThreeRightChildWordCount data node region sigma slot c word :=
  rfl

/-- A level-three parent has twice the level-two child total in every orientation. -/
theorem levelThreeParentIndex_total_twice
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation) :
    (levelThreeParentIndex node sigma).count .X +
        (levelThreeParentIndex node sigma).count .Y +
        (levelThreeParentIndex node sigma).count .Z = 2 * 4 := by
  simpa [Tensor.sum_leg] using (levelThreeParentIndex node sigma).total

/-- Product-profile component for one quotient, ordered split slot, and tensor leg. -/
def levelThreeProfileComponentFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (c : Leg) (slot : LevelThreeValidSlot node) :
    RecursiveSplitProfileComponent 1 ((levelThreeParentIndex node sigma).count c)
      levelTwoChildDenominator levelTwoChildDenominator where
  leftTotal := (levelThreeChildShape node sigma slot).get c
  rightTotal :=
    (levelThreeChildShape node sigma (levelThreeComplementSlot node slot)).get c
  total_eq := by
    rw [levelThreeChildShape_complement]
    exact RecursiveChildShape.get_add_complement_get
      (levelThreeParentIndex_total_twice node sigma)
      (levelThreeChildShape node sigma slot) c
  left := levelThreeLeftChildProfileFor supportSlot data node region sigma hvalid slot c
  right := levelThreeRightChildProfileFor supportSlot data node region sigma hvalid slot c

/-- Sorted-pair specialization of a product-profile component. -/
def levelThreeProfileComponent
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (slot : LevelThreeValidSlot node) :
    RecursiveSplitProfileComponent 1 ((levelThreeParentIndex node sigma).count c)
      levelTwoChildDenominator levelTwoChildDenominator :=
  levelThreeProfileComponentFor sortedPairSupportSlot
    data node region sigma hvalid c slot

/-- Exact parent interface term for a supplied quotient.

Its row normalization is a consequence of the ordered split law and normalized child profiles. -/
def levelThreeRecursiveParentTermFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  ExactInterfaceTermParameters.ofRecursiveProfiles
    (levelThreeParentIndex node sigma)
    (levelThreeSlotNumerator data node region) rfl
    (levelThreeProfileComponentFor supportSlot data node region sigma hvalid)

/-- Sorted-pair specialization of the exact recursive parent term. -/
def levelThreeRecursiveParentTerm
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  levelThreeRecursiveParentTermFor sortedPairSupportSlot
    data node region sigma hvalid

/-- Proof-independent recursive parent count for a supplied quotient.

Generated row comparisons use this function so their proposition does not depend on a proof term
for child normalization. -/
def levelThreeSemanticParentWordCountFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2) : ℕ :=
  ∑ slot, levelThreeSlotNumerator data node region slot *
    (levelThreeLeftChildWordCountFor supportSlot data node region sigma slot c
        (splitWordSuccEquiv 1 word).1 *
      levelThreeRightChildWordCountFor supportSlot data node region sigma slot c
        (splitWordSuccEquiv 1 word).2)

/-- Sorted-pair specialization of the proof-independent recursive parent count. -/
def levelThreeSemanticParentWordCount
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2) : ℕ :=
  levelThreeSemanticParentWordCountFor sortedPairSupportSlot
    data node region sigma c word

/-- Finite statement that a quotient's padded serialization equals its recursive profile. -/
def LevelThreeEvaluatorRowsAgreeFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  ∀ c word,
    levelThreeParentWordCountFor supportSlot data node region sigma c word =
      levelThreeSemanticParentWordCountFor supportSlot data node region sigma c word

/-- Sorted-pair specialization of evaluator-row agreement. -/
def LevelThreeEvaluatorRowsAgree
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  LevelThreeEvaluatorRowsAgreeFor sortedPairSupportSlot data node region sigma

/-- A quotient-parametric parent term has the split subtotal times the child denominators. -/
@[simp] theorem levelThreeRecursiveParentTermFor_multiplicity
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma) :
    (levelThreeRecursiveParentTermFor supportSlot data node region sigma hvalid).multiplicity =
      levelThreeParentSamples data node region := by
  norm_num [levelThreeRecursiveParentTermFor, levelThreeParentSamples,
    levelThreeSamples, levelThreeChildProductScale, levelTwoChildDenominator,
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localDenominator,
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.localBits]

/-- The sorted-pair parent term has the split subtotal times the child denominators. -/
@[simp] theorem levelThreeRecursiveParentTerm_multiplicity
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    : (levelThreeRecursiveParentTerm data node region sigma hvalid).multiplicity =
      levelThreeParentSamples data node region :=
  levelThreeRecursiveParentTermFor_multiplicity sortedPairSupportSlot
    data node region sigma hvalid

/-- Pointwise integer recurrence for every parent word of a supplied quotient. -/
@[simp] theorem levelThreeRecursiveParentTermFor_split_counts
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (c : Leg) (word : SplitWord 2) :
    ((levelThreeRecursiveParentTermFor supportSlot data node region sigma hvalid).split c).counts
        word =
      levelThreeSemanticParentWordCountFor supportSlot data node region sigma c word := by
  simp only [levelThreeRecursiveParentTermFor,
    ExactInterfaceTermParameters.ofRecursiveProfiles_split_counts,
    levelThreeProfileComponentFor, levelThreeLeftChildProfileFor_counts,
    levelThreeRightChildProfileFor_counts, levelThreeSemanticParentWordCountFor]

/-- Pointwise sorted-pair recurrence for every complete-split parent word. -/
@[simp] theorem levelThreeRecursiveParentTerm_split_counts
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (c : Leg) (word : SplitWord 2) :
    ((levelThreeRecursiveParentTerm data node region sigma hvalid).split c).counts word =
      levelThreeSemanticParentWordCount data node region sigma c word :=
  levelThreeRecursiveParentTermFor_split_counts sortedPairSupportSlot
    data node region sigma hvalid c word

/-- Child normalization and row agreement derive parent normalization for any quotient.

Proof sketch: replace each serialized row by the recursive profile pointwise, sum the finite
profile, and use the already-derived multiplicity formula. -/
theorem levelThreeParentRowsValidFor_of_childRows (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma) :
    LevelThreeParentRowsValidFor supportSlot data node region sigma := by
  intro c
  calc
    (∑ word, levelThreeParentWordCountFor supportSlot data node region sigma c word) =
        ∑ word,
          ((levelThreeRecursiveParentTermFor supportSlot data node region sigma hchild).split c).counts
            word := by
      apply Finset.sum_congr rfl
      intro word _
      rw [hrows c word, levelThreeRecursiveParentTermFor_split_counts]
    _ = (levelThreeRecursiveParentTermFor supportSlot data node region sigma hchild).multiplicity := by
      apply CompleteSplitProfile.sum_counts
    _ = levelThreeParentSamples data node region :=
      levelThreeRecursiveParentTermFor_multiplicity supportSlot data node region sigma hchild

/-- Sorted-pair child normalization plus row agreement derives parent normalization. -/
theorem levelThreeParentRowsValid_of_childRows
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValid data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgree data node region sigma) :
    LevelThreeParentRowsValid data node region sigma :=
  levelThreeParentRowsValidFor_of_childRows sortedPairSupportSlot
    data node region sigma hchild hrows

/-- Quotient-parametric evaluator term whose validity is derived from exact child profiles. -/
noncomputable def levelThreeCheckedParentTermFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  levelThreeParentTermFor supportSlot data node region sigma
    (levelThreeParentRowsValidFor_of_childRows supportSlot data node region sigma hchild hrows)

/-- Sorted-pair specialization of the checked evaluator term. -/
noncomputable def levelThreeCheckedParentTerm
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValid data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgree data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  levelThreeCheckedParentTermFor sortedPairSupportSlot
    data node region sigma hchild hrows

/-- A quotient-parametric checked term has exactly its recursive parent counts. -/
theorem levelThreeCheckedParentTermFor_split_counts (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma)
    (c : Leg) (word : SplitWord 2) :
    ((levelThreeCheckedParentTermFor supportSlot data node region sigma hchild hrows).split c).counts
        word =
      ((levelThreeRecursiveParentTermFor supportSlot data node region sigma hchild).split c).counts
        word := by
  rw [levelThreeRecursiveParentTermFor_split_counts]
  exact hrows c word

/-- The checked sorted-pair term has exactly the semantic recursive parent counts. -/
theorem levelThreeCheckedParentTerm_split_counts
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValid data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgree data node region sigma)
    (c : Leg) (word : SplitWord 2) :
    ((levelThreeCheckedParentTerm data node region sigma hchild hrows).split c).counts word =
      ((levelThreeRecursiveParentTerm data node region sigma hchild).split c).counts word :=
  levelThreeCheckedParentTermFor_split_counts sortedPairSupportSlot
    data node region sigma hchild hrows c word

end MatrixMultiplication.SimplifiedRecursiveChildProfiles
