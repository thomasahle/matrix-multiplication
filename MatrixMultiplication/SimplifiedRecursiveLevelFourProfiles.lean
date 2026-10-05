/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveChildProfiles
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore

/-!
# Exact level-four parent profiles in the simplified recursive certificate

The level-four recurrence independently concatenates two exact depth-two child profiles of size
`2^48` and mixes them by the literal ordered top-split row.  Only nonzero top-split slots consume
serialized beta-three rows: inactive rows are intentionally omitted by the compact certificate.
This file therefore indexes the recursive mixture by the finite support of that row, rather than
requiring dummy normalized profiles at zero-weight slots.

The resulting `ExactInterfaceTermParameters 3` derives parent normalization from the generic exact
recursion theorem.  A generated client need check child normalization only on the active support.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedRecursiveParentTerms

/-- Structurally valid top-split slots carrying nonzero mass in one parent row. -/
def levelFourActiveSlots
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) : Finset (LevelFourValidSlot parent) :=
  Finset.univ.filter fun slot ↦ levelFourSlotNumerator top root region parent slot ≠ 0

/-- A valid parent-local slot that is actually consumed by the recursive mixture. -/
abbrev LevelFourActiveSlot
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :=
  levelFourActiveSlots top root region parent

/-- Membership in the active-slot subtype exposes the nonzero top-split numerator. -/
theorem levelFourActiveSlot_numerator_ne
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot top root region parent) :
    levelFourSlotNumerator top root region parent slot.1 ≠ 0 := by
  simpa [levelFourActiveSlots] using slot.2

/-- Removing zero-weight slots does not change the literal top-split subtotal.

Proof sketch: express the subtype sum as a sum over the filtered finite set.  Every discarded
summand is definitionally zero, so the filtered and unfiltered sums agree. -/
theorem sum_levelFourActiveSlot_numerator
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1) =
      levelFourSamples top root region parent := by
  calc
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1) =
        ∑ slot ∈ levelFourActiveSlots top root region parent,
          levelFourSlotNumerator top root region parent slot :=
      (Finset.sum_subtype (levelFourActiveSlots top root region parent)
        (fun _ ↦ Iff.rfl) (levelFourSlotNumerator top root region parent)).symm
    _ = ∑ slot : LevelFourValidSlot parent,
        levelFourSlotNumerator top root region parent slot := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hnot
      simpa [levelFourActiveSlots] using hnot
    _ = levelFourSamples top root region parent := rfl

/-- Exact count attached to one depth-two word in a serialized beta-three row. -/
def levelThreeWordCountAt
    (betaThree : BetaThreeRows) (row coordinate total : ℕ)
    (word : SplitWord 2) : ℕ :=
  if splitWordWeight word = total then
    betaThreeNumeratorFrom betaThree row coordinate
      ((ternarySupportCodes levelThreeWordLength total).idxOf (splitWordTwoCode word))
  else 0

/-- Every nonzero guarded beta-three count has the advertised aggregate coordinate. -/
theorem levelThreeWordCountAt_supported
    (betaThree : BetaThreeRows) (row coordinate total : ℕ)
    (word : SplitWord 2)
    (hcount : levelThreeWordCountAt betaThree row coordinate total word ≠ 0) :
    splitWordWeight word = total := by
  by_contra hweight
  exact hcount (by simp [levelThreeWordCountAt, hweight])

/-- The proof-free parent lookup agrees with the typed positive-parent enumeration. -/
theorem parentShapeAt_eq_positiveLevelFourShape
    (parent : Fin positiveLevelFourShapeCount) :
    parentShapeAt parent.val = positiveLevelFourShape parent := by
  unfold parentShapeAt positiveLevelFourShape
  rw [List.getElem?_eq_getElem (by
    rw [positiveLevelFourShapes_length]
    exact parent.isLt)]
  rfl

/-- The proof-free evaluator pair lookup agrees with the typed valid-slot lookup. -/
theorem pairAt_eq_levelFourPairAtSlot
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    pairAt parent.val slot.1.val = levelFourPairAtSlot parent slot.1 slot.2 := by
  unfold pairAt levelFourPairAtSlot
  rw [parentShapeAt_eq_positiveLevelFourShape]
  rw [List.getElem?_eq_getElem slot.2]
  rfl

/-- Exact depth-three profile count for the ordered left child. -/
def levelFourLeftChildWordCount
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2) : ℕ :=
  let pair := levelFourPairAtSlot parent slot.1 slot.2
  levelThreeWordCountAt betaThree
    (shapeEightIndex pair.1 * 6 + region.val) (coordinateOfLeg (sigma c)).val
    ((levelFourChildShape parent sigma slot).get c) word

/-- A level-four parent has twice the level-three child total in every orientation. -/
theorem levelFourParentIndex_total_twice
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    (levelFourParentIndex parent sigma).count .X +
        (levelFourParentIndex parent sigma).count .Y +
        (levelFourParentIndex parent sigma).count .Z = 2 * 8 := by
  simpa [Tensor.sum_leg] using (levelFourParentIndex parent sigma).total

/-- Exact depth-three profile count for the labelled right child. -/
def levelFourRightChildWordCount
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2) : ℕ :=
  let pair := levelFourPairAtSlot parent slot.1 slot.2
  let parentTotal := levelFourParentIndex_total_twice parent sigma
  let right := RecursiveChildShape.complement parentTotal
    (levelFourChildShape parent sigma slot)
  levelThreeWordCountAt betaThree
    (shapeEightIndex pair.2 * 6 + region.val) (coordinateOfLeg (sigma c)).val
    (right.get c) word

/-- The stored right child has exactly the intrinsic complementary coordinate in every
orientation. -/
theorem levelFourRightChild_evaluatorTotal
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) :
    shapeCoordinate (levelFourPairAtSlot parent slot.1 slot.2).2
        (coordinateOfLeg (sigma c)).val =
      (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot)).get c := by
  calc
    shapeCoordinate (levelFourPairAtSlot parent slot.1 slot.2).2
        (coordinateOfLeg (sigma c)).val =
        (levelFourPairAtSlot parent slot.1 slot.2).2.leg (sigma c) :=
      shapeCoordinate_coordinateOfLeg _ _
    _ = (levelFourChildShape parent sigma
        (levelFourComplementSlot parent slot)).get c := by
      rw [levelFourChildShape_get, levelFourComplementSlot_leftChild]
      rfl
    _ = (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot)).get c :=
      congrArg (fun child ↦ child.get c) (levelFourChildShape_complement parent sigma slot)

/-- Finite normalization check for every labelled depth-three child row consumed by one
level-four parent.  Zero-weight top slots impose no condition because they contribute nothing to
the recursive profile and their beta-three rows are deliberately absent from the compact
certificate. -/
def LevelFourChildRowsValid
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) : Prop :=
  ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
    (∑ word, levelFourLeftChildWordCount betaThree region parent sigma slot c word =
        levelFourChildSamples) ∧
      (∑ word, levelFourRightChildWordCount betaThree region parent sigma slot c word =
        levelFourChildSamples)

/-- Exact complete-split profile of one ordered level-three left child. -/
def levelFourLeftChildProfile
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (slot : LevelFourActiveSlot top root region parent) (c : Leg) :
    CompleteSplitProfile 2 ((levelFourChildShape parent sigma slot.1).get c)
      levelFourChildSamples :=
  CompleteSplitProfile.ofCounts
    (levelFourLeftChildWordCount betaThree region parent sigma slot.1 c)
    (hvalid slot.1 c (levelFourActiveSlot_numerator_ne top root region parent slot)).1
    (levelThreeWordCountAt_supported betaThree
      (shapeEightIndex (levelFourPairAtSlot parent slot.1.1 slot.1.2).1 * 6 + region.val)
      (coordinateOfLeg (sigma c)).val ((levelFourChildShape parent sigma slot.1).get c))

/-- Reading a constructed left child profile returns its guarded beta-three row. -/
@[simp] theorem levelFourLeftChildProfile_counts
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (slot : LevelFourActiveSlot top root region parent) (c : Leg) (word : SplitWord 2) :
    (levelFourLeftChildProfile top betaThree root region parent sigma hvalid slot c).counts word =
      levelFourLeftChildWordCount betaThree region parent sigma slot.1 c word :=
  rfl

/-- Exact complete-split profile of the labelled complementary level-three child. -/
def levelFourRightChildProfile
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (slot : LevelFourActiveSlot top root region parent) (c : Leg) :
    CompleteSplitProfile 2
      ((RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot.1)).get c) levelFourChildSamples :=
  CompleteSplitProfile.ofCounts
    (levelFourRightChildWordCount betaThree region parent sigma slot.1 c)
    (hvalid slot.1 c (levelFourActiveSlot_numerator_ne top root region parent slot)).2
    (levelThreeWordCountAt_supported betaThree
      (shapeEightIndex (levelFourPairAtSlot parent slot.1.1 slot.1.2).2 * 6 + region.val)
      (coordinateOfLeg (sigma c)).val
      ((RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot.1)).get c))

/-- Reading a constructed right child profile returns its guarded complementary beta-three row. -/
@[simp] theorem levelFourRightChildProfile_counts
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (slot : LevelFourActiveSlot top root region parent) (c : Leg) (word : SplitWord 2) :
    (levelFourRightChildProfile top betaThree root region parent sigma hvalid slot c).counts word =
      levelFourRightChildWordCount betaThree region parent sigma slot.1 c word :=
  rfl

/-- Product-profile component belonging to one ordered top split and tensor leg. -/
def levelFourProfileComponent
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (slot : LevelFourActiveSlot top root region parent) :
    RecursiveSplitProfileComponent 2 ((levelFourParentIndex parent sigma).count c)
      levelFourChildSamples levelFourChildSamples where
  leftTotal := (levelFourChildShape parent sigma slot.1).get c
  rightTotal :=
    (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
      (levelFourChildShape parent sigma slot.1)).get c
  total_eq := RecursiveChildShape.get_add_complement_get
    (levelFourParentIndex_total_twice parent sigma)
    (levelFourChildShape parent sigma slot.1) c
  left := levelFourLeftChildProfile top betaThree root region parent sigma hvalid slot c
  right := levelFourRightChildProfile top betaThree root region parent sigma hvalid slot c

/-- Exact level-four parent interface term obtained from the top split law and the serialized
depth-three child profiles. -/
def levelFourRecursiveParentTerm
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma) :
    ExactInterfaceTermParameters 3 :=
  ExactInterfaceTermParameters.ofRecursiveProfiles
    (levelFourParentIndex parent sigma)
    (fun slot : LevelFourActiveSlot top root region parent ↦
      levelFourSlotNumerator top root region parent slot.1)
    (sum_levelFourActiveSlot_numerator top root region parent)
    (levelFourProfileComponent top betaThree root region parent sigma hvalid)

/-- Proof-independent form of the exact level-four recursive parent count. -/
def levelFourSemanticParentWordCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) (c : Leg) (word : SplitWord 3) : ℕ :=
  ∑ slot : LevelFourActiveSlot top root region parent,
    levelFourSlotNumerator top root region parent slot.1 *
    (levelFourLeftChildWordCount betaThree region parent sigma slot.1 c
        (splitWordSuccEquiv 2 word).1 *
      levelFourRightChildWordCount betaThree region parent sigma slot.1 c
        (splitWordSuccEquiv 2 word).2)

/-- Count read from the evaluator's padded beta-four row at one intrinsic split word. -/
def levelFourEvaluatorParentWordCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) (c : Leg) (word : SplitWord 3) : ℕ :=
  let total := (levelFourParentIndex parent sigma).count c
  if splitWordWeight word = total then
    (betaFourParentRow top betaThree root.val region.val parent.val
      (coordinateOfLeg (sigma c)).val)[
        (ternarySupportCodes parentWordLength total).idxOf
          ((word ⟨0, by decide⟩ : ℕ) * 2187 +
            (word ⟨1, by decide⟩ : ℕ) * 729 +
              (word ⟨2, by decide⟩ : ℕ) * 243 +
                (word ⟨3, by decide⟩ : ℕ) * 81 +
                  (word ⟨4, by decide⟩ : ℕ) * 27 +
                    (word ⟨5, by decide⟩ : ℕ) * 9 +
                      (word ⟨6, by decide⟩ : ℕ) * 3 +
                        (word ⟨7, by decide⟩ : ℕ))]?.getD 0
  else 0

/-- Nonzero evaluator parent counts have the advertised parent coordinate. -/
theorem levelFourEvaluatorParentWordCount_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) (c : Leg) (word : SplitWord 3)
    (hcount : levelFourEvaluatorParentWordCount
      top betaThree root region parent sigma c word ≠ 0) :
    splitWordWeight word = (levelFourParentIndex parent sigma).count c := by
  by_contra hweight
  exact hcount (by simp [levelFourEvaluatorParentWordCount, hweight])

/-- Finite statement that the evaluator's beta-four serialization is exactly the intrinsic
recursive profile, word for word. -/
def LevelFourEvaluatorRowsAgree
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) : Prop :=
  ∀ c word,
    levelFourEvaluatorParentWordCount top betaThree root region parent sigma c word =
      levelFourSemanticParentWordCount top betaThree root region parent sigma c word

/-- The exact parent multiplicity is the literal top-split subtotal times `2^96`. -/
@[simp] theorem levelFourRecursiveParentTerm_multiplicity
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma) :
    (levelFourRecursiveParentTerm top betaThree root region parent sigma hvalid).multiplicity =
      levelFourParentSamples top root region parent := by
  norm_num [levelFourRecursiveParentTerm, levelFourParentSamples,
    levelFourSamples, levelFourChildProductScale, levelFourChildSamples, childBits]

/-- Pointwise integer recurrence for every depth-three complete-split parent word. -/
@[simp] theorem levelFourRecursiveParentTerm_split_counts
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (word : SplitWord 3) :
    ((levelFourRecursiveParentTerm top betaThree root region parent sigma hvalid).split c).counts
        word =
      levelFourSemanticParentWordCount top betaThree root region parent sigma c word := by
  simp only [levelFourRecursiveParentTerm,
    ExactInterfaceTermParameters.ofRecursiveProfiles_split_counts,
    levelFourProfileComponent, levelFourLeftChildProfile_counts,
    levelFourRightChildProfile_counts, levelFourSemanticParentWordCount]

/-- Child normalization and wordwise agreement derive normalization of every serialized
beta-four parent row. -/
theorem levelFourEvaluatorParentRowsValid_of_childRows
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : LevelFourEvaluatorRowsAgree top betaThree root region parent sigma) :
    ∀ c, ∑ word,
      levelFourEvaluatorParentWordCount top betaThree root region parent sigma c word =
        levelFourParentSamples top root region parent := by
  intro c
  calc
    (∑ word,
        levelFourEvaluatorParentWordCount top betaThree root region parent sigma c word) =
        ∑ word, ((levelFourRecursiveParentTerm
          top betaThree root region parent sigma hchild).split c).counts word := by
      apply Finset.sum_congr rfl
      intro word _
      rw [hrows c word, levelFourRecursiveParentTerm_split_counts]
    _ = (levelFourRecursiveParentTerm top betaThree root region parent sigma hchild).multiplicity :=
      CompleteSplitProfile.sum_counts
        ((levelFourRecursiveParentTerm top betaThree root region parent sigma hchild).split c)
    _ = levelFourParentSamples top root region parent :=
      levelFourRecursiveParentTerm_multiplicity
        top betaThree root region parent sigma hchild

/-- Evaluator-facing exact level-four term, with normalization derived from the recursive
construction rather than assumed. -/
def levelFourCheckedParentTerm
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : LevelFourEvaluatorRowsAgree top betaThree root region parent sigma) :
    ExactInterfaceTermParameters 3 :=
  ExactInterfaceTermParameters.ofCountRows
    (levelFourParentIndex parent sigma)
    (levelFourEvaluatorParentWordCount top betaThree root region parent sigma)
    (levelFourEvaluatorParentRowsValid_of_childRows
      top betaThree root region parent sigma hchild hrows)
    (levelFourEvaluatorParentWordCount_supported
      top betaThree root region parent sigma)

/-- The checked beta-four term has exactly the semantic recursive counts. -/
theorem levelFourCheckedParentTerm_split_counts
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : LevelFourEvaluatorRowsAgree top betaThree root region parent sigma)
    (c : Leg) (word : SplitWord 3) :
    ((levelFourCheckedParentTerm top betaThree root region parent sigma hchild hrows).split c).counts
        word =
      ((levelFourRecursiveParentTerm top betaThree root region parent sigma hchild).split c).counts
        word := by
  rw [levelFourRecursiveParentTerm_split_counts]
  exact hrows c word

end MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
