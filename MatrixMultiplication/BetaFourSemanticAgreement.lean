/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.BetaFourLocalGatherAgreement
import MatrixMultiplication.BetaFourLocalPointwise
import MatrixMultiplication.BetaThreeZeroPadding
import MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
import MatrixMultiplication.TernarySplitWordEncoding

/-!
# Semantic agreement for beta-four parent rows

The level-four evaluator scatters padded beta-three arrays into a padded beta-four row.  The
recursive tensor semantics instead index the same counts by intrinsic complete-split words.  This
module bridges those representations without evaluating a closed 1,107-cell parent array for
every certificate parent.

The bridge makes the one necessary serialization hypothesis explicit: entries beyond the true
fixed-weight support of every beta-three coordinate row are zero.  That condition is small—it
concerns the 19-cell child rows—and is separated from the generic support-code and scatter
mathematics.  A concrete certificate therefore checks zero padding once for its beta-three cache;
all beta-four parents then inherit evaluator/semantic agreement structurally.
-/

namespace MatrixMultiplication.BetaFourSemanticAgreement

open scoped BigOperators

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-! ## Canonical serialization of a recursive parent word -/

/-- The canonical eight-digit code is the base-`3^4` concatenation of its two recursive halves.

Proof sketch: `splitWordSuccEquiv 2` reads positions `0,…,3` into the left word and positions
`4,…,7` into the right word.  Substitution into the two four-digit polynomials leaves only linear
arithmetic with the fixed positional weights. -/
theorem splitWordDepthThreeCode_eq_concat (word : SplitWord 3) :
    TernarySplitWordEncoding.splitWordDepthThreeCode word =
      TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).1 *
          3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength +
        TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).2 := by
  have hleft (i : Fin 4) :
      (splitWordSuccEquiv 2 word).1 i = word ⟨i.val, by omega⟩ := by
    change word ((splitIndexSuccEquiv 2).symm (Sum.inl i)) = _
    apply congrArg word
    apply Fin.ext
    fin_cases i <;> rfl
  have hright (i : Fin 4) :
      (splitWordSuccEquiv 2 word).2 i = word ⟨4 + i.val, by omega⟩ := by
    change word ((splitIndexSuccEquiv 2).symm (Sum.inr i)) = _
    apply congrArg word
    apply Fin.ext
    fin_cases i <;> rfl
  simp only [TernarySplitWordEncoding.splitWordDepthThreeCode,
    TernarySplitWordEncoding.splitWordDepthTwoCode]
  rw [hleft ⟨0, by decide⟩, hleft ⟨1, by decide⟩,
    hleft ⟨2, by decide⟩, hleft ⟨3, by decide⟩,
    hright ⟨0, by decide⟩, hright ⟨1, by decide⟩,
    hright ⟨2, by decide⟩, hright ⟨3, by decide⟩]
  norm_num [MatrixMultiplication.BetaFourLocalGeometry.childWordLength]
  all_goals omega

/-- The canonical code belongs to the fixed-weight parent support selected by the word.

Proof sketch: rewrite the parent code and weight as concatenations, then concatenate the two
already-supported four-digit half codes. -/
theorem splitWordDepthThreeCode_mem_support (word : SplitWord 3) :
    TernarySplitWordEncoding.splitWordDepthThreeCode word ∈
      MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (splitWordWeight word) := by
  rw [splitWordDepthThreeCode_eq_concat, splitWordWeight_succ]
  exact TernarySplitWordEncoding.concat_mem_parent_support
    (TernarySplitWordEncoding.splitWordDepthTwoCode_mem_support _)
    (TernarySplitWordEncoding.splitWordDepthTwoCode_mem_support _)

/-- The local support statement for the canonical parent code is identical to the global
recurrence support statement.

Proof sketch: the lightweight local geometry intentionally reuses the executable global support
enumeration and parent-word length. -/
private theorem splitWordDepthThreeCode_mem_global_support (word : SplitWord 3) :
    TernarySplitWordEncoding.splitWordDepthThreeCode word ∈
      ternarySupportCodes parentWordLength (splitWordWeight word) := by
  simpa only [
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentWordLength_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq]
    using splitWordDepthThreeCode_mem_support word

/-- Dividing the canonical parent code by `3^4` recovers the left recursive half code. -/
theorem splitWordDepthThreeCode_div (word : SplitWord 3) :
    TernarySplitWordEncoding.splitWordDepthThreeCode word /
        3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength =
      TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).1 := by
  rw [splitWordDepthThreeCode_eq_concat]
  exact TernarySplitWordEncoding.concat_div_depthTwo _ _
    (TernarySplitWordEncoding.splitWordDepthTwoCode_lt _)

/-- Reducing the canonical parent code modulo `3^4` recovers the right recursive half code. -/
theorem splitWordDepthThreeCode_mod (word : SplitWord 3) :
    TernarySplitWordEncoding.splitWordDepthThreeCode word %
        3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength =
      TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).2 := by
  rw [splitWordDepthThreeCode_eq_concat]
  exact TernarySplitWordEncoding.concat_mod_depthTwo _ _
    (TernarySplitWordEncoding.splitWordDepthTwoCode_lt _)

/-- Quotient/remainder decoding recovers both recursive half codes at once. -/
theorem decodeDepthTwoPair_splitWordDepthThreeCode (word : SplitWord 3) :
    TernarySplitWordEncoding.decodeDepthTwoPair
        (TernarySplitWordEncoding.splitWordDepthThreeCode word) =
      (TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).1,
        TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).2) := by
  unfold TernarySplitWordEncoding.decodeDepthTwoPair
  rw [splitWordDepthThreeCode_div, splitWordDepthThreeCode_mod]

/-! ## Zero-padding semantics -/

/-- Reading the serialized code of a split word agrees with the guarded semantic word count.

The premise is deliberately row-local: it says only that entries beyond this fixed-weight
support are zero.  Global cache clients obtain it from `BetaThreeRowsHaveZeroPadding`.

Proof sketch: at the requested weight, the two lookups are definitionally identical.  At every
other weight, the code is absent from the support by
`splitWordDepthTwoCode_mem_support_iff`; `idxOf` therefore returns the support length, where the
zero-padding premise applies. -/
private theorem betaThreeNumeratorFrom_idxOf_splitWordDepthTwoCode_eq_levelThreeWordCountAt
    (betaThree : BetaThreeRows) (row coordinate total : ℕ) (word : SplitWord 2)
    (hzero : ∀ symbol,
      (ternarySupportCodes levelThreeWordLength total).length ≤ symbol →
        betaThreeNumeratorFrom betaThree row coordinate symbol = 0) :
    betaThreeNumeratorFrom betaThree row coordinate
        ((ternarySupportCodes levelThreeWordLength total).idxOf
          (TernarySplitWordEncoding.splitWordDepthTwoCode word)) =
      levelThreeWordCountAt betaThree row coordinate total word := by
  by_cases hweight : splitWordWeight word = total
  · simp [levelThreeWordCountAt, hweight,
      MatrixMultiplication.SimplifiedRecursiveParentTerms.splitWordTwoCode,
      TernarySplitWordEncoding.splitWordDepthTwoCode]
  · have hnotMemLocal :
        TernarySplitWordEncoding.splitWordDepthTwoCode word ∉
          MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
            MatrixMultiplication.BetaFourLocalGeometry.childWordLength total :=
      fun hmem ↦ hweight
        ((TernarySplitWordEncoding.splitWordDepthTwoCode_mem_support_iff word total).mp hmem)
    have hnotMem :
        TernarySplitWordEncoding.splitWordDepthTwoCode word ∉
          ternarySupportCodes levelThreeWordLength total := by
      simpa only [
        MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.childWordLength_eq,
        MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq]
        using hnotMemLocal
    rw [levelThreeWordCountAt, if_neg hweight,
      List.idxOf_eq_length_iff.mpr hnotMem]
    exact hzero _ le_rfl

/-- Gathering one typed valid slot at a canonical depth-three word is exactly the recursive
semantic summand for that slot.

Proof sketch: the typed slot identifies its total-eight left and right child shapes.  The parent
support lookup returns the canonical eight-digit code, whose quotient and remainder are the two
canonical four-digit child codes.  Zero padding then turns the two raw beta-three array lookups
into the guarded left and right semantic counts. -/
private theorem betaFourGatherSlotNumerator_at_depthThreeCode
    (betaThree : BetaThreeRows) (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 3)
    (hweight : splitWordWeight word = (levelFourParentIndex parent sigma).count c)
    (slot : LevelFourValidSlot parent) :
    betaFourGatherSlotNumerator top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val
        ((ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c)).idxOf
            (TernarySplitWordEncoding.splitWordDepthThreeCode word))
        slot.1.val =
      levelFourSlotNumerator top root region parent slot *
        (levelFourLeftChildWordCount betaThree region parent sigma slot c
            (splitWordSuccEquiv 2 word).1 *
         levelFourRightChildWordCount betaThree region parent sigma slot c
            (splitWordSuccEquiv 2 word).2) := by
  let pair := levelFourPairAtSlot parent slot.1 slot.2
  have hpair : pairAt parent.val slot.1.val = pair := by
    simpa [pair] using pairAt_eq_levelFourPairAtSlot parent slot
  have htotals := mem_levelFourPairs_iff.mp
    (levelFourPairAtSlot_geometry parent slot.1 slot.2).1
  have hleftShape : pair.1 ∈ shapes 8 := mem_shapes_iff_total.mpr htotals.1
  have hrightShape : pair.2 ∈ shapes 8 := mem_shapes_iff_total.mpr htotals.2.1
  have hparentTotal :
      shapeCoordinate (parentShapeAt parent.val) (coordinateOfLeg (sigma c)).val =
        (levelFourParentIndex parent sigma).count c := by
    rw [parentShapeAt_eq_positiveLevelFourShape, shapeCoordinate_coordinateOfLeg]
    rfl
  have hleftTotal :
      shapeCoordinate pair.1 (coordinateOfLeg (sigma c)).val =
        (levelFourChildShape parent sigma slot).get c := by
    rw [levelFourChildShape_get]
    simpa [pair] using shapeCoordinate_coordinateOfLeg pair.1 (sigma c)
  have hrightTotal :
      shapeCoordinate pair.2 (coordinateOfLeg (sigma c)).val =
        (RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
          (levelFourChildShape parent sigma slot)).get c := by
    simpa [pair] using levelFourRightChild_evaluatorTotal parent sigma slot c
  have hparentCode :
      ternarySupportCodeAt parentWordLength
          ((levelFourParentIndex parent sigma).count c)
          ((ternarySupportCodes parentWordLength
            ((levelFourParentIndex parent sigma).count c)).idxOf
              (TernarySplitWordEncoding.splitWordDepthThreeCode word)) =
        TernarySplitWordEncoding.splitWordDepthThreeCode word := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentWordLength_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodeAt_eq,
      hweight] using
        (TernarySplitWordEncoding.ternarySupportCodeAt_idxOf
          (splitWordDepthThreeCode_mem_support word))
  have hleftLookup :=
    betaThreeNumeratorFrom_idxOf_splitWordDepthTwoCode_eq_levelThreeWordCountAt
      betaThree
      (shapeEightIndex pair.1 * regionCount + region.val)
      (coordinateOfLeg (sigma c)).val
      (shapeCoordinate pair.1 (coordinateOfLeg (sigma c)).val)
      (splitWordSuccEquiv 2 word).1
      (hpadding pair.1 hleftShape region (coordinateOfLeg (sigma c)))
  have hrightLookup :=
    betaThreeNumeratorFrom_idxOf_splitWordDepthTwoCode_eq_levelThreeWordCountAt
      betaThree
      (shapeEightIndex pair.2 * regionCount + region.val)
      (coordinateOfLeg (sigma c)).val
      (shapeCoordinate pair.2 (coordinateOfLeg (sigma c)).val)
      (splitWordSuccEquiv 2 word).2
      (hpadding pair.2 hrightShape region (coordinateOfLeg (sigma c)))
  have hleftCount :
      betaThreeNumeratorFrom betaThree
          (shapeEightIndex pair.1 * regionCount + region.val)
          (coordinateOfLeg (sigma c)).val
          ((ternarySupportCodes levelThreeWordLength
            (shapeCoordinate pair.1 (coordinateOfLeg (sigma c)).val)).idxOf
              (TernarySplitWordEncoding.splitWordDepthTwoCode
                (splitWordSuccEquiv 2 word).1)) =
        levelFourLeftChildWordCount betaThree region parent sigma slot c
          (splitWordSuccEquiv 2 word).1 := by
    calc
      _ = levelThreeWordCountAt betaThree
          (shapeEightIndex pair.1 * regionCount + region.val)
          (coordinateOfLeg (sigma c)).val
          (shapeCoordinate pair.1 (coordinateOfLeg (sigma c)).val)
          (splitWordSuccEquiv 2 word).1 := hleftLookup
      _ = _ := by
        change
          levelThreeWordCountAt betaThree
              (shapeEightIndex pair.1 * regionCount + region.val)
              (coordinateOfLeg (sigma c)).val
              (shapeCoordinate pair.1 (coordinateOfLeg (sigma c)).val)
              (splitWordSuccEquiv 2 word).1 =
            levelThreeWordCountAt betaThree
              (shapeEightIndex pair.1 * regionCount + region.val)
              (coordinateOfLeg (sigma c)).val
              ((levelFourChildShape parent sigma slot).get c)
              (splitWordSuccEquiv 2 word).1
        rw [← hleftTotal]
  have hrightCount :
      betaThreeNumeratorFrom betaThree
          (shapeEightIndex pair.2 * regionCount + region.val)
          (coordinateOfLeg (sigma c)).val
          ((ternarySupportCodes levelThreeWordLength
            (shapeCoordinate pair.2 (coordinateOfLeg (sigma c)).val)).idxOf
              (TernarySplitWordEncoding.splitWordDepthTwoCode
                (splitWordSuccEquiv 2 word).2)) =
        levelFourRightChildWordCount betaThree region parent sigma slot c
          (splitWordSuccEquiv 2 word).2 := by
    calc
      _ = levelThreeWordCountAt betaThree
          (shapeEightIndex pair.2 * regionCount + region.val)
          (coordinateOfLeg (sigma c)).val
          (shapeCoordinate pair.2 (coordinateOfLeg (sigma c)).val)
          (splitWordSuccEquiv 2 word).2 := hrightLookup
      _ = _ := by
        change
          levelThreeWordCountAt betaThree
              (shapeEightIndex pair.2 * regionCount + region.val)
              (coordinateOfLeg (sigma c)).val
              (shapeCoordinate pair.2 (coordinateOfLeg (sigma c)).val)
              (splitWordSuccEquiv 2 word).2 =
            levelThreeWordCountAt betaThree
              (shapeEightIndex pair.2 * regionCount + region.val)
              ((coordinateOfLeg (sigma c)).val)
              ((RecursiveChildShape.complement
                (levelFourParentIndex_total_twice parent sigma)
                (levelFourChildShape parent sigma slot)).get c)
              (splitWordSuccEquiv 2 word).2
        rw [← hrightTotal]
  have hdiv :
      TernarySplitWordEncoding.splitWordDepthThreeCode word / 3 ^ levelThreeWordLength =
        TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).1 := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.childWordLength_eq]
      using splitWordDepthThreeCode_div word
  have hmod :
      TernarySplitWordEncoding.splitWordDepthThreeCode word % 3 ^ levelThreeWordLength =
        TernarySplitWordEncoding.splitWordDepthTwoCode (splitWordSuccEquiv 2 word).2 := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.childWordLength_eq]
      using splitWordDepthThreeCode_mod word
  unfold betaFourGatherSlotNumerator
  dsimp only
  rw [hpair, hparentTotal, hparentCode,
    hdiv, hmod,
    hleftCount, hrightCount]
  change
    topSplitNumerator top root.val region.val parent.val slot.1.val *
          levelFourLeftChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).1 *
            levelFourRightChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).2 =
      topSplitNumerator top root.val region.val parent.val slot.1.val *
        (levelFourLeftChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).1 *
          levelFourRightChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).2)
  exact Nat.mul_assoc _ _ _

/-- Removing top slots with zero split numerator does not change a numerator-weighted slot sum.

Proof sketch: write the active-slot subtype sum as a sum over the filtered finite set.  Every
discarded valid slot has zero split numerator, so its product contributes zero. -/
private theorem sum_levelFourActiveSlot_numerator_mul
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount)
    (f : LevelFourValidSlot parent → ℕ) :
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1 * f slot.1) =
      ∑ slot : LevelFourValidSlot parent,
        levelFourSlotNumerator top root region parent slot * f slot := by
  calc
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1 * f slot.1) =
        ∑ slot ∈ levelFourActiveSlots top root region parent,
          levelFourSlotNumerator top root region parent slot * f slot :=
      (Finset.sum_subtype (levelFourActiveSlots top root region parent)
        (fun _ ↦ Iff.rfl)
        (fun slot ↦ levelFourSlotNumerator top root region parent slot * f slot)).symm
    _ = ∑ slot : LevelFourValidSlot parent,
        levelFourSlotNumerator top root region parent slot * f slot := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hnot
      have hzero : levelFourSlotNumerator top root region parent slot = 0 := by
        simpa [levelFourActiveSlots] using hnot
      simp [hzero]

/-- The pointwise global gather at a canonical depth-three word is the intrinsic recursive parent
count, provided the word has the requested parent weight.

Proof sketch: convert the proof-free `validSlots` list to the intrinsic valid-slot finite type,
apply the typed one-slot equation term by term, and then remove the zero-numerator slots.  The
remaining active-slot sum is definitionally `levelFourSemanticParentWordCount`. -/
private theorem betaFourParentNumeratorGather_at_depthThreeCode
    (betaThree : BetaThreeRows) (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 3)
    (hweight : splitWordWeight word = (levelFourParentIndex parent sigma).count c) :
    betaFourParentNumeratorGather top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val
        ((ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c)).idxOf
            (TernarySplitWordEncoding.splitWordDepthThreeCode word)) =
      levelFourSemanticParentWordCount top betaThree root region parent sigma c word := by
  have hparentTotal :
      shapeCoordinate (parentShapeAt parent.val) (coordinateOfLeg (sigma c)).val =
        (levelFourParentIndex parent sigma).count c := by
    rw [parentShapeAt_eq_positiveLevelFourShape, shapeCoordinate_coordinateOfLeg]
    rfl
  have hcodeMem :
      TernarySplitWordEncoding.splitWordDepthThreeCode word ∈
        ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c) := by
    simpa only [hweight] using splitWordDepthThreeCode_mem_global_support word
  have hposition :
      (ternarySupportCodes parentWordLength
        ((levelFourParentIndex parent sigma).count c)).idxOf
          (TernarySplitWordEncoding.splitWordDepthThreeCode word) <
        (ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c)).length :=
    List.idxOf_lt_length_of_mem hcodeMem
  unfold betaFourParentNumeratorGather
  rw [if_pos (by simpa only [hparentTotal] using hposition),
    sum_validSlots_eq_sum_validSlot]
  calc
    (∑ slot : LevelFourValidSlot parent,
        betaFourGatherSlotNumerator top betaThree root.val region.val parent.val
          (coordinateOfLeg (sigma c)).val
          ((ternarySupportCodes parentWordLength
            ((levelFourParentIndex parent sigma).count c)).idxOf
              (TernarySplitWordEncoding.splitWordDepthThreeCode word))
          slot.1.val) =
        ∑ slot : LevelFourValidSlot parent,
          levelFourSlotNumerator top root region parent slot *
            (levelFourLeftChildWordCount betaThree region parent sigma slot c
                (splitWordSuccEquiv 2 word).1 *
             levelFourRightChildWordCount betaThree region parent sigma slot c
                (splitWordSuccEquiv 2 word).2) := by
      apply Finset.sum_congr rfl
      intro slot _
      exact betaFourGatherSlotNumerator_at_depthThreeCode
        betaThree hpadding top root region parent sigma c word hweight slot
    _ = ∑ slot : LevelFourActiveSlot top root region parent,
          levelFourSlotNumerator top root region parent slot.1 *
            (levelFourLeftChildWordCount betaThree region parent sigma slot.1 c
                (splitWordSuccEquiv 2 word).1 *
             levelFourRightChildWordCount betaThree region parent sigma slot.1 c
                (splitWordSuccEquiv 2 word).2) :=
      (sum_levelFourActiveSlot_numerator_mul top root region parent
        (fun slot ↦
          levelFourLeftChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).1 *
            levelFourRightChildWordCount betaThree region parent sigma slot c
              (splitWordSuccEquiv 2 word).2)).symm
    _ = levelFourSemanticParentWordCount top betaThree root region parent sigma c word := rfl

/-- A proof-free valid slot can be viewed as the corresponding intrinsic typed slot.

Proof sketch: membership in `validSlots` supplies both the common thirty-slot bound and the
parent-local pair-list bound. -/
private def typedSlotOfMem (parent : Fin positiveLevelFourShapeCount) (slot : ℕ)
    (hslot : slot ∈ validSlots parent.val) : LevelFourValidSlot parent := by
  have hbounds : slot < pairSlotCount ∧
      slot < (levelFourPairsForParent (positiveLevelFourShape parent)).length := by
    simpa [validSlots, parentShapeAt_eq_positiveLevelFourShape] using hslot
  exact ⟨⟨slot, hbounds.1⟩, hbounds.2⟩

/-- Both shapes addressed by a proof-free valid slot are genuine total-eight child shapes. -/
private theorem pairAt_mem_shapes (parent : Fin positiveLevelFourShapeCount) (slot : ℕ)
    (hslot : slot ∈ validSlots parent.val) :
    (pairAt parent.val slot).1 ∈ shapes 8 ∧ (pairAt parent.val slot).2 ∈ shapes 8 := by
  let typedSlot : LevelFourValidSlot parent := typedSlotOfMem parent slot hslot
  have hpair : pairAt parent.val slot =
      levelFourPairAtSlot parent typedSlot.1 typedSlot.2 := by
    change pairAt parent.val typedSlot.1.val =
      levelFourPairAtSlot parent typedSlot.1 typedSlot.2
    exact pairAt_eq_levelFourPairAtSlot parent typedSlot
  have hgeometry := (levelFourPairAtSlot_geometry parent typedSlot.1 typedSlot.2).1
  have htotals := mem_levelFourPairs_iff.mp hgeometry
  simpa only [mem_shapes_iff_total, hpair] using ⟨htotals.1, htotals.2.1⟩

/-- Projecting a zero-padded global cache to one parent-local record preserves zero padding.

Proof sketch: membership in the mapped local slot list identifies a proof-free valid top slot.
Its two child shapes are total-eight shapes, so the global invariant applies to the two projected
coordinate arrays. -/
theorem fromGlobal_isSupportZero (betaThree : BetaThreeRows)
    (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (coordinate : Fin 3) :
    BetaFourLocalData.IsSupportZero
      (BetaFourLocalData.fromGlobal top betaThree root.val region.val parent.val coordinate.val)
      parent.val coordinate.val := by
  intro slotData hslotData
  simp only [BetaFourLocalData.fromGlobal, List.mem_map] at hslotData
  obtain ⟨slot, hslot, rfl⟩ := hslotData
  have hshapes := pairAt_mem_shapes parent slot hslot
  constructor
  · intro symbol hsymbol
    exact hpadding (pairAt parent.val slot).1 hshapes.1 region coordinate symbol hsymbol
  · intro symbol hsymbol
    exact hpadding (pairAt parent.val slot).2 hshapes.2 region coordinate symbol hsymbol

/-- A valid proof-free slot has the advertised coordinatewise parent sum.

Proof sketch: convert the list membership proof to the typed local slot, use the canonical
level-four pair-geometry theorem, and project its shape equality to the requested coordinate. -/
private theorem pairAt_coordinate_add
    (parent : Fin positiveLevelFourShapeCount) (slot : ℕ)
    (hslot : slot ∈ validSlots parent.val) (coordinate : Fin 3) :
    MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slot).1 coordinate.val +
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slot).2 coordinate.val =
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
        (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent.val) coordinate.val := by
  let typedSlot : LevelFourValidSlot parent := typedSlotOfMem parent slot hslot
  have hpair : pairAt parent.val slot =
      levelFourPairAtSlot parent typedSlot.1 typedSlot.2 := by
    change pairAt parent.val typedSlot.1.val =
      levelFourPairAtSlot parent typedSlot.1 typedSlot.2
    exact pairAt_eq_levelFourPairAtSlot parent typedSlot
  have hsum := (levelFourPairAtSlot_geometry parent typedSlot.1 typedSlot.2).2
  have hparent : parentShapeAt parent.val = positiveLevelFourShape parent :=
    parentShapeAt_eq_positiveLevelFourShape parent
  simp only [
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.shapeCoordinate_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.pairAt_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentShapeAt_eq]
  fin_cases coordinate
  · rw [hpair, hparent]
    change
      (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).1.x +
          (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).2.x =
        (positiveLevelFourShape parent).x
    exact congrArg AlgebraicComplexity.LevelFourReconstruction.Shape.x hsum
  · rw [hpair, hparent]
    change
      (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).1.y +
          (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).2.y =
        (positiveLevelFourShape parent).y
    exact congrArg AlgebraicComplexity.LevelFourReconstruction.Shape.y hsum
  · rw [hpair, hparent]
    change
      (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).1.z +
          (levelFourPairAtSlot parent typedSlot.1 typedSlot.2).2.z =
        (positiveLevelFourShape parent).z
    exact congrArg AlgebraicComplexity.LevelFourReconstruction.Shape.z hsum

/-- Either child support of a valid local pair fits the common nineteen-symbol padding.

Proof sketch: both child shapes have total eight.  Each of their three coordinates is therefore
at most eight, and the generic length-four support bound applies. -/
private theorem pairAt_childSupport_length_le
    (parent : Fin positiveLevelFourShapeCount) (slot : ℕ)
    (hslot : slot ∈ validSlots parent.val) (coordinate : Fin 3) (right : Bool) :
    (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength
      (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
        (if right then
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slot).2
        else
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slot).1)
        coordinate.val)).length ≤
      MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth := by
  simp only [
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.childWordLength_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.shapeCoordinate_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.pairAt_eq,
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.childSupportWidth_eq]
  have hshapes := pairAt_mem_shapes parent slot hslot
  have htotal :
      shapeCoordinate
        (if right then
          (pairAt parent.val slot).2
        else
          (pairAt parent.val slot).1)
        coordinate.val ≤ 8 := by
    have hshapeTotal :
        (if right then
          (pairAt parent.val slot).2
        else
          (pairAt parent.val slot).1).total = 8 := by
      cases right
      · simpa using mem_shapes_total hshapes.1
      · simpa using mem_shapes_total hshapes.2
    cases right <;> fin_cases coordinate <;>
      simp [shapeCoordinate,
        AlgebraicComplexity.LevelFourReconstruction.Shape.total] at hshapeTotal ⊢ <;>
      omega
  exact TernarySplitWordEncoding.ternarySupportCodes_depthTwo_length_le _ htotal

/-! ## Whole local rows -/

/-- A fold whose every step adds one value is its initial value plus the sum of all added values.

Proof sketch: induction moves the head addition into the accumulator.  Associativity identifies
the resulting nested additions with the sum of the mapped tail. -/
private theorem foldl_eq_add_sum_of_step {A : Type*} (values : List A)
    (step : ℕ → A → ℕ) (value : A → ℕ)
    (hstep : ∀ accumulator item, item ∈ values →
      step accumulator item = accumulator + value item)
    (initial : ℕ) :
    values.foldl step initial = initial + (values.map value).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons item values ih =>
      rw [List.foldl_cons, hstep initial item (by simp)]
      rw [ih]
      · simp [Nat.add_assoc]
      · intro accumulator other hother
        exact hstep accumulator other (by simp [hother])

namespace BetaFourLocalData

/-- For a genuine global projection, every local slot has the advertised parent sum and both
child support rows fit the common padding.

Proof sketch: membership in the mapped local-data list exposes a valid proof-free top slot.  The
three conclusions are the typed pair-geometry and support-width lemmas proved above. -/
theorem fromGlobal_hasSupportGeometry (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin regionCount) (parent : Fin positiveLevelFourShapeCount)
    (coordinate : Fin 3) :
    ∀ slotData ∈
        (MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.fromGlobal
          top betaThree root.val region.val parent.val coordinate.val).slots,
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
            (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slotData.slot).1
            coordinate.val +
          MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
            (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slotData.slot).2
            coordinate.val =
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent.val) coordinate.val ∧
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slotData.slot).1
          coordinate.val)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth ∧
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent.val slotData.slot).2
          coordinate.val)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth := by
  intro slotData hslotData
  simp only [
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.fromGlobal,
    List.mem_map] at hslotData
  obtain ⟨slot, hslot, rfl⟩ := hslotData
  exact ⟨pairAt_coordinate_add parent slot hslot coordinate,
    pairAt_childSupport_length_le parent slot hslot coordinate false,
    pairAt_childSupport_length_le parent slot hslot coordinate true⟩

/-- On a genuine parent-support position, a zero-padded local scatter numerator equals inverse-code
gathering.

The geometry premise is relation-free: it only says that every local pair adds to the parent and
that both fixed-weight child supports fit the common padding.  Thus the theorem can be reused for
certificate formats other than `fromGlobal`.

Proof sketch: the slot theorem identifies every outer-fold step with addition of that slot's
gathered product.  The generic fold lemma sums those products, which is definitionally the local
gather numerator at an in-support position. -/
theorem numeratorAt_eq_gatherNumerator (data : BetaFourLocalData)
    (parent coordinate position : ℕ)
    (hpadding : data.IsSupportZero parent coordinate)
    (hgeometry : ∀ slotData ∈ data.slots,
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
            (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slotData.slot).1 coordinate +
          MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
            (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slotData.slot).2 coordinate =
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate ∧
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slotData.slot).1
          coordinate)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth ∧
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slotData.slot).2
          coordinate)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth)
    (hposition : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)).length) :
    data.numeratorAt parent coordinate position =
      data.gatherNumerator parent coordinate position := by
  unfold MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.numeratorAt
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.addToNumeratorAt
  rw [foldl_eq_add_sum_of_step data.slots
    (fun accumulator slotData ↦
      slotData.addToNumeratorAt parent coordinate position accumulator)
    (fun slotData ↦ slotData.gatherNumerator parent coordinate position)]
  · simp [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.gatherNumerator,
      hposition]
  · intro accumulator slotData hslotData
    have hslotPadding := hpadding slotData hslotData
    have hslotGeometry := hgeometry slotData hslotData
    exact
      MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalSlotData.addToNumeratorAt_eq_add_gatherNumerator
        slotData
          parent coordinate position accumulator hslotPadding hslotGeometry.1
          hslotGeometry.2.1 hslotGeometry.2.2 hposition

/-- The global cache projection has pointwise scatter/gather agreement on every genuine parent
support symbol. -/
theorem fromGlobal_numeratorAt_eq_gatherNumerator
    (betaThree : BetaThreeRows) (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (coordinate : Fin 3) (position : ℕ)
    (hposition : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent.val)
          coordinate.val)).length) :
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.numeratorAt
        (MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.fromGlobal
          top betaThree root.val region.val parent.val coordinate.val)
        parent.val coordinate.val position =
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.gatherNumerator
        (MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.fromGlobal
          top betaThree root.val region.val parent.val coordinate.val)
        parent.val coordinate.val position := by
  apply BetaFourLocalData.numeratorAt_eq_gatherNumerator
  · exact fromGlobal_isSupportZero betaThree hpadding top root region parent coordinate
  · exact fromGlobal_hasSupportGeometry top betaThree root region parent coordinate
  · exact hposition

end BetaFourLocalData

/-- Reading the dense evaluator row at a canonical depth-three word gives the intrinsic recursive
parent count.

Proof sketch: the structural support bound places the canonical position inside the common
1,107-cell padding.  Pointwise local scattering at that position agrees first with the dense
global row, then with inverse-code gathering, and finally with the typed whole-parent gather
proved above. -/
private theorem betaFourParentRow_at_depthThreeCode_eq_semantic
    (betaThree : BetaThreeRows) (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 3)
    (hweight : splitWordWeight word = (levelFourParentIndex parent sigma).count c) :
    (betaFourParentRow top betaThree root.val region.val parent.val
      (coordinateOfLeg (sigma c)).val)[
        (ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c)).idxOf
            (TernarySplitWordEncoding.splitWordDepthThreeCode word)]?.getD 0 =
      levelFourSemanticParentWordCount top betaThree root region parent sigma c word := by
  let position :=
    (ternarySupportCodes parentWordLength
      ((levelFourParentIndex parent sigma).count c)).idxOf
        (TernarySplitWordEncoding.splitWordDepthThreeCode word)
  change
    (betaFourParentRow top betaThree root.val region.val parent.val
      (coordinateOfLeg (sigma c)).val)[position]?.getD 0 = _
  have hparentTotal :
      shapeCoordinate (parentShapeAt parent.val) (coordinateOfLeg (sigma c)).val =
        (levelFourParentIndex parent sigma).count c := by
    rw [parentShapeAt_eq_positiveLevelFourShape, shapeCoordinate_coordinateOfLeg]
    rfl
  have hmem :
      TernarySplitWordEncoding.splitWordDepthThreeCode word ∈
        ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c) := by
    simpa only [hweight] using splitWordDepthThreeCode_mem_global_support word
  have hposition :
      position <
        (ternarySupportCodes parentWordLength
          ((levelFourParentIndex parent sigma).count c)).length := by
    simpa only [position] using List.idxOf_lt_length_of_mem hmem
  have hwordLe : splitWordWeight word ≤ 16 := by
    rw [splitWordWeight_succ]
    exact Nat.add_le_add
      (TernarySplitWordEncoding.splitWordWeight_depthTwo_le _)
      (TernarySplitWordEncoding.splitWordWeight_depthTwo_le _)
  have hsupportWidth :
      (ternarySupportCodes parentWordLength
        ((levelFourParentIndex parent sigma).count c)).length ≤ parentSupportWidth := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentWordLength_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentSupportWidth_eq,
      hweight] using
        TernarySplitWordEncoding.ternarySupportCodes_depthThree_length_le
          (splitWordWeight word) hwordLe
  have hpositionWidth : position < parentSupportWidth :=
    lt_of_lt_of_le hposition hsupportWidth
  have hpositionWidthLocal :
      position < MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentSupportWidth_eq]
      using hpositionWidth
  let data :=
    MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.fromGlobal
      top betaThree root.val region.val parent.val (coordinateOfLeg (sigma c)).val
  have hrows :
      data.scatter parent.val (coordinateOfLeg (sigma c)).val =
        betaFourParentRow top betaThree root.val region.val parent.val
          (coordinateOfLeg (sigma c)).val :=
    data.scatter_eq_global top betaThree root.val region.val parent.val
      (coordinateOfLeg (sigma c)).val rfl
  have hrange := data.scatterOn_range_eq_scatter parent.val
    (coordinateOfLeg (sigma c)).val
  have hread :
      data.numeratorAt parent.val (coordinateOfLeg (sigma c)).val position =
        (betaFourParentRow top betaThree root.val region.val parent.val
          (coordinateOfLeg (sigma c)).val)[position]?.getD 0 := by
    have h := congrArg (fun row : List ℕ ↦ row[position]?.getD 0) (hrange.trans hrows)
    simp only [BetaFourLocalData.scatterOn] at h
    rw [List.getElem?_map, List.getElem?_range hpositionWidthLocal] at h
    simpa only [Option.map_some, Option.getD_some] using h
  have hpositionLocal : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent.val)
          (coordinateOfLeg (sigma c)).val)).length := by
    simpa only [
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentWordLength_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.ternarySupportCodes_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.shapeCoordinate_eq,
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.LocalGeometry.parentShapeAt_eq,
      hparentTotal] using hposition
  calc
    (betaFourParentRow top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val)[position]?.getD 0 =
        data.numeratorAt parent.val (coordinateOfLeg (sigma c)).val position := hread.symm
    _ = data.gatherNumerator parent.val (coordinateOfLeg (sigma c)).val position := by
      simpa only [data] using
        MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalData.fromGlobal_numeratorAt_eq_gatherNumerator
          betaThree hpadding top root region parent (coordinateOfLeg (sigma c))
          position hpositionLocal
    _ = betaFourParentNumeratorGather top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val position := by
      exact data.gatherNumerator_eq_global top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val position rfl
    _ = levelFourSemanticParentWordCount top betaThree root region parent sigma c word := by
      simpa only [position] using
        betaFourParentNumeratorGather_at_depthThreeCode
          betaThree hpadding top root region parent sigma c word hweight

/-- An intrinsic recursive parent count vanishes when the word has the wrong parent weight.

Proof sketch: if one child count is zero, every corresponding active-slot summand is zero.  If
both child counts were nonzero, their guarded-support theorems would identify the two half-word
weights with complementary child coordinates.  Those coordinates add to the parent coordinate,
contradicting the assumed parent-weight mismatch. -/
private theorem levelFourSemanticParentWordCount_eq_zero_of_weight_ne
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin regionCount) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) (c : Leg) (word : SplitWord 3)
    (hweight : splitWordWeight word ≠ (levelFourParentIndex parent sigma).count c) :
    levelFourSemanticParentWordCount top betaThree root region parent sigma c word = 0 := by
  unfold levelFourSemanticParentWordCount
  apply Finset.sum_eq_zero
  intro slot _hslot
  by_cases hleft :
      levelFourLeftChildWordCount betaThree region parent sigma slot.1 c
        (splitWordSuccEquiv 2 word).1 = 0
  · simp [hleft]
  by_cases hright :
      levelFourRightChildWordCount betaThree region parent sigma slot.1 c
        (splitWordSuccEquiv 2 word).2 = 0
  · simp [hright]
  have hleftWeight :
      splitWordWeight (splitWordSuccEquiv 2 word).1 =
        (levelFourChildShape parent sigma slot.1).get c := by
    apply levelThreeWordCountAt_supported betaThree
      (shapeEightIndex
          (levelFourPairAtSlot parent slot.1.1 slot.1.2).1 * regionCount + region.val)
      (coordinateOfLeg (sigma c)).val
      ((levelFourChildShape parent sigma slot.1).get c)
      (splitWordSuccEquiv 2 word).1
    exact hleft
  have hrightWeight :
      splitWordWeight (splitWordSuccEquiv 2 word).2 =
        (RecursiveChildShape.complement
          (levelFourParentIndex_total_twice parent sigma)
          (levelFourChildShape parent sigma slot.1)).get c := by
    apply levelThreeWordCountAt_supported betaThree
      (shapeEightIndex
          (levelFourPairAtSlot parent slot.1.1 slot.1.2).2 * regionCount + region.val)
      (coordinateOfLeg (sigma c)).val
      ((RecursiveChildShape.complement
        (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot.1)).get c)
      (splitWordSuccEquiv 2 word).2
    exact hright
  have hsum :
      (levelFourChildShape parent sigma slot.1).get c +
          (RecursiveChildShape.complement
            (levelFourParentIndex_total_twice parent sigma)
            (levelFourChildShape parent sigma slot.1)).get c =
        (levelFourParentIndex parent sigma).count c := by
    have hsumPerm := RecursiveChildShape.get_add_complement_get
      (levelFourParentIndex_total_twice parent sigma)
      (levelFourChildShape parent sigma slot.1) c
    change
      (levelFourChildShape parent sigma slot.1).get c +
          (RecursiveChildShape.complement
            (levelFourParentIndex_total_twice parent sigma)
            (levelFourChildShape parent sigma slot.1)).get c =
        (levelFourParentIndex parent sigma).count c at hsumPerm
    exact hsumPerm
  exact (hweight (by
    rw [splitWordWeight_succ, hleftWeight, hrightWeight]
    exact hsum)).elim

/-- Zero-padded beta-three cache rows make every dense beta-four evaluator row agree word for word
with the intrinsic recursive complete-split semantics.

Proof sketch: at the correct parent weight, rewrite the evaluator's inline ternary polynomial as
the canonical depth-three code and apply the dense-row bridge.  At every other weight, the guarded
evaluator is zero by definition and the recursive semantic count vanishes by the preceding
complement argument. -/
theorem levelFourEvaluatorRowsAgree_of_zeroPadding
    (betaThree : BetaThreeRows) (hpadding : BetaThreeRowsHaveZeroPadding betaThree)
    (top : TopBranchRows) (root region : Fin regionCount)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    LevelFourEvaluatorRowsAgree top betaThree root region parent sigma := by
  intro c word
  unfold levelFourEvaluatorParentWordCount
  by_cases hweight :
      splitWordWeight word = (levelFourParentIndex parent sigma).count c
  · rw [if_pos hweight]
    change
      (betaFourParentRow top betaThree root.val region.val parent.val
        (coordinateOfLeg (sigma c)).val)[
          (ternarySupportCodes parentWordLength
            ((levelFourParentIndex parent sigma).count c)).idxOf
              (TernarySplitWordEncoding.splitWordDepthThreeCode word)]?.getD 0 = _
    exact betaFourParentRow_at_depthThreeCode_eq_semantic
      betaThree hpadding top root region parent sigma c word hweight
  · rw [if_neg hweight]
    exact (levelFourSemanticParentWordCount_eq_zero_of_weight_ne
      top betaThree root region parent sigma c word hweight).symm


end MatrixMultiplication.BetaFourSemanticAgreement
