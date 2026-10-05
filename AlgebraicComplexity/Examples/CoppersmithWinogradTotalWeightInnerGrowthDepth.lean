/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerPrimeHashingDepth

set_option autoImplicit false

/-!
# Depth-generic exponential growth of the total-weight inner hashing field

The depth-generic counterpart of the growth half of
`Examples/CoppersmithWinogradTotalWeightInnerGrowth.lean`: the two exponential bounds on the
localized competitor requirement and the hash modulus, the sequence-ready record
`CWTotalWeightInnerGrowthDataAtDepth`, and the canonical Behrend bucket/seed/copy family with its
three asymptotic theorems.

Split out of `Examples/CoppersmithWinogradTotalWeightInnerSequenceDepth.lean` under the
repository's 900-line module rule; no name, statement or import path changed.  The depth-generic
constructor that consumes this file is still `…InnerSequenceDepth`.
-/

namespace AlgebraicComplexity.Examples

open scoped BigOperators
open AlgebraicComplexity Tensor

universe u v w x

/-! ## Depth-generic exponential growth of the inner hashing field -/

/-- Exact exponential upper bound for the maximum localized competitor requirement. -/
theorem cwTotalWeightInnerCompetitorRequirement_cast_le_atDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q depth profile) k)
    (ambientBase : ℝ) (hambientBase : 0 ≤ ambientBase)
    (ambientLoss : ℕ → ℝ)
    (hambientLoss : 0 < ambientLoss k)
    (hambient :
      ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts profile k) coarseWord).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k) :
    (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      cwTotalWeightInnerCompetitorInputLoss K q depth profile ambientLoss k *
        cwTotalWeightInnerCompetitorBase K q depth profile ambientBase ^ k := by
  let base := cwTotalWeightInnerCompetitorBase K q depth profile ambientBase
  let sumLoss := ∑ c : Leg, WordType.structuralZeroMultinomialLoss
    (cwTotalWeightConditionalLegType K q depth profile c) k
  have hbase : 0 ≤ base :=
    (one_le_cwTotalWeightInnerCompetitorBase K q depth profile ambientBase).trans'
      (by norm_num)
  have hsumNonneg : 0 ≤ sumLoss := by
    exact Finset.sum_nonneg fun c _ ↦
      (WordType.structuralZeroMultinomialLoss_pos
        (cwTotalWeightConditionalLegType K q depth profile c) k).le
  have hcommon : ∀ c : Leg,
      WordType.structuralZeroMultinomialLoss
          (cwTotalWeightConditionalLegType K q depth profile c) k * ambientLoss k *
        (ambientBase /
          cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k ≤
      ambientLoss k * sumLoss * base ^ k := by
    intro c
    have hloss : WordType.structuralZeroMultinomialLoss
        (cwTotalWeightConditionalLegType K q depth profile c) k ≤ sumLoss := by
      exact Finset.single_le_sum
        (fun d _ ↦ (WordType.structuralZeroMultinomialLoss_pos
          (cwTotalWeightConditionalLegType K q depth profile d) k).le)
        (Finset.mem_univ c)
    have hratioNonneg : 0 ≤ ambientBase /
        cwTotalWeightConditionalLegEntropyBase K q depth profile c :=
      div_nonneg hambientBase
        (cwTotalWeightConditionalLegEntropyBase_pos K q depth profile c).le
    have hpow : (ambientBase /
        cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k ≤ base ^ k :=
      pow_le_pow_left₀ hratioNonneg
        (div_conditionalLegEntropyBase_le_innerCompetitorBase
          K q depth profile ambientBase c) k
    calc
      WordType.structuralZeroMultinomialLoss
            (cwTotalWeightConditionalLegType K q depth profile c) k * ambientLoss k *
          (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k =
        WordType.structuralZeroMultinomialLoss
            (cwTotalWeightConditionalLegType K q depth profile c) k *
          (ambientLoss k * (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k) := by ring
      _ ≤ sumLoss * (ambientLoss k * (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k) :=
        mul_le_mul_of_nonneg_right hloss
          (mul_nonneg hambientLoss.le (pow_nonneg hratioNonneg k))
      _ ≤ sumLoss * (ambientLoss k * base ^ k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hambientLoss.le) hsumNonneg
      _ = ambientLoss k * sumLoss * base ^ k := by ring
  have hmaximum :
      (cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      ambientLoss k * sumLoss * base ^ k := by
    unfold cwTotalWeightInnerLegFiberMaximumAtDepth
    apply natCast_finsetSup_le
    · exact mul_nonneg (mul_nonneg hambientLoss.le hsumNonneg) (pow_nonneg hbase k)
    intro c hc
    apply natCast_finsetSup_le
    · exact mul_nonneg (mul_nonneg hambientLoss.le hsumNonneg) (pow_nonneg hbase k)
    intro markedWord hmarkedWord
    exact (cwTotalWeight_sourceWordLegFiber_card_le_entropyQuotient
      K q depth n profile hprofileMass k hk hlen coarseWord hcoarseWord
      ambientBase (ambientLoss k) hambient
      markedWord hmarkedWord c).trans (hcommon c)
  unfold cwTotalWeightInnerCompetitorRequirementAtDepth
    cwTotalWeightInnerCompetitorInputLoss
  push_cast
  change 12 *
      (cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
    12 * ambientLoss k * sumLoss * base ^ k
  calc
    12 * (cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      12 * (ambientLoss k * sumLoss * base ^ k) :=
        mul_le_mul_of_nonneg_left hmaximum (show (0 : ℝ) ≤ 12 by norm_num)
    _ = 12 * ambientLoss k * sumLoss * base ^ k := by ring

/-- The canonical next-prime hashing field has exactly the same conditional competitor base. -/
theorem cwTotalWeightInnerHashModulus_cast_le_atDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q depth profile) k)
    (ambientBase : ℝ) (hambientBase : 0 ≤ ambientBase)
    (ambientLoss : ℕ → ℝ)
    (hambientLoss : 0 < ambientLoss k)
    (hambient :
      ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts profile k) coarseWord).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k) :
    (cwTotalWeightInnerHashModulusAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      PrimeFieldSizing.loss (cwChunkAlphabetSize depth)
          (cwTotalWeightInnerCompetitorInputLoss K q depth profile ambientLoss) k *
        cwTotalWeightInnerCompetitorBase K q depth profile ambientBase ^ k := by
  simpa only [cwTotalWeightInnerHashModulusAtDepth, PrimeFieldSizing.loss, add_assoc] using
    (PrimeFieldSizing.modulus_cast_le_loss_mul_pow
      (cwChunkAlphabetSize depth)
      (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord)
      k
      (cwTotalWeightInnerCompetitorInputLoss K q depth profile ambientLoss k)
      (cwTotalWeightInnerCompetitorBase K q depth profile ambientBase)
      (one_le_cwTotalWeightInnerCompetitorBase K q depth profile ambientBase)
      (cwTotalWeightInnerCompetitorRequirement_cast_le_atDepth
        K q depth n profile hprofileMass k hk hlen coarseWord hcoarseWord
        ambientBase hambientBase ambientLoss hambientLoss hambient))

/-! ### Depth-generic sequence-ready packaging -/

/-- Depth-generic restatement of `CWTotalWeightInnerGrowthData`: exact proportional coarse-word
sequence together with a sharp localized-ambient cardinality upper bound. -/
structure CWTotalWeightInnerGrowthDataAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) (ambientLoss : ℕ → ℝ) where
  exponent : ℕ → ℕ
  coarseWord : ∀ k,
    PositiveWord (CWTotalWeightCoarseSupport K q depth) (exponent k)
  length_eq : ∀ k, 0 < k →
    WordType.profileMass profile * k = exponent k + 1
  coarse_type : ∀ k, 0 < k →
    WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (exponent k)
          (coarseWord k)) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q depth profile) k
  ambientBase_nonneg : 0 ≤ ambientBase
  ambientLoss_pos : ∀ k, 0 < ambientLoss k
  ambientLoss_subexponential : Growth.Subexponential ambientLoss
  ambient_upper : ∀ k, 0 < k →
    ((cwTotalWeightLocalizedAmbientWords K q depth (exponent k)
      (WordType.proportionalCounts profile k) (coarseWord k)).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k

namespace CWTotalWeightInnerGrowthDataAtDepth

variable {K : Type u} [CommRing K] {q depth : ℕ}
variable {profile : (cwChunkPartitionedTensor K q depth).support → ℕ}
variable {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}

/-- Exact competitor requirement sequence attached to the chosen coarse representatives. -/
noncomputable def requirement
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (k : ℕ) : ℕ :=
  cwTotalWeightInnerCompetitorRequirementAtDepth K q depth (data.exponent k)
    (WordType.proportionalCounts profile k) (data.coarseWord k)

/-- Canonical next-prime modulus sequence. -/
noncomputable def modulus
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (k : ℕ) : ℕ :=
  PrimeFieldSizing.modulus (cwChunkAlphabetSize depth) (data.requirement k)

/-- Complete prime-field loss: exact conditional counting followed by Bertrand. -/
noncomputable def fieldLoss
    (_data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (k : ℕ) : ℝ :=
  PrimeFieldSizing.loss (cwChunkAlphabetSize depth)
    (cwTotalWeightInnerCompetitorInputLoss K q depth profile ambientLoss) k

theorem fieldLoss_pos
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (k : ℕ) : 0 < data.fieldLoss k := by
  unfold fieldLoss PrimeFieldSizing.loss
  have hinput := cwTotalWeightInnerCompetitorInputLoss_pos
    K q depth profile ambientLoss data.ambientLoss_pos k
  positivity

theorem fieldLoss_subexponential
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss) :
    Growth.Subexponential data.fieldLoss := by
  exact PrimeFieldSizing.loss_subexponential (cwChunkAlphabetSize depth)
    (cwTotalWeightInnerCompetitorInputLoss_subexponential
      K q depth profile ambientLoss data.ambientLoss_subexponential)

/-- The canonical prime fields grow at the exact conditional competitor base. -/
theorem modulus_cast_le_fieldLoss_mul_pow
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    (data.modulus k : ℝ) ≤ data.fieldLoss k *
      cwTotalWeightInnerCompetitorBase K q depth profile ambientBase ^ k := by
  exact cwTotalWeightInnerHashModulus_cast_le_atDepth
    K q depth (data.exponent k) profile hprofileMass k hk
    (data.length_eq k hk) (data.coarseWord k) (data.coarse_type k hk)
    ambientBase data.ambientBase_nonneg ambientLoss (data.ambientLoss_pos k)
    (data.ambient_upper k hk)

/-- The exact marked target family has the pushed-profile target base uniformly over the coarse
representative sequence. -/
theorem targetBase_pow_le_markedFiber
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth profile ambientBase ambientLoss)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    cwTotalWeightInnerTargetBase K q depth profile ^ k ≤
      WordType.pushedTypeFiberLoss profile k *
        ((cwTotalWeightMarkedFiberWords K q depth (data.exponent k)
          (WordType.proportionalCounts profile k) (data.coarseWord k)).card : ℝ) := by
  exact cwTotalWeightInnerTargetBase_pow_le_markedFiber
    K q depth (data.exponent k) profile hprofileMass k hk
      (data.length_eq k hk) (data.coarseWord k) (data.coarse_type k hk)

end CWTotalWeightInnerGrowthDataAtDepth

/-! ### Depth-generic canonical chosen finite sequence -/

/-- Canonical half-interval Behrend bucket set in the safe inner prime field. -/
noncomputable def cwTotalWeightInnerBehrendBucketsAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    Finset (CWTotalWeightInnerHashFieldAtDepth K q depth n profile coarseWord) :=
  Classical.choose (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulusAtDepth K q depth n profile coarseWord))

theorem cwTotalWeightInnerBehrendBucketsAtDepth_card
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n profile coarseWord).card =
      rothNumberNat
        (cwTotalWeightInnerHashModulusAtDepth K q depth n profile coarseWord / 2) :=
  (Classical.choose_spec (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulusAtDepth K q depth n profile coarseWord))).1

theorem cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ThreeAPFree
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n profile coarseWord :
        Set (CWTotalWeightInnerHashFieldAtDepth K q depth n profile coarseWord)) :=
  (Classical.choose_spec (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulusAtDepth K q depth n profile coarseWord))).2

/-- Canonical good affine seed for the standard bucket choice. -/
noncomputable def cwTotalWeightInnerBehrendSeedAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ProgressionHash.Seed
      (CWTotalWeightInnerHashFieldAtDepth K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (Fin (n + 1)) :=
  Classical.choose
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSumAtDepth
      K q depth leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))

/-- Canonical inner copy count after localized marked hashing. -/
noncomputable def cwTotalWeightInnerBehrendCopiesAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) : ℕ :=
  ((cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendSeedAtDepth K q depth leaf hdimension n k coarseWord)).card

/-- The naturally indexed selected-address type whose cardinality is the canonical inner copy
count. -/
noncomputable abbrev CWTotalWeightInnerBehrendIndexAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendSeedAtDepth K q depth leaf hdimension n k coarseWord)

@[simp] theorem card_cwTotalWeightInnerBehrendIndexAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
      Fintype.card (CWTotalWeightInnerBehrendIndexAtDepth
      K q depth leaf hdimension n k coarseWord) =
      cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension n k coarseWord := by
  exact Fintype.card_coe _

/-- Exact hashing count for the canonical choices. -/
theorem cwTotalWeightInnerBehrend_hashCountAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    3 * (cwTotalWeightMarkedFiberWords K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord / 2) ≤
      4 * (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord *
        cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
        cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension n k coarseWord := by
  have hspec := (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSumAtDepth
      K q depth leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))).1
  calc
    3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord / 2) =
      3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card := by
      rw [cwTotalWeightInnerBehrendBucketsAtDepth_card]
    _ ≤ 4 * (Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
          Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)) *
        cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension n k coarseWord := by
      simpa only [cwTotalWeightInnerBehrendSeedAtDepth,
        cwTotalWeightInnerBehrendCopiesAtDepth] using hspec
    _ = 4 * (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord *
        cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
        cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension n k coarseWord := by
      simp only [CWTotalWeightInnerHashFieldAtDepth, ZMod.card,
        cwTotalWeightInnerHashModulusAtDepth]

/-- Exact tensor degeneration for the canonical inner-copy sequence. -/
theorem cwTotalWeightInnerBehrend_degeneratesAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightFineMarginalType K q depth
          (WordType.proportionalCounts leaf.profile.count k))).realize
      (Tensor.indexedDirectSum
        (fun _selected : (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord
            ).markedLegwiseIsolatedPowerAddresses n
              (cwTotalWeightLocalizedAmbientWords K q depth n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightMarkedFiberWords K q depth n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightInnerBehrendSeedAtDepth K q depth leaf hdimension n k
                coarseWord) ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  exact (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSumAtDepth
      K q depth leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))).2

namespace CWTotalWeightInnerGrowthDataAtDepth

/-- Every base strictly below the exact target/field quotient is eventually attained by the
canonical Behrend copy sequence. -/
theorem exists_eventually_pow_le_behrendCopies
    {K : Type u} [CommRing K] {q depth : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth leaf.profile.count
      ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q depth leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q depth leaf.profile.count ambientBase)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 0 < k →
      W ^ k ≤
        (cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
          (data.exponent k) k (data.coarseWord k) : ℝ) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  let targetBase := cwTotalWeightInnerTargetBase K q depth leaf.profile.count
  let fieldBase := cwTotalWeightInnerCompetitorBase K q depth leaf.profile.count ambientBase
  let enlargedFieldBase := δ * fieldBase
  let targetLoss := WordType.pushedTypeFiberLoss leaf.profile.count
  let poly : ℕ → ℝ := fun k ↦ 4 * targetLoss k
  have hfieldBase : 0 < fieldBase := by
    exact zero_lt_one.trans_le
      (one_le_cwTotalWeightInnerCompetitorBase K q depth leaf.profile.count ambientBase)
  have henlargedFieldBase : 0 < enlargedFieldBase := by
    exact mul_pos (zero_lt_one.trans hδ) hfieldBase
  have hpoly : Growth.Subexponential poly := by
    exact (WordType.pushedTypeFiberLoss_subexponential leaf.profile.count).const_mul
      (by norm_num : (0 : ℝ) ≤ 4)
  obtain ⟨Nfield, hNfield⟩ := data.fieldLoss_subexponential.eventually_le_pow hδ
  obtain ⟨Nrate, hNrate⟩ := Growth.exists_forall_pow_le_copies
    henlargedFieldBase (by norm_num : (0 : ℝ) < 1) hpoly hW
    (by simpa only [targetBase, enlargedFieldBase] using hWrate)
  refine ⟨max Nfield Nrate, fun k hk hkpos ↦ ?_⟩
  have hkField : Nfield ≤ k := (Nat.le_max_left _ _).trans hk
  have hkRate : Nrate ≤ k := (Nat.le_max_right _ _).trans hk
  let M := data.modulus k
  let copies := cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
    (data.exponent k) k (data.coarseWord k)
  have hMtwo : 2 ≤ M := by
    have hchar := PrimeFieldSizing.characteristicFloor_lt_modulus
      (cwChunkAlphabetSize depth) (data.requirement k)
    have hfloor := two_le_cwChunkAlphabetSize depth
    dsimp [M, CWTotalWeightInnerGrowthDataAtDepth.modulus]
    omega
  have hMsharp : (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := by
    simpa only [M, fieldBase] using
      data.modulus_cast_le_fieldLoss_mul_pow leaf.profile.mass_pos k hkpos
  have hMupper : (M : ℝ) ≤ 1 * enlargedFieldBase ^ k := by
    calc
      (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := hMsharp
      _ ≤ δ ^ k * fieldBase ^ k :=
        mul_le_mul_of_nonneg_right (hNfield k hkField)
          (pow_nonneg hfieldBase.le k)
      _ = 1 * enlargedFieldBase ^ k := by
        rw [one_mul, mul_pow]
  have htarget := data.targetBase_pow_le_markedFiber
    leaf.profile.mass_pos k hkpos
  let marked := (cwTotalWeightMarkedFiberWords K q depth (data.exponent k)
    (WordType.proportionalCounts leaf.profile.count k) (data.coarseWord k)).card
  have htarget' : targetBase ^ k ≤ targetLoss k * (marked : ℝ) := by
    simpa only [targetBase, targetLoss, marked] using htarget
  have hhashNat := cwTotalWeightInnerBehrend_hashCountAtDepth
    K q depth leaf hdimension (data.exponent k) k (data.coarseWord k)
  have hhash : 3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    exact_mod_cast hhashNat
  have hcount : targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
      poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    calc
      targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
          (targetLoss k * (marked : ℝ)) *
            (rothNumberNat (M / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right htarget' (by positivity)
      _ ≤ targetLoss k *
          (3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ)) := by
        have htargetLoss : 0 ≤ targetLoss k :=
          (WordType.pushedTypeFiberLoss_pos leaf.profile.count k).le
        have hmarkedRoth : 0 ≤ (marked : ℝ) *
            (rothNumberNat (M / 2) : ℝ) := by positivity
        nlinarith
      _ ≤ targetLoss k *
          (4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ)) :=
        mul_le_mul_of_nonneg_left hhash
          (WordType.pushedTypeFiberLoss_pos leaf.profile.count k).le
      _ = poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
        unfold poly
        ring
  exact hNrate k M copies hkRate hMtwo hMupper hcount

/-- The canonical selected-address family is nonempty at every positive proportional
repetition. -/
theorem behrendCopies_pos
    {K : Type u} [CommRing K] {q depth : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth leaf.profile.count
      ambientBase ambientLoss)
    (k : ℕ) (hk : 0 < k) :
    0 < cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
      (data.exponent k) k (data.coarseWord k) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  let M := data.modulus k
  let marked := (cwTotalWeightMarkedFiberWords K q depth (data.exponent k)
    (WordType.proportionalCounts leaf.profile.count k) (data.coarseWord k)).card
  let copies := cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
    (data.exponent k) k (data.coarseWord k)
  have hM : cwChunkAlphabetSize depth < M := by
    simpa only [M, CWTotalWeightInnerGrowthDataAtDepth.modulus] using
      PrimeFieldSizing.characteristicFloor_lt_modulus
        (cwChunkAlphabetSize depth) (data.requirement k)
  have hfloor := two_le_cwChunkAlphabetSize depth
  have hhalf : 0 < M / 2 := by omega
  have htarget := data.targetBase_pow_le_markedFiber
    leaf.profile.mass_pos k hk
  have htarget' :
      cwTotalWeightInnerTargetBase K q depth leaf.profile.count ^ k ≤
        WordType.pushedTypeFiberLoss leaf.profile.count k * (marked : ℝ) := by
    simpa only [marked] using htarget
  have htargetPos :
      0 < cwTotalWeightInnerTargetBase K q depth leaf.profile.count ^ k :=
    pow_pos (cwTotalWeightInnerTargetBase_pos K q depth leaf.profile.count) k
  have hmarked : 0 < marked := by
    by_contra hnot
    have hzero : marked = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.cast_zero, mul_zero] at htarget'
    exact (not_lt_of_ge htarget') htargetPos
  have hroth : 0 < rothNumberNat (M / 2) := rothNumberNat_pos hhalf
  have hhash : 3 * marked * rothNumberNat (M / 2) ≤ 4 * (M * M) * copies := by
    simpa only [M, marked, copies, CWTotalWeightInnerGrowthDataAtDepth.modulus,
      CWTotalWeightInnerGrowthDataAtDepth.requirement,
      cwTotalWeightInnerHashModulusAtDepth] using
      cwTotalWeightInnerBehrend_hashCountAtDepth
        K q depth leaf hdimension (data.exponent k) k (data.coarseWord k)
  have hcopies : 0 < copies := by
    by_contra hnot
    have hzero : copies = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hhash
    have hleft : 0 < 3 * marked * rothNumberNat (M / 2) := by positivity
    omega
  exact hcopies

/-- Sequence-ready count growth for the canonical inner extraction at arbitrary depth. -/
theorem exists_subexponentialLoss_pow_le_behrendCopies
    {K : Type u} [CommRing K] {q depth : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth leaf.profile.count
      ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q depth leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q depth leaf.profile.count ambientBase)) :
    ∃ loss : ℕ → ℝ,
      Growth.Subexponential loss ∧
      (∀ k, 0 < loss k) ∧
      ∀ k, 0 < k →
        W ^ k ≤ loss k *
          (cwTotalWeightInnerBehrendCopiesAtDepth K q depth leaf hdimension
            (data.exponent k) k (data.coarseWord k) : ℝ) := by
  obtain ⟨N, hN⟩ := data.exists_eventually_pow_le_behrendCopies
    leaf hdimension hδ hW hWrate
  refine ⟨Growth.finitePrefixPowerLoss W N,
    Growth.finitePrefixPowerLoss_subexponential hW.le N,
    fun k ↦ Growth.finitePrefixPowerLoss_pos hW N k, ?_⟩
  exact Growth.pow_le_finitePrefixPowerLoss_mul_count hW
    (fun k hk ↦ data.behrendCopies_pos leaf hdimension k hk) hN

end CWTotalWeightInnerGrowthDataAtDepth
end AlgebraicComplexity.Examples
