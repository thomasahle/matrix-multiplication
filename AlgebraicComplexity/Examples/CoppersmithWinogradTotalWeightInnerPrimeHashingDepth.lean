/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerSequence

set_option autoImplicit false

/-!
# Depth-generic canonical prime field for total-weight inner hashing

The depth-generic counterpart of `Examples/CoppersmithWinogradTotalWeightInnerPrimeHashing.lean`,
whose declarations pin the recursion depth to `1`.  Everything here is the depth-one argument
verbatim, with `9` replaced by the constant `cwChunkAlphabetSize depth = 3 ^ 2 ^ depth` and the
level-two encoding replaced by the depth-generic `cwChunkPartitionHashEncoding`
(`Examples/CoppersmithWinogradChunkHashEncoding.lean`).  Since the floor is a constant in `depth`,
`PrimeFieldSizing.loss` absorbs it and no exponential rate changes.

Split out of `Examples/CoppersmithWinogradTotalWeightInnerSequenceDepth.lean` under the
repository's 900-line module rule; no name, statement or import path changed.  Clients that need
the whole depth-generic chain still import `…InnerSequenceDepth`, which re-exports this file
through `…InnerGrowthDepth`.
-/

namespace AlgebraicComplexity.Examples

open scoped BigOperators
open AlgebraicComplexity Tensor

universe u v w x

/-! ## Depth-generic canonical prime field for inner hashing -/

/-- Largest exact ambient source-word leg fiber encountered by an actual marked fine word. -/
noncomputable def cwTotalWeightInnerLegFiberMaximumAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) : ℕ :=
  (Finset.univ : Finset Leg).sup fun c ↦
    (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord).sup fun markedWord ↦
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n markedWord c)).card

/-- Exact standard field-cardinality requirement: three leg fibers and the affine quarter
reserve. -/
noncomputable def cwTotalWeightInnerCompetitorRequirementAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) : ℕ :=
  12 * cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n profile coarseWord

/-- Every marked source word and leg is bounded by the exact maximum. -/
theorem cwTotalWeight_sourceWordLegFiber_card_le_innerMaximumAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (markedWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord)
    (c : Leg) :
    (PartitionHashEncoding.sourceWordLegFiber n
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
      (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤
        cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n profile coarseWord := by
  unfold cwTotalWeightInnerLegFiberMaximumAtDepth
  exact (Finset.le_sup (f := fun word ↦
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n word c)).card)
      hmarkedWord).trans
    (Finset.le_sup (f := fun d : Leg ↦
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord).sup fun word ↦
        (PartitionHashEncoding.sourceWordLegFiber n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) d
          (PartitionHashEncoding.supportWordAddress n word d)).card)
      (Finset.mem_univ c))

/-- Every legal marked target has each ambient hashing leg fiber bounded by the exact source-side
maximum. -/
theorem cwTotalWeight_card_innerTarget_legFiber_leAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord))
    (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (H.legalTargets n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
      triple c).card ≤
        cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n profile coarseWord := by
  have hmarkedSubset := cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
    K q depth n profile coarseWord
  have hambient : triple ∈ H.legalTargets n
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) :=
    H.legalTargets_mono n hmarkedSubset htriple
  rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    n (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) hambient c]
  let markedWord := H.sourceWordOfLegalTriple n triple
  have hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord :=
    H.sourceWordOfLegalTriple_mem_of_mem n _ htriple
  change (PartitionHashEncoding.sourceWordLegFiber n
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
      (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤ _
  exact cwTotalWeight_sourceWordLegFiber_card_le_innerMaximumAtDepth
    K q depth n profile coarseWord markedWord hmarkedWord c

/-- The all-leg collision-proxy family costs at most three exact maximal leg fibers. -/
theorem cwTotalWeight_card_innerTarget_legwiseCompetitors_leAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord)) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (H.legalTargets n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
      triple).card ≤
        3 * cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n profile coarseWord := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  exact fun c ↦ cwTotalWeight_card_innerTarget_legFiber_leAtDepth
    K q depth n H profile coarseWord htriple c

/-- Any field meeting the exact source-side requirement satisfies the marked hashing quarter
budget. -/
theorem cwTotalWeight_innerQuarterBudget_of_fieldCardAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type*} [Field R] [Fintype R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hfield : cwTotalWeightInnerCompetitorRequirementAtDepth
      K q depth n profile coarseWord ≤ Fintype.card R) :
    ∀ triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord),
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
        triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
        triple).card ≤
      4 * (3 * cwTotalWeightInnerLegFiberMaximumAtDepth K q depth n profile coarseWord) :=
        Nat.mul_le_mul_left 4
          (cwTotalWeight_card_innerTarget_legwiseCompetitors_leAtDepth
            K q depth n H profile coarseWord htriple)
    _ = cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n profile coarseWord := by
      unfold cwTotalWeightInnerCompetitorRequirementAtDepth
      ring
    _ ≤ Fintype.card R := hfield

/-- Canonical prime modulus for the inner depth-`depth` hashing problem. -/
noncomputable abbrev cwTotalWeightInnerHashModulusAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) : ℕ :=
  PrimeFieldSizing.modulus (cwChunkAlphabetSize depth)
    (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n profile coarseWord)

/-- Canonical safe prime field for inner depth-`depth` hashing. -/
noncomputable abbrev CWTotalWeightInnerHashFieldAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  ZMod (cwTotalWeightInnerHashModulusAtDepth K q depth n profile coarseWord)

/-- Base-three chunk encoding into the canonical safe prime field. -/
noncomputable def cwTotalWeightInnerPartitionHashEncodingAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    PartitionHashEncoding
      (R := CWTotalWeightInnerHashFieldAtDepth K q depth n profile coarseWord)
      (cwChunkPartitionedTensor K q depth).support :=
  cwChunkPartitionHashEncoding K q depth
    (Nat.le_of_lt (PrimeFieldSizing.characteristicFloor_lt_modulus
      (cwChunkAlphabetSize depth)
      (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n profile coarseWord)))

/-- Two is nonzero in the canonical inner field. -/
noncomputable instance instNeZeroTwoCWTotalWeightInnerHashFieldAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    NeZero (2 : CWTotalWeightInnerHashFieldAtDepth K q depth n profile coarseWord) :=
  PrimeFieldSizing.neZeroTwo (cwChunkAlphabetSize depth)
    (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n profile coarseWord)
    (two_le_cwChunkAlphabetSize depth)

/-- The canonical inner field automatically satisfies the finite quarter budget. -/
theorem cwTotalWeightInnerPrimeField_quarterBudgetAtDepth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ∀ triple ∈ (cwTotalWeightInnerPartitionHashEncodingAtDepth
        K q depth n profile coarseWord).legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord),
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        ((cwTotalWeightInnerPartitionHashEncodingAtDepth
          K q depth n profile coarseWord).legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
        triple).card ≤
      Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n profile coarseWord) := by
  apply cwTotalWeight_innerQuarterBudget_of_fieldCardAtDepth
  simpa only [CWTotalWeightInnerHashFieldAtDepth,
    cwTotalWeightInnerHashModulusAtDepth, ZMod.card] using
    Nat.le_of_lt (PrimeFieldSizing.requirement_lt_modulus (cwChunkAlphabetSize depth)
      (cwTotalWeightInnerCompetitorRequirementAtDepth K q depth n profile coarseWord))

/-- Canonical-prime specialization of the localized marked-leaf extraction at arbitrary depth. -/
theorem exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSumAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (B : Finset (CWTotalWeightInnerHashFieldAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord))
    (hB : ThreeAPFree (B : Set (CWTotalWeightInnerHashFieldAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord))) :
    ∃ seed : ProgressionHash.Seed
        (CWTotalWeightInnerHashFieldAtDepth K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (Fin (n + 1)),
      3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card * B.card ≤
        4 * (Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
          Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)) *
          ((cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord
            ).markedLegwiseIsolatedPowerAddresses n
              (cwTotalWeightLocalizedAmbientWords K q depth n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightMarkedFiberWords K q depth n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              B seed).card ∧
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
                B seed ↦
            matrixMultiplication (K := K)
              (leaf.dimensionProduct .X ^ k)
              (leaf.dimensionProduct .Y ^ k)
              (leaf.dimensionProduct .Z ^ k))) := by
  exact exists_seed_many_cwTotalWeightLocalizedMarkedLeafDirectSum
    K q depth leaf hdimension
    (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    n k coarseWord B hB
    (cwTotalWeightInnerPrimeField_quarterBudgetAtDepth K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
end AlgebraicComplexity.Examples
