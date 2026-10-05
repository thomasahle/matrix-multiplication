/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerSequenceDepth
import AlgebraicComplexity.MatrixMultiplication.EmbeddedRationalTypedLeafHashing

set_option autoImplicit false

/-!
# Sparse-alphabet inner extraction for a total-weight CW constituent

A depth-four CW chunk partition has an enormous ambient support, while a rational certificate uses
only the finitely many chunk letters carrying positive mass.  This module embeds that positive
alphabet into the ambient support and pushes its count table forward, assigning exact zero mass to
all unused chunk letters.  The localized total-weight hashing theorem then retains the complete
inner copy exponent without requiring a fictitious full-support positive profile.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w z

/-- The zero-extended chunk profile represented by a sparse typed-leaf alphabet. -/
noncomputable def cwEmbeddedChunkProfile
    {K : Type u} [CommRing K] {q depth : ℕ}
    {I : Type z} [Fintype I]
    {C : Leg → Type w}
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support) :
    (cwChunkPartitionedTensor K q depth).support → ℕ :=
  WordType.mappedType letter leaf.profile.count

/-- Embedding a sparse positive profile preserves its exact total mass. -/
theorem profileMass_cwEmbeddedChunkProfile
    {K : Type u} [CommRing K] {q depth : ℕ}
    {I : Type z} [Fintype I]
    {C : Leg → Type w}
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support) :
    WordType.profileMass (cwEmbeddedChunkProfile leaf letter) = leaf.profile.mass := by
  exact WordType.profileMass_mappedType letter leaf.profile.count

/-- Canonical chunk constituent restriction in the dimension-table form consumed by embedded
typed-leaf extraction. -/
theorem cwChunkSupportedConstituent_restricts_canonicalDimension
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
      (matrixMultiplication (K := K)
        (cwChunkConstituentDimension K q depth support .X)
        (cwChunkConstituentDimension K q depth support .Y)
        (cwChunkConstituentDimension K q depth support .Z)) := by
  exact cwChunkSupportedConstituent_restricts_productDimensions K q depth support

/-- Good-seed inner extraction for a sparse rational typed leaf at arbitrary chunk depth.

The exact length equation is recovered from any selected marked word's pushed multiplicity type.
If the marked family is empty, the resulting empty direct sum and zero count remain valid. -/
theorem exists_seed_many_cwTotalWeightInnerPrimeEmbeddedMarkedLeafDirectSumAtDepth
    (K : Type u) [CommRing K] (q depth : ℕ)
    {I : Type z} [Fintype I] [Nonempty I]
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (B : Finset (CWTotalWeightInnerHashFieldAtDepth K q depth n
      (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord))
    (hB : ThreeAPFree (B : Set (CWTotalWeightInnerHashFieldAtDepth K q depth n
      (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord))) :
    ∃ seed : ProgressionHash.Seed
        (CWTotalWeightInnerHashFieldAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (Fin (n + 1)),
      3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord).card * B.card ≤
        4 * (Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord) *
          Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)) *
          ((cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
            (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord
            ).markedLegwiseIsolatedPowerAddresses n
              (cwTotalWeightLocalizedAmbientWords K q depth n
                (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
              (cwTotalWeightMarkedFiberWords K q depth n
                (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
              B seed).card ∧
      PolynomialDegenerates
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n coarseWord)
          (cwTotalWeightFineMarginalType K q depth
            (WordType.proportionalCounts
              (cwEmbeddedChunkProfile leaf letter) k))).realize
        (Tensor.indexedDirectSum
          (fun _selected : (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
              (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord
              ).markedLegwiseIsolatedPowerAddresses n
                (cwTotalWeightLocalizedAmbientWords K q depth n
                  (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
                (cwTotalWeightMarkedFiberWords K q depth n
                  (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
                B seed ↦
            matrixMultiplication (K := K)
              (leaf.dimensionProduct .X ^ k)
              (leaf.dimensionProduct .Y ^ k)
              (leaf.dimensionProduct .Z ^ k))) := by
  let profile := cwEmbeddedChunkProfile leaf letter
  exact leaf.exists_seed_many_localizedEmbeddedMarkedLeafDirectSum
    letter (cwChunkConstituentDimension K q depth)
    (cwChunkSupportedConstituent_restricts_canonicalDimension K q depth)
    hdimension
    (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts profile k) coarseWord)
    n k
    (cwTotalWeightLocalizedAmbientWords K q depth n
      (WordType.proportionalCounts profile k) coarseWord)
    (cwTotalWeightMarkedFiberWords K q depth n
      (WordType.proportionalCounts profile k) coarseWord)
    (cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
      K q depth n (WordType.proportionalCounts profile k) coarseWord)
    (fun word hword ↦ cwTotalWeightMarkedFiberWords_type
      K q depth n (WordType.proportionalCounts profile k)
      coarseWord word hword)
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (cwTotalWeightFineMarginalType K q depth
        (WordType.proportionalCounts profile k)))
    (cwTotalWeightLocalizedFineTypes_support_eq_modeledAddresses
      K q depth n
      (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
        (WordType.proportionalCounts profile k) coarseWord)
      (WordType.proportionalCounts profile k) coarseWord)
    (cwTotalWeightLocalizedFineTypes_constituent K q depth n _ _)
    B hB
    (cwTotalWeightInnerPrimeField_quarterBudgetAtDepth K q depth n
      (WordType.proportionalCounts profile k) coarseWord)

end AlgebraicComplexity.Examples
