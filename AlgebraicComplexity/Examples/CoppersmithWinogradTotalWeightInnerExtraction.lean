/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLocalizedSelection
import AlgebraicComplexity.MatrixMultiplication.NestedLaserVolume
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafHashing

set_option autoImplicit false

/-!
# Inner typed-leaf extraction inside a total-weight quotient constituent

The outer total-weight cleanup separates quotient constituents.  Each retained constituent still
contains a whole fine type-selected tensor.  This module runs the ordinary marked affine hashing
argument *inside* that localized tensor and therefore produces the genuine inner direct sum whose
copy exponent is the usual typed-leaf/combination-loss exponent.

The finite theorem is fully semantic: it identifies the localized support with the modeled fine
word family and proves every retained constituent is the original fine-power constituent.  A
client supplies only a constant-sum injective field encoding of the fine chunk alphabet and the
standard finite competitor bound.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x y

/-- A localized total-weight marginal fiber restricts to a genuine indexed direct sum of equal
fine rational typed leaves.  The marked word family is exactly the pushed-profile fiber, so its
cardinality is the one bounded in `PushedProfileFiberGrowth`. -/
theorem cwTotalWeightLocalizedFineTypes_restricts_markedLeafDirectSum
    (K : Type u) [CommRing K] (q depth : ℕ)
    {R : Type v} [Field R]
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightFineMarginalType K q depth
          (WordType.proportionalCounts leaf.profile.count k))).realize
      (Tensor.indexedDirectSum
        (fun _selected : H.markedLegwiseIsolatedPowerAddresses n
          (cwTotalWeightLocalizedAmbientWords K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)
          (cwTotalWeightMarkedFiberWords K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)
          B seed ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  classical
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  apply leaf.localizedAmbient_restricts_markedLeafDirectSum
    (cwChunk_constituent_restricts_of_leaf_dimension_eq
      K q depth leaf hdimension)
    H n k
    (cwTotalWeightLocalizedAmbientWords K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightMarkedFiberWords K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
      K q depth n (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (fun word hword ↦ cwTotalWeightMarkedFiberWords_type
      K q depth n (WordType.proportionalCounts leaf.profile.count k)
      coarseWord word hword)
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (cwTotalWeightFineMarginalType K q depth
        (WordType.proportionalCounts leaf.profile.count k)))
    (cwTotalWeightLocalizedFineTypes_support_eq_modeledAddresses
      K q depth n H (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightLocalizedFineTypes_constituent K q depth n _ _)
    B hB seed

/-- Good-seed form of the localized inner extraction.  It returns both the division-free exact
survivor count and the polynomial degeneration to that survivor-indexed rectangular family. -/
theorem exists_seed_many_cwTotalWeightLocalizedMarkedLeafDirectSum
    (K : Type u) [CommRing K] (q depth : ℕ)
    {R : Type v} [Field R] [Fintype R]
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord),
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord))
        triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (H.markedLegwiseIsolatedPowerAddresses n
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
          (fun _selected : H.markedLegwiseIsolatedPowerAddresses n
            (cwTotalWeightLocalizedAmbientWords K q depth n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord)
            (cwTotalWeightMarkedFiberWords K q depth n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord)
            B seed ↦
            matrixMultiplication (K := K)
              (leaf.dimensionProduct .X ^ k)
              (leaf.dimensionProduct .Y ^ k)
              (leaf.dimensionProduct .Z ^ k))) := by
  classical
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  exact leaf.exists_seed_many_localizedMarkedLeafDirectSum
    (cwChunk_constituent_restricts_of_leaf_dimension_eq
      K q depth leaf hdimension)
    H n k
    (cwTotalWeightLocalizedAmbientWords K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightMarkedFiberWords K q depth n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
      K q depth n (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (fun word hword ↦ cwTotalWeightMarkedFiberWords_type
      K q depth n (WordType.proportionalCounts leaf.profile.count k)
      coarseWord word hword)
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (cwTotalWeightFineMarginalType K q depth
        (WordType.proportionalCounts leaf.profile.count k)))
    (cwTotalWeightLocalizedFineTypes_support_eq_modeledAddresses
      K q depth n H (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    (cwTotalWeightLocalizedFineTypes_constituent K q depth n _ _)
    B hB hquarter

/-- Build a finite nested laser-volume stage by performing the inner extraction once on a
canonical coarse word and transporting it to every same-type outer survivor.

This is the direct consumer of the position-transport theorem.  The hypotheses expose exactly
the two genuinely quantitative inputs: the number of outer survivors and the number of inner
leaves in the canonical extraction. -/
noncomputable def cwTotalWeightNestedLaserVolumeStage_of_canonicalInner
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source)
    {I : Type w} [Fintype I]
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (reference : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hsame : ∀ i, WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n reference) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n (coarseWord i)))
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    {J : Type x} [Fintype J]
    (outerCopies innerCopies xSize ySize zSize : ℕ)
    (hcardI : Fintype.card I = outerCopies)
    (hcardJ : Fintype.card J = innerCopies)
    (houter : Restricts source
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize)))
    (hcanonical : PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize := by
  apply NestedLaserVolumeStage.ofDependentInnerFamilies K
    hcardI houter (fun _i ↦ hcardJ)
  intro i
  exact cwTotalWeightLocalizedFineTypes_polynomialDegenerates_of_sameCoarseType
    K q depth n fineType reference (coarseWord i) (hsame i) hcanonical

/-- Certificate-facing wrapper: if the reference and every outer survivor belong to one exact
coarse type class, the common-position transport hypothesis is automatic. -/
noncomputable def cwTotalWeightNestedLaserVolumeStage_of_fixedCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source)
    {I : Type w} [Fintype I]
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (reference : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (coarseType : CWTotalWeightCoarseSupport K q depth → ℕ)
    (hreference : reference ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (hcoarseWord : ∀ i, coarseWord i ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    {J : Type x} [Fintype J]
    (outerCopies innerCopies xSize ySize zSize : ℕ)
    (hcardI : Fintype.card I = outerCopies)
    (hcardJ : Fintype.card J = innerCopies)
    (houter : Restricts source
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize)))
    (hcanonical : PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize := by
  refine cwTotalWeightNestedLaserVolumeStage_of_canonicalInner
    K q depth n source coarseWord reference ?_ fineType
    outerCopies innerCopies xSize ySize zSize
    hcardI hcardJ houter hcanonical
  intro i
  rw [mem_positiveTypeClass] at hreference
  have hi := hcoarseWord i
  rw [mem_positiveTypeClass] at hi
  exact hreference.trans hi.symm

end AlgebraicComplexity.Examples
