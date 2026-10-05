/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PrimeFieldSizing
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkHashEncoding
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerFiberCounting

set_option autoImplicit false

/-!
# Canonical prime field for inner hashing in a total-weight CW fiber

The inner marked-hashing theorem needs a field at least four times larger than its collision-proxy
family.  A proxy family is bounded by the sum of three ambient leg fibers.  We take the exact
maximum of those source-side leg fibers over the actual marked family, so the resulting
requirement `12 * maximum` is independent of the field and loses no exponential information.

At paper level two, characteristic nine is already enough for the base-three chunk encoding.
Choosing the next prime above both nine and the exact competitor requirement therefore discharges
the encoding, odd-characteristic, and quarter-budget obligations automatically.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Largest exact ambient source-word leg fiber encountered by an actual marked fine word. -/
noncomputable def cwTotalWeightInnerLegFiberMaximum
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) : ℕ :=
  (Finset.univ : Finset Leg).sup fun c ↦
    (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord).sup fun markedWord ↦
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n markedWord c)).card

/-- Exact standard field-cardinality requirement: three leg fibers and the affine quarter
reserve. -/
noncomputable def cwTotalWeightInnerCompetitorRequirement
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) : ℕ :=
  12 * cwTotalWeightInnerLegFiberMaximum K q n profile coarseWord

/-- Every marked source word and leg is bounded by the exact maximum. -/
theorem cwTotalWeight_sourceWordLegFiber_card_le_innerMaximum
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    (markedWord : PositiveWord (cwChunkPartitionedTensor K q 1).support n)
    (hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord)
    (c : Leg) :
    (PartitionHashEncoding.sourceWordLegFiber n
      (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) c
      (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤
        cwTotalWeightInnerLegFiberMaximum K q n profile coarseWord := by
  unfold cwTotalWeightInnerLegFiberMaximum
  exact (Finset.le_sup (f := fun word ↦
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n word c)).card)
      hmarkedWord).trans
    (Finset.le_sup (f := fun d : Leg ↦
      (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord).sup fun word ↦
        (PartitionHashEncoding.sourceWordLegFiber n
          (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) d
          (PartitionHashEncoding.supportWordAddress n word d)).card)
      (Finset.mem_univ c))

/-- Every legal marked target has each ambient hashing leg fiber bounded by the exact source-side
maximum. -/
theorem cwTotalWeight_card_innerTarget_legFiber_le
    (K : Type u) [CommRing K] (q n : ℕ)
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q 1).support)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord))
    (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (H.legalTargets n
        (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord))
      triple c).card ≤
        cwTotalWeightInnerLegFiberMaximum K q n profile coarseWord := by
  have hmarkedSubset := cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
    K q 1 n profile coarseWord
  have hambient : triple ∈ H.legalTargets n
      (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) :=
    H.legalTargets_mono n hmarkedSubset htriple
  rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    n (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) hambient c]
  let markedWord := H.sourceWordOfLegalTriple n triple
  have hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord :=
    H.sourceWordOfLegalTriple_mem_of_mem n _ htriple
  change (PartitionHashEncoding.sourceWordLegFiber n
      (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord) c
      (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤ _
  exact cwTotalWeight_sourceWordLegFiber_card_le_innerMaximum
    K q n profile coarseWord markedWord hmarkedWord c

/-- The all-leg collision-proxy family costs at most three exact maximal leg fibers. -/
theorem cwTotalWeight_card_innerTarget_legwiseCompetitors_le
    (K : Type u) [CommRing K] (q n : ℕ)
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q 1).support)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord)) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (H.legalTargets n
        (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord))
      triple).card ≤
        3 * cwTotalWeightInnerLegFiberMaximum K q n profile coarseWord := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  exact fun c ↦ cwTotalWeight_card_innerTarget_legFiber_le
    K q n H profile coarseWord htriple c

/-- Any field meeting the exact source-side requirement satisfies the marked hashing quarter
budget. -/
theorem cwTotalWeight_innerQuarterBudget_of_fieldCard
    (K : Type u) [CommRing K] (q n : ℕ)
    {R : Type*} [Field R] [Fintype R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q 1).support)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    (hfield : cwTotalWeightInnerCompetitorRequirement
      K q n profile coarseWord ≤ Fintype.card R) :
    ∀ triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord),
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord))
        triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord))
        triple).card ≤
      4 * (3 * cwTotalWeightInnerLegFiberMaximum K q n profile coarseWord) :=
        Nat.mul_le_mul_left 4
          (cwTotalWeight_card_innerTarget_legwiseCompetitors_le
            K q n H profile coarseWord htriple)
    _ = cwTotalWeightInnerCompetitorRequirement K q n profile coarseWord := by
      unfold cwTotalWeightInnerCompetitorRequirement
      ring
    _ ≤ Fintype.card R := hfield

/-- Canonical prime modulus for the inner level-two hashing problem. -/
noncomputable abbrev cwTotalWeightInnerHashModulus
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) : ℕ :=
  PrimeFieldSizing.modulus 9
    (cwTotalWeightInnerCompetitorRequirement K q n profile coarseWord)

/-- Canonical safe prime field for inner level-two hashing. -/
noncomputable abbrev CWTotalWeightInnerHashField
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :=
  ZMod (cwTotalWeightInnerHashModulus K q n profile coarseWord)

/-- Base-three chunk encoding into the canonical safe prime field. -/
noncomputable def cwTotalWeightInnerPartitionHashEncoding
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    PartitionHashEncoding
      (R := CWTotalWeightInnerHashField K q n profile coarseWord)
      (cwChunkPartitionedTensor K q 1).support :=
  cwLevelTwoChunkPartitionHashEncoding K q
    (Nat.le_of_lt (PrimeFieldSizing.characteristicFloor_lt_modulus 9
      (cwTotalWeightInnerCompetitorRequirement K q n profile coarseWord)))

/-- Two is nonzero in the canonical inner field. -/
noncomputable instance instNeZeroTwoCWTotalWeightInnerHashField
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    NeZero (2 : CWTotalWeightInnerHashField K q n profile coarseWord) :=
  PrimeFieldSizing.neZeroTwo 9
    (cwTotalWeightInnerCompetitorRequirement K q n profile coarseWord) (by norm_num)

/-- The canonical inner field automatically satisfies the finite quarter budget. -/
theorem cwTotalWeightInnerPrimeField_quarterBudget
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    ∀ triple ∈ (cwTotalWeightInnerPartitionHashEncoding
        K q n profile coarseWord).legalTargets n
      (cwTotalWeightMarkedFiberWords K q 1 n profile coarseWord),
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        ((cwTotalWeightInnerPartitionHashEncoding
          K q n profile coarseWord).legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q 1 n profile coarseWord))
        triple).card ≤
      Fintype.card (CWTotalWeightInnerHashField K q n profile coarseWord) := by
  apply cwTotalWeight_innerQuarterBudget_of_fieldCard
  simpa only [CWTotalWeightInnerHashField, cwTotalWeightInnerHashModulus, ZMod.card] using
    Nat.le_of_lt (PrimeFieldSizing.requirement_lt_modulus 9
      (cwTotalWeightInnerCompetitorRequirement K q n profile coarseWord))

/-- Canonical-prime specialization of the localized marked-leaf extraction.  In contrast to
`exists_seed_many_cwTotalWeightLocalizedMarkedLeafDirectSum`, a client supplies neither a hash
encoding nor a collision budget: the base-three level-two encoding and the next safe prime above
the exact localized competitor maximum discharge both obligations.

The progression-free bucket set remains explicit because its eventual choice controls the
subexponential hashing loss, rather than finite correctness. -/
theorem exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSum
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    (B : Finset (CWTotalWeightInnerHashField K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord))
    (hB : ThreeAPFree (B : Set (CWTotalWeightInnerHashField K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord))) :
    ∃ seed : ProgressionHash.Seed
        (CWTotalWeightInnerHashField K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (Fin (n + 1)),
      3 * (cwTotalWeightMarkedFiberWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card * B.card ≤
        4 * (Fintype.card (CWTotalWeightInnerHashField K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
          Fintype.card (CWTotalWeightInnerHashField K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)) *
          ((cwTotalWeightInnerPartitionHashEncoding K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord
            ).markedLegwiseIsolatedPowerAddresses n
              (cwTotalWeightLocalizedAmbientWords K q 1 n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightMarkedFiberWords K q 1 n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              B seed).card ∧
      PolynomialDegenerates
        (cwTotalWeightLocalizedFineTypes K q 1 n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q 1) n coarseWord)
          (cwTotalWeightFineMarginalType K q 1
            (WordType.proportionalCounts leaf.profile.count k))).realize
        (Tensor.indexedDirectSum
          (fun _selected : (cwTotalWeightInnerPartitionHashEncoding K q n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord
              ).markedLegwiseIsolatedPowerAddresses n
                (cwTotalWeightLocalizedAmbientWords K q 1 n
                  (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                (cwTotalWeightMarkedFiberWords K q 1 n
                  (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                B seed ↦
            matrixMultiplication (K := K)
              (leaf.dimensionProduct .X ^ k)
              (leaf.dimensionProduct .Y ^ k)
              (leaf.dimensionProduct .Z ^ k))) := by
  exact exists_seed_many_cwTotalWeightLocalizedMarkedLeafDirectSum
    K q 1 leaf hdimension
    (cwTotalWeightInnerPartitionHashEncoding K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)
    n k coarseWord B hB
    (cwTotalWeightInnerPrimeField_quarterBudget K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord)

end AlgebraicComplexity.Examples
