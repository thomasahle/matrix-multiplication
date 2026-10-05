/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightEmbeddedInnerExtraction

set_option autoImplicit false

/-!
# Canonical total-weight inner sequence for an embedded sparse leaf

The depth-generic total-weight sequence machinery was originally stated for a rational typed leaf
whose alphabet is the entire support of the chunk partition.  That interface is unusable at the
finite stride needed by the certificate: a positive profile of mass nineteen cannot have positive
count on all `6 ^ 16` depth-four chunk letters.

This module carries the sparse embedded finite extraction through the same canonical Behrend seed,
copy-count growth, and `CanonicalInnerSequenceData` interface.  The leaf lives on an arbitrary
finite alphabet `I`; `letter : I ↪ (cwChunkPartitionedTensor K q depth).support` is its semantic
embedding, and `cwEmbeddedChunkProfile leaf letter` is the exact zero extension used by every
ambient word family and counting theorem.

No assembled tensor restriction is accepted as a hypothesis.  The canonical degeneration below
is the second projection of
`exists_seed_many_cwTotalWeightInnerPrimeEmbeddedMarkedLeafDirectSumAtDepth` for the very seed whose
selected-address type supplies the copy count.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x z

section CanonicalFiniteSequence

variable {K : Type u} [CommRing K]
variable {q depth : ℕ}
variable {I : Type z} [Fintype I] [Nonempty I]
variable {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]

/-- Canonical good affine seed for an embedded sparse leaf. -/
noncomputable def cwTotalWeightInnerEmbeddedBehrendSeedAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    ProgressionHash.Seed
      (CWTotalWeightInnerHashFieldAtDepth K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
      (Fin (n + 1)) :=
  Classical.choose
    (exists_seed_many_cwTotalWeightInnerPrimeEmbeddedMarkedLeafDirectSumAtDepth
      K q depth leaf letter hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord))

/-- Exact number of selected addresses at the canonical embedded-leaf seed. -/
noncomputable def cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) : ℕ :=
  ((cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightInnerEmbeddedBehrendSeedAtDepth
          leaf letter hdimension n k coarseWord)).card

/-- Selected-address type whose cardinality is the embedded canonical copy count. -/
noncomputable abbrev CWTotalWeightInnerEmbeddedBehrendIndexAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwTotalWeightInnerPartitionHashEncodingAtDepth K q depth n
      (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
        (cwTotalWeightInnerEmbeddedBehrendSeedAtDepth
          leaf letter hdimension n k coarseWord)

@[simp] theorem card_cwTotalWeightInnerEmbeddedBehrendIndexAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    Fintype.card (CWTotalWeightInnerEmbeddedBehrendIndexAtDepth
      leaf letter hdimension n k coarseWord) =
      cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
        leaf letter hdimension n k coarseWord := by
  exact Fintype.card_coe _

/-- Exact division-free hashing count for the embedded canonical choices. -/
theorem cwTotalWeightInnerEmbeddedBehrend_hashCountAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    3 * (cwTotalWeightMarkedFiberWords K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
        coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord / 2) ≤
      4 * (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord *
        cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord) *
        cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
          leaf letter hdimension n k coarseWord := by
  have hspec := (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeEmbeddedMarkedLeafDirectSumAtDepth
      K q depth leaf letter hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord))).1
  calc
    3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord / 2) =
      3 * (cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord).card *
        (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
          coarseWord).card := by
      rw [cwTotalWeightInnerBehrendBucketsAtDepth_card]
    _ ≤ 4 * (Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
            coarseWord) *
          Fintype.card (CWTotalWeightInnerHashFieldAtDepth K q depth n
            (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k)
            coarseWord)) *
        cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
          leaf letter hdimension n k coarseWord := by
      simpa only [cwTotalWeightInnerEmbeddedBehrendSeedAtDepth,
        cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth] using hspec
    _ = 4 * (cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord *
        cwTotalWeightInnerHashModulusAtDepth K q depth n
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord) *
        cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
          leaf letter hdimension n k coarseWord := by
      simp only [CWTotalWeightInnerHashFieldAtDepth, ZMod.card,
        cwTotalWeightInnerHashModulusAtDepth]

/-- Exact tensor degeneration for the embedded canonical inner-copy sequence. -/
theorem cwTotalWeightInnerEmbeddedBehrend_degeneratesAtDepth
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightFineMarginalType K q depth
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k))).realize
      (Tensor.indexedDirectSum
        (fun _selected : CWTotalWeightInnerEmbeddedBehrendIndexAtDepth
            leaf letter hdimension n k coarseWord ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  exact (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeEmbeddedMarkedLeafDirectSumAtDepth
      K q depth leaf letter hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBucketsAtDepth K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord)
      (cwTotalWeightInnerBehrendBucketsAtDepth_threeAPFree K q depth n
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) k) coarseWord))).2

end CanonicalFiniteSequence

namespace CWTotalWeightInnerGrowthDataAtDepth

variable {K : Type u} [CommRing K]
variable {q depth : ℕ}
variable {I : Type z} [Fintype I] [Nonempty I]
variable {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]

/-- Every base below the target/field quotient is eventually attained by the embedded canonical
Behrend copy sequence.  This is the quantitative proof used by the full-support constructor, with
the ambient profile consistently replaced by the sparse profile's zero extension. -/
theorem exists_eventually_pow_le_embeddedBehrendCopies
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W <
      cwTotalWeightInnerTargetBase K q depth (cwEmbeddedChunkProfile leaf letter) /
        (δ * cwTotalWeightInnerCompetitorBase K q depth
          (cwEmbeddedChunkProfile leaf letter) ambientBase)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 0 < k →
      W ^ k ≤
        (cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
          leaf letter hdimension (data.exponent k) k (data.coarseWord k) : ℝ) := by
  let profile := cwEmbeddedChunkProfile leaf letter
  let targetBase := cwTotalWeightInnerTargetBase K q depth profile
  let fieldBase := cwTotalWeightInnerCompetitorBase K q depth profile ambientBase
  let enlargedFieldBase := δ * fieldBase
  let targetLoss := WordType.pushedTypeFiberLoss profile
  let poly : ℕ → ℝ := fun k ↦ 4 * targetLoss k
  have hprofileMass : 0 < WordType.profileMass profile := by
    rw [show profile = cwEmbeddedChunkProfile leaf letter from rfl,
      profileMass_cwEmbeddedChunkProfile]
    exact leaf.profile.mass_pos
  have hfieldBase : 0 < fieldBase := by
    exact zero_lt_one.trans_le
      (one_le_cwTotalWeightInnerCompetitorBase K q depth profile ambientBase)
  have henlargedFieldBase : 0 < enlargedFieldBase := by
    exact mul_pos (zero_lt_one.trans hδ) hfieldBase
  have hpoly : Growth.Subexponential poly := by
    exact (WordType.pushedTypeFiberLoss_subexponential profile).const_mul
      (by norm_num : (0 : ℝ) ≤ 4)
  obtain ⟨Nfield, hNfield⟩ := data.fieldLoss_subexponential.eventually_le_pow hδ
  obtain ⟨Nrate, hNrate⟩ := Growth.exists_forall_pow_le_copies
    henlargedFieldBase (by norm_num : (0 : ℝ) < 1) hpoly hW
    (by simpa only [targetBase, enlargedFieldBase, fieldBase, profile] using hWrate)
  refine ⟨max Nfield Nrate, fun k hk hkpos ↦ ?_⟩
  have hkField : Nfield ≤ k := (Nat.le_max_left _ _).trans hk
  have hkRate : Nrate ≤ k := (Nat.le_max_right _ _).trans hk
  let M := data.modulus k
  let copies := cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
    leaf letter hdimension (data.exponent k) k (data.coarseWord k)
  have hMtwo : 2 ≤ M := by
    have hchar := PrimeFieldSizing.characteristicFloor_lt_modulus
      (cwChunkAlphabetSize depth) (data.requirement k)
    have hfloor := two_le_cwChunkAlphabetSize depth
    dsimp [M, CWTotalWeightInnerGrowthDataAtDepth.modulus]
    omega
  have hMsharp : (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := by
    simpa only [M, fieldBase, profile] using
      data.modulus_cast_le_fieldLoss_mul_pow hprofileMass k hkpos
  have hMupper : (M : ℝ) ≤ 1 * enlargedFieldBase ^ k := by
    calc
      (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := hMsharp
      _ ≤ δ ^ k * fieldBase ^ k :=
        mul_le_mul_of_nonneg_right (hNfield k hkField)
          (pow_nonneg hfieldBase.le k)
      _ = 1 * enlargedFieldBase ^ k := by
        rw [one_mul, mul_pow]
  have htarget := data.targetBase_pow_le_markedFiber hprofileMass k hkpos
  let marked := (cwTotalWeightMarkedFiberWords K q depth (data.exponent k)
    (WordType.proportionalCounts profile k) (data.coarseWord k)).card
  have htarget' : targetBase ^ k ≤ targetLoss k * (marked : ℝ) := by
    simpa only [targetBase, targetLoss, marked, profile] using htarget
  have hhashNat := cwTotalWeightInnerEmbeddedBehrend_hashCountAtDepth
    leaf letter hdimension (data.exponent k) k (data.coarseWord k)
  have hhash : 3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    exact_mod_cast hhashNat
  have hcount : targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
      poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    calc
      targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
          (targetLoss k * (marked : ℝ)) * (rothNumberNat (M / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right htarget' (by positivity)
      _ ≤ targetLoss k *
          (3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ)) := by
        have htargetLoss : 0 ≤ targetLoss k :=
          (WordType.pushedTypeFiberLoss_pos profile k).le
        have hmarkedRoth : 0 ≤ (marked : ℝ) *
            (rothNumberNat (M / 2) : ℝ) := by positivity
        nlinarith
      _ ≤ targetLoss k *
          (4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ)) :=
        mul_le_mul_of_nonneg_left hhash
          (WordType.pushedTypeFiberLoss_pos profile k).le
      _ = poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
        unfold poly
        ring
  exact hNrate k M copies hkRate hMtwo hMupper hcount

/-- The embedded canonical selected-address family is nonempty at every positive repetition. -/
theorem embeddedBehrendCopies_pos
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    (k : ℕ) (hk : 0 < k) :
    0 < cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
      leaf letter hdimension (data.exponent k) k (data.coarseWord k) := by
  let profile := cwEmbeddedChunkProfile leaf letter
  let M := data.modulus k
  let marked := (cwTotalWeightMarkedFiberWords K q depth (data.exponent k)
    (WordType.proportionalCounts profile k) (data.coarseWord k)).card
  let copies := cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
    leaf letter hdimension (data.exponent k) k (data.coarseWord k)
  have hprofileMass : 0 < WordType.profileMass profile := by
    rw [show profile = cwEmbeddedChunkProfile leaf letter from rfl,
      profileMass_cwEmbeddedChunkProfile]
    exact leaf.profile.mass_pos
  have hM : cwChunkAlphabetSize depth < M := by
    simpa only [M, CWTotalWeightInnerGrowthDataAtDepth.modulus] using
      PrimeFieldSizing.characteristicFloor_lt_modulus
        (cwChunkAlphabetSize depth) (data.requirement k)
  have hfloor := two_le_cwChunkAlphabetSize depth
  have hhalf : 0 < M / 2 := by omega
  have htarget := data.targetBase_pow_le_markedFiber hprofileMass k hk
  have htarget' :
      cwTotalWeightInnerTargetBase K q depth profile ^ k ≤
        WordType.pushedTypeFiberLoss profile k * (marked : ℝ) := by
    simpa only [marked, profile] using htarget
  have htargetPos : 0 < cwTotalWeightInnerTargetBase K q depth profile ^ k :=
    pow_pos (cwTotalWeightInnerTargetBase_pos K q depth profile) k
  have hmarked : 0 < marked := by
    by_contra hnot
    have hzero : marked = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.cast_zero, mul_zero] at htarget'
    exact (not_lt_of_ge htarget') htargetPos
  have hroth : 0 < rothNumberNat (M / 2) := rothNumberNat_pos hhalf
  have hhash : 3 * marked * rothNumberNat (M / 2) ≤ 4 * (M * M) * copies := by
    simpa only [M, marked, copies, profile,
      CWTotalWeightInnerGrowthDataAtDepth.modulus,
      CWTotalWeightInnerGrowthDataAtDepth.requirement,
      cwTotalWeightInnerHashModulusAtDepth] using
      cwTotalWeightInnerEmbeddedBehrend_hashCountAtDepth
        leaf letter hdimension (data.exponent k) k (data.coarseWord k)
  by_contra hnot
  have hzero : copies = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hzero, Nat.mul_zero] at hhash
  have hleft : 0 < 3 * marked * rothNumberNat (M / 2) := by positivity
  omega

/-- Sequence-ready subexponential loss for the embedded canonical copy count. -/
theorem exists_subexponentialLoss_pow_le_embeddedBehrendCopies
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W <
      cwTotalWeightInnerTargetBase K q depth (cwEmbeddedChunkProfile leaf letter) /
        (δ * cwTotalWeightInnerCompetitorBase K q depth
          (cwEmbeddedChunkProfile leaf letter) ambientBase)) :
    ∃ loss : ℕ → ℝ,
      Growth.Subexponential loss ∧
      (∀ k, 0 < loss k) ∧
      ∀ k, 0 < k →
        W ^ k ≤ loss k *
          (cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
            leaf letter hdimension (data.exponent k) k (data.coarseWord k) : ℝ) := by
  obtain ⟨N, hN⟩ := data.exists_eventually_pow_le_embeddedBehrendCopies
    leaf letter hdimension hδ hW hWrate
  refine ⟨Growth.finitePrefixPowerLoss W N,
    Growth.finitePrefixPowerLoss_subexponential hW.le N,
    fun k ↦ Growth.finitePrefixPowerLoss_pos hW N k, ?_⟩
  exact Growth.pow_le_finitePrefixPowerLoss_mul_count hW
    (fun k hk ↦ data.embeddedBehrendCopies_pos leaf letter hdimension k hk) hN

end CWTotalWeightInnerGrowthDataAtDepth

/-! ## Depth-generic embedded sequence constructor -/

/-- Build the canonical inner sequence for a sparse leaf embedded in the depth-`depth` chunk
support.

Every paper-specific object appearing in the conclusion is computed here.  In particular `J` is
the selected-address family of the canonical embedded good seed, and `canonical_degenerates` is
obtained from the finite hashing theorem rather than accepted as a premise. -/
theorem exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, x}
      K q depth T stride outerBase)
    {I : Type z} [Fintype I] [Nonempty I]
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support)
    (hdimension : ∀ i c,
      leaf.dimension i c = cwChunkConstituentDimension K q depth (letter i) c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (growth : CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwEmbeddedChunkProfile leaf letter) ambientBase ambientLoss)
    (hn : ∀ r, outer.n r = growth.exponent r)
    (hfine : ∀ r, outer.fineType r =
      cwTotalWeightFineMarginalType K q depth
        (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) r))
    (hcoarseWordType : ∀ r i,
      WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
            (outer.coarseWord r i)) =
        WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
            (positiveWordCast (hn r).symm (growth.coarseWord r))))
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W <
      cwTotalWeightInnerTargetBase K q depth (cwEmbeddedChunkProfile leaf letter) /
        (δ * cwTotalWeightInnerCompetitorBase K q depth
          (cwEmbeddedChunkProfile leaf letter) ambientBase)) :
    Nonempty
      (CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, v, x, 0}
        outer W
          ((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
            leaf.dimensionProduct .Z : ℕ) : ℝ)) := by
  obtain ⟨innerLoss, hinnerLoss, hinnerLossPos, hinnerGrowth⟩ :=
    growth.exists_subexponentialLoss_pow_le_embeddedBehrendCopies
      leaf letter hdimension hδ hW hWrate
  let reference : ∀ r,
      PositiveWord (CWTotalWeightCoarseSupport K q depth) (outer.n r) :=
    fun r ↦ positiveWordCast (hn r).symm (growth.coarseWord r)
  let coarseType : ℕ → CWTotalWeightCoarseSupport K q depth → ℕ :=
    fun r ↦ WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (outer.n r)
        (reference r))
  let innerCount : ℕ → ℕ := fun r ↦
    cwTotalWeightInnerEmbeddedBehrendCopiesAtDepth
      leaf letter hdimension (growth.exponent r) r (growth.coarseWord r)
  let J : ℕ → Type 0 := fun r ↦
    {a // a ∈ CWTotalWeightInnerEmbeddedBehrendIndexAtDepth
      leaf letter hdimension (growth.exponent r) r (growth.coarseWord r)}
  let xSize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .X ^ r
  let ySize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .Y ^ r
  let zSize : ℕ → ℕ := fun r ↦ leaf.dimensionProduct .Z ^ r
  refine ⟨{
    innerBase_pos := hW
    volumeBase_pos := ?_
    innerLoss := innerLoss
    innerCount := innerCount
    xSize := xSize
    ySize := ySize
    zSize := zSize
    reference := reference
    coarseType := coarseType
    reference_mem := ?_
    coarseWord_mem := ?_
    J := J
    fintypeJ := fun _r ↦ inferInstance
    card_J := ?_
    canonical_degenerates := ?_
    innerLoss_subexponential := hinnerLoss
    innerLoss_pos := fun r _hr ↦ hinnerLossPos r
    innerCount_pos := ?_
    xSize_pos := ?_
    ySize_pos := ?_
    zSize_pos := ?_
    inner_copy_growth := ?_
    volume_growth := ?_
  }⟩
  · exact_mod_cast mul_pos
      (mul_pos (rationalTypedLeaf_dimensionProduct_pos leaf .X)
        (rationalTypedLeaf_dimensionProduct_pos leaf .Y))
      (rationalTypedLeaf_dimensionProduct_pos leaf .Z)
  · intro r
    rw [mem_positiveTypeClass]
  · intro r i
    rw [mem_positiveTypeClass]
    exact hcoarseWordType r i
  · intro r
    simpa only [J, innerCount] using
      card_cwTotalWeightInnerEmbeddedBehrendIndexAtDepth
        leaf letter hdimension (growth.exponent r) r (growth.coarseWord r)
  · intro r hr
    simp only [hfine r]
    have htransport :=
      cwTotalWeightLocalizedFineTypes_isomorphic_of_length_cast
        K q depth (hn r).symm (growth.coarseWord r)
        (cwTotalWeightFineMarginalType K q depth
          (WordType.proportionalCounts (cwEmbeddedChunkProfile leaf letter) r))
    have hcanonical :=
      cwTotalWeightInnerEmbeddedBehrend_degeneratesAtDepth
        leaf letter hdimension (growth.exponent r) r (growth.coarseWord r)
    exact (PolynomialDegenerates.of_restricts htransport.restricts).trans
      (by simpa [J, xSize, ySize, zSize] using hcanonical)
  · intro r hr
    exact growth.embeddedBehrendCopies_pos leaf letter hdimension r hr
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .X) r
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .Y) r
  · intro r _hr
    exact pow_pos (rationalTypedLeaf_dimensionProduct_pos leaf .Z) r
  · intro r hr
    exact hinnerGrowth r hr
  · intro r _hr
    simp only [xSize, ySize, zSize, Nat.cast_mul, Nat.cast_pow, mul_pow]
    exact le_rfl

end AlgebraicComplexity.Examples
