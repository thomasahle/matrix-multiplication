/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLocalizedSelection
import AlgebraicComplexity.MatrixMultiplication.ConditionalLegFiberCounting
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing
import AlgebraicComplexity.MatrixMultiplication.PermutationStableLegFiberCounting

set_option autoImplicit false

/-!
# Permutation-stable envelopes for localized total-weight CW fibers

A single total-weight quotient constituent fixes its coarse word pointwise, so it is not invariant
under arbitrary permutations of the sample positions.  The ordinary marginal family obtained by
forgetting that coarse word *is* permutation-stable.  This module embeds every localized family
in that global envelope and applies exact leg-fiber double counting there.

The resulting inequality is deliberately division-free:

`marginal type-class size * localized leg-fiber size ≤ global ambient size`.

This is the sound finite interface for bounding the prime-field size used by inner hashing.  It
does not identify a localized fiber with the global fiber, and therefore does not silently assume
permutation stability after fixing a quotient word.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- Function-level characterization of one localized marginal family: its fine support word maps
to the fixed joint coarse word and its three transposed legs have the prescribed fine marginal
types. -/
theorem mem_cwTotalWeightLocalizedAmbientWords_iff
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) :
    word ∈ cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord ↔
      positiveWordMap
          ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
            (cwTotalWeightChunkCoarsening depth)) n word = coarseWord ∧
      ∀ c, WordType.multiplicity
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (PartitionHashEncoding.supportWordAddress n word c)) =
        cwTotalWeightFineMarginalType K q depth profile c := by
  classical
  rw [cwTotalWeightLocalizedAmbientWords,
    PartitionedTensor.mem_positiveWordsOverSupport,
    cwTotalWeightLocalizedFineTypes,
    PartitionedTensor.mem_select_support,
    PartitionedTensor.coarseningFiber_support,
    PartitionedTensor.mem_coarseningFiberSupport]
  constructor
  · rintro ⟨⟨_hpower, hcoarseAddress⟩, hmarginal⟩
    refine ⟨?_, fun c ↦ mem_positiveTypeClass.mp (hmarginal c)⟩
    apply Tensor.positiveSupportWordBlockAddress_injective
      (CWTotalWeightCoarseSupport K q depth) n
    rw [(cwChunkPartitionedTensor K q depth
      ).positiveSupportWordBlockAddress_coarseningSupportMap
        (cwTotalWeightChunkCoarsening depth) n word]
    exact hcoarseAddress
  · rintro ⟨hcoarseWord, hmarginal⟩
    refine ⟨⟨?_, ?_⟩, fun c ↦ mem_positiveTypeClass.mpr (hmarginal c)⟩
    · rw [(cwChunkPartitionedTensor K q depth
        ).positivePower_support_eq_image_positiveSupportWordBlockAddress n]
      exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩
    · change (fun c ↦ positiveWordMap
          (cwTotalWeightChunkCoarsening depth c) n
          (positiveSupportWordBlockAddress
            (cwChunkPartitionedTensor K q depth).support n word c)) = _
      rw [← (cwChunkPartitionedTensor K q depth
        ).positiveSupportWordBlockAddress_coarseningSupportMap
          (cwTotalWeightChunkCoarsening depth) n word,
        hcoarseWord]

/-- One localized quotient constituent is invariant under precisely the position permutations
that stabilize its fixed joint coarse word. -/
theorem cwTotalWeightLocalizedAmbientWords_reindex_mem_iff_of_coarse_stable
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (e : Equiv.Perm (Fin (n + 1)))
    (hcoarseStable :
      positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord ∘ e.symm =
        positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) :
    word ∈ cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord ↔
      PartitionHashEncoding.positiveWordReindex n e word ∈
        cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord := by
  classical
  let coarseSource :=
    positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord
  have forward : ∀ (permutation : Equiv.Perm (Fin (n + 1)))
      (hstable : coarseSource ∘ permutation.symm = coarseSource)
      (fineWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n),
      fineWord ∈ cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord →
        PartitionHashEncoding.positiveWordReindex n permutation fineWord ∈
          cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord := by
    intro permutation hstable fineWord hfineWord
    rw [mem_cwTotalWeightLocalizedAmbientWords_iff] at hfineWord ⊢
    refine ⟨?_, ?_⟩
    · apply (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n).injective
      have hmap := congrArg
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n) hfineWord.1
      rw [positiveWordEquiv_map] at hmap ⊢
      rw [PartitionHashEncoding.positiveWordEquiv_positiveWordReindex]
      change
        ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
            (cwTotalWeightChunkCoarsening depth) ∘
          positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n fineWord) ∘
            permutation.symm = coarseSource
      rw [hmap]
      exact hstable
    · intro c
      have hreindex :=
        PartitionHashEncoding.positiveWordEquiv_supportWordAddress_reindex
          (A := fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1))
          (support := (cwChunkPartitionedTensor K q depth).support)
          n permutation fineWord c
      calc
        WordType.multiplicity
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              (PartitionHashEncoding.supportWordAddress n
                (PartitionHashEncoding.positiveWordReindex n permutation fineWord) c)) =
          WordType.multiplicity
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              (PartitionHashEncoding.supportWordAddress n fineWord c) ∘ permutation.symm) :=
            congrArg WordType.multiplicity hreindex
        _ = WordType.multiplicity
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              (PartitionHashEncoding.supportWordAddress n fineWord c)) :=
            WordType.multiplicity_reindex permutation _
        _ = cwTotalWeightFineMarginalType K q depth profile c := hfineWord.2 c
  constructor
  · exact forward e hcoarseStable word
  · intro hword
    have hcoarseStableBack : coarseSource ∘ e = coarseSource := by
      funext i
      have hi := congrFun hcoarseStable (e i)
      simpa [coarseSource, Function.comp_apply] using hi.symm
    have hback := forward e.symm hcoarseStableBack
      (PartitionHashEncoding.positiveWordReindex n e word) hword
    simpa using hback

/-- Exact conditional fine-leg profile over the full joint total-weight support symbol.  This is
the orbit invariant for the stabilizer of one coarse support word. -/
noncomputable def cwTotalWeightConditionalLegType
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) :
    CWTotalWeightCoarseSupport K q depth ×
        PositiveWord CWBlock (2 ^ depth - 1) → ℕ :=
  WordType.mappedType
    (fun s : (cwChunkPartitionedTensor K q depth).support ↦
      ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
        (cwTotalWeightChunkCoarsening depth) s, s.1 c))
    profile

/-- Every exact marked fine word realizes the certificate-determined conditional profile on each
leg.  In particular this conditional type is independent of the representative fine lift. -/
theorem cwTotalWeightMarkedFiberWords_conditionalLegType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (markedWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord)
    (c : Leg) :
    WordType.multiplicity
      (WordType.jointWord
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (PartitionHashEncoding.supportWordAddress n markedWord c))) =
      cwTotalWeightConditionalLegType K q depth profile c := by
  have htyped := ((cwChunkPartitionedTensor K q depth
    ).mem_typedCoarseningFiberPositiveWords_iff
      (cwTotalWeightChunkCoarsening depth) n profile coarseWord markedWord).mp hmarkedWord
  have hcoarse := congrArg
    (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n) htyped.2
  rw [positiveWordEquiv_map] at hcoarse
  have hjoint :
      WordType.jointWord
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (PartitionHashEncoding.supportWordAddress n markedWord c)) =
        (fun s : (cwChunkPartitionedTensor K q depth).support ↦
          ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
            (cwTotalWeightChunkCoarsening depth) s, s.1 c)) ∘
          positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n markedWord := by
    funext i
    apply Prod.ext
    · have hi := congrFun hcoarse i
      change
        positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord i =
          (((cwChunkPartitionedTensor K q depth).coarseningSupportMap
            (cwTotalWeightChunkCoarsening depth)) ∘
            positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n markedWord) i
      exact hi.symm
    · exact congrFun
        (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n markedWord c) i
  rw [hjoint, WordType.multiplicity_comp_eq_mappedType, htyped.1]
  rfl

/-- Sharp conditional, division-free upper bound for every marked source-word leg fiber inside
one fixed total-weight quotient constituent. -/
theorem cwTotalWeight_card_conditionalLegType_mul_card_markedSourceWordLegFiber_le
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (markedWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord)
    (c : Leg) :
    (WordType.conditionalTypeClass
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightConditionalLegType K q depth profile c)).card *
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord).card := by
  have hconditional :=
    cwTotalWeightMarkedFiberWords_conditionalLegType
      K q depth n profile coarseWord markedWord hmarkedWord c
  simpa only [hconditional] using
    (PartitionHashEncoding.card_conditionalTypeClass_mul_card_sourceWordLegFiber_le
      n (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (fun e word hstable ↦
        cwTotalWeightLocalizedAmbientWords_reindex_mem_iff_of_coarse_stable
          K q depth n profile coarseWord e hstable word)
      (PartitionHashEncoding.supportWordAddress n markedWord c))

/-- Hash-encoded form of the sharp conditional leg-fiber bound.  This is the direct quantitative
input to the standard three-leg competitor and quarter-budget estimates. -/
theorem cwTotalWeight_card_conditionalLegType_mul_card_markedLegalLegFiber_le
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type v} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord))
    (c : Leg) :
    (WordType.conditionalTypeClass
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightConditionalLegType K q depth profile c)).card *
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
        triple c).card ≤
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord).card := by
  have hsubset := cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
    K q depth n profile coarseWord
  have hambient : triple ∈ H.legalTargets n
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) :=
    H.legalTargets_mono n hsubset htriple
  rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    n (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) hambient c]
  let markedWord := H.sourceWordOfLegalTriple n triple
  have hmarkedWord : markedWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord :=
    H.sourceWordOfLegalTriple_mem_of_mem n _ htriple
  change (WordType.conditionalTypeClass
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightConditionalLegType K q depth profile c)).card *
      (PartitionHashEncoding.sourceWordLegFiber n
        (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord) c
        (PartitionHashEncoding.supportWordAddress n markedWord c)).card ≤ _
  exact cwTotalWeight_card_conditionalLegType_mul_card_markedSourceWordLegFiber_le
    K q depth n profile coarseWord markedWord hmarkedWord c

/-- All supported fine words having the three prescribed fine marginal types, with no quotient
word fixed.  This is the permutation-stable envelope of every localized total-weight constituent
with those marginals. -/
noncomputable def cwTotalWeightFineMarginalAmbientWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    Finset (PositiveWord (cwChunkPartitionedTensor K q depth).support n) :=
  Finset.univ.filter fun word ↦ ∀ c,
    WordType.multiplicity
      (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
        (PartitionHashEncoding.supportWordAddress n word c)) =
      cwTotalWeightFineMarginalType K q depth profile c

/-- Membership in the global envelope is exactly the conjunction of its three marginal-type
equations. -/
theorem mem_cwTotalWeightFineMarginalAmbientWords_iff
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) :
    word ∈ cwTotalWeightFineMarginalAmbientWords K q depth n profile ↔
      ∀ c, WordType.multiplicity
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (PartitionHashEncoding.supportWordAddress n word c)) =
        cwTotalWeightFineMarginalType K q depth profile c := by
  classical
  simp [cwTotalWeightFineMarginalAmbientWords]

/-- Fixing a total-weight quotient word only shrinks the global fixed-marginal family. -/
theorem cwTotalWeightLocalizedAmbientWords_subset_fineMarginalAmbientWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord ⊆
      cwTotalWeightFineMarginalAmbientWords K q depth n profile := by
  classical
  intro word hword
  rw [mem_cwTotalWeightFineMarginalAmbientWords_iff]
  intro c
  have haddress :=
    ((cwChunkPartitionedTensor K q depth).mem_positiveWordsOverSupport n
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightFineMarginalType K q depth profile)).support word).mp hword
  have hselected := (PartitionedTensor.mem_select_support
    ((cwChunkPartitionedTensor K q depth).positivePower n |>.coarseningFiber
      (fun c ↦ positiveWordMap (cwTotalWeightChunkCoarsening depth c) n)
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord))
    (fun c fineWord ↦ fineWord ∈ positiveTypeClass
      (PositiveWord CWBlock (2 ^ depth - 1)) n
      (cwTotalWeightFineMarginalType K q depth profile c))
    (positiveSupportWordBlockAddress
      (cwChunkPartitionedTensor K q depth).support n word)).mp haddress
  exact mem_positiveTypeClass.mp (hselected.2 c)

/-- The global fixed-marginal family is invariant under every common permutation of sample
positions. -/
theorem cwTotalWeightFineMarginalAmbientWords_reindex_mem_iff
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (e : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) :
    word ∈ cwTotalWeightFineMarginalAmbientWords K q depth n profile ↔
      PartitionHashEncoding.positiveWordReindex n e word ∈
        cwTotalWeightFineMarginalAmbientWords K q depth n profile := by
  classical
  have forward : ∀ (permutation : Equiv.Perm (Fin (n + 1)))
      (source : PositiveWord (cwChunkPartitionedTensor K q depth).support n),
      source ∈ cwTotalWeightFineMarginalAmbientWords K q depth n profile →
        PartitionHashEncoding.positiveWordReindex n permutation source ∈
          cwTotalWeightFineMarginalAmbientWords K q depth n profile := by
    intro permutation source hsource
    rw [mem_cwTotalWeightFineMarginalAmbientWords_iff] at hsource ⊢
    intro c
    have hreindex :=
      PartitionHashEncoding.positiveWordEquiv_supportWordAddress_reindex
        (A := fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1))
        (support := (cwChunkPartitionedTensor K q depth).support)
        n permutation source c
    calc
      WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (PartitionHashEncoding.supportWordAddress n
              (PartitionHashEncoding.positiveWordReindex n permutation source) c)) =
        WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (PartitionHashEncoding.supportWordAddress n source c) ∘ permutation.symm) :=
          congrArg WordType.multiplicity hreindex
      _ = WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (PartitionHashEncoding.supportWordAddress n source c)) :=
          WordType.multiplicity_reindex permutation _
      _ = cwTotalWeightFineMarginalType K q depth profile c := hsource c
  constructor
  · exact forward e word
  · intro hword
    have hback := forward e.symm
      (PartitionHashEncoding.positiveWordReindex n e word) hword
    simpa using hback

/-- Exact division-free double count in the global fixed-marginal envelope. -/
theorem cwTotalWeight_card_marginalType_mul_card_globalLegFiber
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type v} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightFineMarginalAmbientWords K q depth n profile)) :
    (positiveTypeClass (PositiveWord CWBlock (2 ^ depth - 1)) n
        (cwTotalWeightFineMarginalType K q depth profile c)).card *
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n
          (cwTotalWeightFineMarginalAmbientWords K q depth n profile))
        triple c).card =
      (cwTotalWeightFineMarginalAmbientWords K q depth n profile).card := by
  apply H.card_legType_mul_card_legFiber_legalTargets n
    (cwTotalWeightFineMarginalAmbientWords K q depth n profile) c
    (cwTotalWeightFineMarginalAmbientWords_reindex_mem_iff K q depth n profile)
    (cwTotalWeightFineMarginalType K q depth profile c)
    (fun word hword ↦
      (mem_cwTotalWeightFineMarginalAmbientWords_iff
        K q depth n profile word).mp hword c)
    htriple
  exact mem_positiveTypeClass.mpr
    ((mem_cwTotalWeightFineMarginalAmbientWords_iff
      K q depth n profile (H.sourceWordOfLegalTriple n triple)).mp
      (H.sourceWordOfLegalTriple_mem_of_mem n _ htriple) c)

/-- Sound localized form of the leg-fiber identity.  The left fiber is computed in one fixed
quotient constituent, while the right side counts the permutation-stable global envelope. -/
theorem cwTotalWeight_card_marginalType_mul_card_localizedLegFiber_le
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type v} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (c : Leg)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n
      (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord)) :
    (positiveTypeClass (PositiveWord CWBlock (2 ^ depth - 1)) n
        (cwTotalWeightFineMarginalType K q depth profile c)).card *
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n
          (cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord))
        triple c).card ≤
      (cwTotalWeightFineMarginalAmbientWords K q depth n profile).card := by
  let localized := cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord
  let global := cwTotalWeightFineMarginalAmbientWords K q depth n profile
  have hsubset : localized ⊆ global :=
    cwTotalWeightLocalizedAmbientWords_subset_fineMarginalAmbientWords
      K q depth n profile coarseWord
  have hglobal : triple ∈ H.legalTargets n global :=
    H.legalTargets_mono n hsubset htriple
  have hfiber : (ProgressionHash.LegalTriple.legFiber
      (H.legalTargets n localized) triple c).card ≤
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n global) triple c).card := by
    rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber n localized htriple c,
      H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber n global hglobal c]
    apply Finset.card_le_card
    intro word hword
    rw [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter] at hword ⊢
    exact ⟨hsubset hword.1, hword.2⟩
  calc
    (positiveTypeClass (PositiveWord CWBlock (2 ^ depth - 1)) n
          (cwTotalWeightFineMarginalType K q depth profile c)).card *
        (ProgressionHash.LegalTriple.legFiber
          (H.legalTargets n localized) triple c).card ≤
      (positiveTypeClass (PositiveWord CWBlock (2 ^ depth - 1)) n
          (cwTotalWeightFineMarginalType K q depth profile c)).card *
        (ProgressionHash.LegalTriple.legFiber
          (H.legalTargets n global) triple c).card :=
        Nat.mul_le_mul_left _ hfiber
    _ = global.card :=
      cwTotalWeight_card_marginalType_mul_card_globalLegFiber
        K q depth n H profile c hglobal

end AlgebraicComplexity.Examples
