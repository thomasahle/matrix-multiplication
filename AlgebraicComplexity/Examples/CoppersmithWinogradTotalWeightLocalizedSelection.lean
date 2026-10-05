/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing
import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# Fine type selection localized inside total-weight CW quotient constituents

The total-weight compatibility cleanup separates whole quotient constituents.  A later fine
typed-leaf extraction must run inside each such output; projecting each quotient constituent to
only one fine word would lose that inner exponent.  This file supplies the exact semantic bridge:
every retained quotient constituent restricts to the realization of **all** fine addresses in
its quotient fiber whose three leg words have the prescribed fine types.

No type-class cardinality is asserted here.  That quantitative conditional-fiber count is kept
separate from this exact tensor restriction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-- Fine coordinate marginal induced by an exact joint chunk-support profile. -/
noncomputable def cwTotalWeightFineMarginalType
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) : PositiveWord CWBlock (2 ^ depth - 1) → ℕ :=
  WordType.mappedType
    (fun s : (cwChunkPartitionedTensor K q depth).support ↦ s.1 c) profile

/-- Exact fine joint-type lifts of one supported total-weight quotient word. -/
noncomputable def cwTotalWeightTypedFiberWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwChunkPartitionedTensor K q depth).typedCoarseningFiberWords
    (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- Fine positive-power addresses represented by the exact total-weight typed fiber. -/
noncomputable def cwTotalWeightTypedFiberAddresses
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwChunkPartitionedTensor K q depth).typedCoarseningFiberAddresses
    (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- Exact typed lifts represented as positive fine-support words, ready for marked hashing. -/
noncomputable def cwTotalWeightMarkedFiberWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwChunkPartitionedTensor K q depth).typedCoarseningFiberPositiveWords
    (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- The concrete total-weight fine-address family is cardinality-equivalent to the exact
`typedWordMapFiber` consumed by the pushed-profile entropy lower bound. -/
theorem card_cwTotalWeightTypedFiberAddresses
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    (cwTotalWeightTypedFiberAddresses
      K q depth n profile coarseWord).card =
      (cwTotalWeightTypedFiberWords K q depth n profile coarseWord).card :=
    (cwChunkPartitionedTensor K q depth).card_typedCoarseningFiberAddresses
    (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- The marked positive-word family has exactly the pushed-profile typed-fiber cardinality. -/
theorem card_cwTotalWeightMarkedFiberWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    (cwTotalWeightMarkedFiberWords K q depth n profile coarseWord).card =
      (cwTotalWeightTypedFiberWords K q depth n profile coarseWord).card :=
  (cwChunkPartitionedTensor K q depth
    ).card_typedCoarseningFiberPositiveWords
      (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- The fine type-selected partition localized to one total-weight quotient address. -/
noncomputable def cwTotalWeightLocalizedFineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (target : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) := by
  classical
  let P := cwChunkPartitionedTensor K q depth
  let wordMap : ∀ c,
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n →
        PositiveWord (CWCoarseDigit depth) n :=
    fun c ↦ positiveWordMap (cwTotalWeightChunkCoarsening depth c) n
  exact ((P.positivePower n).coarseningFiber wordMap target).select
    (fun c word ↦ word ∈ positiveTypeClass
      (PositiveWord CWBlock (2 ^ depth - 1)) n (fineType c))

/-- Fine support words whose addresses occur in one localized total-weight marginal fiber. -/
noncomputable def cwTotalWeightLocalizedAmbientWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :=
  (cwChunkPartitionedTensor K q depth).positiveWordsOverSupport n
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (cwTotalWeightFineMarginalType K q depth profile)).support

/-- The exact typed-fiber address family lies in the localized fine marginal selection attached
to the same coarse word.  Together with `card_cwTotalWeightTypedFiberAddresses`, this is the
finite semantic/cardinality bridge for the ordinary inner extraction. -/
theorem cwTotalWeightTypedFiberAddresses_subset_localizedFineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    cwTotalWeightTypedFiberAddresses K q depth n profile coarseWord ⊆
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord)
        (cwTotalWeightFineMarginalType K q depth profile)).support :=
  (cwChunkPartitionedTensor K q depth
    ).typedCoarseningFiberAddresses_subset_localizedMarginalTypes
      (cwTotalWeightChunkCoarsening depth) n profile coarseWord

/-- Localized quotient-fiber selection never introduces an address outside the original fine
positive-power support. -/
theorem cwTotalWeightLocalizedFineTypes_support_subset_positivePower
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (target : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    (cwTotalWeightLocalizedFineTypes K q depth n target fineType).support ⊆
      ((cwChunkPartitionedTensor K q depth).positivePower n).support := by
  classical
  intro address haddress
  rw [cwTotalWeightLocalizedFineTypes,
    PartitionedTensor.mem_select_support,
    PartitionedTensor.coarseningFiber_support,
    PartitionedTensor.mem_coarseningFiberSupport] at haddress
  exact haddress.1.1

/-- Every exact joint typed lift is an ambient word of the corresponding localized marginal
fiber. -/
theorem cwTotalWeightMarkedFiberWords_subset_localizedAmbientWords
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    cwTotalWeightMarkedFiberWords K q depth n profile coarseWord ⊆
      cwTotalWeightLocalizedAmbientWords K q depth n profile coarseWord := by
  classical
  intro fineWord hfineWord
  rw [cwTotalWeightLocalizedAmbientWords,
    PartitionedTensor.mem_positiveWordsOverSupport]
  apply cwTotalWeightTypedFiberAddresses_subset_localizedFineTypes
    K q depth n profile coarseWord
  rw [cwTotalWeightMarkedFiberWords,
    PartitionedTensor.typedCoarseningFiberPositiveWords] at hfineWord
  obtain ⟨typedWord, _htypedWord, rfl⟩ := Finset.mem_image.mp hfineWord
  rw [cwTotalWeightTypedFiberAddresses,
    PartitionedTensor.typedCoarseningFiberAddresses]
  exact Finset.mem_image.mpr ⟨typedWord, Finset.mem_univ _, rfl⟩

/-- Every marked localized word has exactly the prescribed fine joint multiplicity type. -/
theorem cwTotalWeightMarkedFiberWords_type
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (fineWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hfineWord : fineWord ∈
      cwTotalWeightMarkedFiberWords K q depth n profile coarseWord) :
    WordType.multiplicity
      (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n fineWord) =
        profile := by
  exact ((cwChunkPartitionedTensor K q depth
    ).mem_typedCoarseningFiberPositiveWords_iff
      (cwTotalWeightChunkCoarsening depth) n profile coarseWord fineWord).mp hfineWord |>.1

/-- Any fine partition hash encoding models the localized marginal fiber exactly when its source
word family is `cwTotalWeightLocalizedAmbientWords`. -/
theorem cwTotalWeightLocalizedFineTypes_support_eq_modeledAddresses
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R)
      (cwChunkPartitionedTensor K q depth).support)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n) :
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (cwTotalWeightFineMarginalType K q depth profile)).support =
      H.modeledAddresses n (H.legalTargets n
        (cwTotalWeightLocalizedAmbientWords
          K q depth n profile coarseWord)) := by
  classical
  rw [H.modeledAddresses_legalTargets_eq_image]
  exact ((cwChunkPartitionedTensor K q depth).image_positiveWordsOverSupport_eq n _
    (cwTotalWeightLocalizedFineTypes_support_subset_positivePower
      K q depth n _ _)).symm

/-- Localization and marginal selection change only the support; every retained constituent is
definitionally the original fine positive-power constituent. -/
theorem cwTotalWeightLocalizedFineTypes_constituent
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (target : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    (cwTotalWeightLocalizedFineTypes K q depth n target fineType).constituent address =
      ((cwChunkPartitionedTensor K q depth).positivePower n).constituent address :=
  rfl

/-- Localized fine type-selected tensors over two total-weight coarse words of the same exact
joint multiplicity type are tensor-isomorphic.  The isomorphism is the common permutation of
sample positions carrying the second coarse word to the first; exact fine marginal types are
invariant under that permutation.

This lets an inner extraction be constructed once for a canonical coarse word and transported
without loss to every outer survivor of the same pushed joint type. -/
theorem cwTotalWeightLocalizedFineTypes_isomorphic_of_sameCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (left right : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hsame : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n left) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n right)) :
    Isomorphic
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n right) fineType).realize
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n left) fineType).realize := by
  classical
  let leftWord := positiveWordEquiv
    (CWTotalWeightCoarseSupport K q depth) n left
  let rightWord := positiveWordEquiv
    (CWTotalWeightCoarseSupport K q depth) n right
  let sigma := WordType.positionPermOfSameMultiplicity leftWord rightWord hsame
  have hword : positiveWordPositionEquiv
      (CWTotalWeightCoarseSupport K q depth) n sigma right = left := by
    apply (positiveWordEquiv
      (CWTotalWeightCoarseSupport K q depth) n).injective
    rw [positiveWordEquiv_position_apply]
    exact WordType.positionPermOfSameMultiplicity_map leftWord rightWord hsame
  have haddress :
      positionRelabelBlockAddress (fun _c ↦ CWCoarseDigit depth) n sigma
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n right) =
        positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n left := by
    rw [positionRelabelBlockAddress_positiveSupportWordBlockAddress, hword]
  have hisomorphic :=
    Tensor.Isomorphic.positivePower_localizedCoarseningFiberTypes_position
      (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n right)
      fineType sigma
  rw [haddress] at hisomorphic
  simpa only [cwTotalWeightLocalizedFineTypes] using hisomorphic

/-- A dependent-length transport lemma for a localized fine family.  The coarse word is
transported with `positiveWordCast`; after eliminating the length equality all data are literally
the same, so this is the canonical identity isomorphism.  Keeping this small lemma explicit avoids
fragile rewriting under the dependent `PositiveWord` and block-address indices in sequence-level
constructions. -/
theorem cwTotalWeightLocalizedFineTypes_isomorphic_of_length_cast
    (K : Type u) [CommRing K] (q depth : ℕ)
    {n m : ℕ} (h : n = m)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    Isomorphic
      (cwTotalWeightLocalizedFineTypes K q depth m
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) m
          (positiveWordCast h coarseWord)) fineType).realize
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n coarseWord) fineType).realize := by
  cases h
  exact Isomorphic.refl _

/-- Profile-specialized transport form used by the inner typed-fiber extraction. -/
theorem cwTotalWeightLocalizedMarginalTypes_isomorphic_of_sameCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (left right : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hsame : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n left) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n right)) :
    Isomorphic
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n right)
        (cwTotalWeightFineMarginalType K q depth profile)).realize
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n left)
        (cwTotalWeightFineMarginalType K q depth profile)).realize :=
  cwTotalWeightLocalizedFineTypes_isomorphic_of_sameCoarseType
    K q depth n (cwTotalWeightFineMarginalType K q depth profile)
    left right hsame

/-- Membership in one exact coarse type class is a convenient certificate-facing form of the
same-type transport hypothesis. -/
theorem cwTotalWeightLocalizedFineTypes_isomorphic_of_mem_sameCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (coarseType : CWTotalWeightCoarseSupport K q depth → ℕ)
    (left right : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hleft : left ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (hright : right ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType) :
    Isomorphic
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n right) fineType).realize
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n left) fineType).realize := by
  apply cwTotalWeightLocalizedFineTypes_isomorphic_of_sameCoarseType
    K q depth n fineType left right
  rw [mem_positiveTypeClass] at hleft hright
  exact hleft.trans hright.symm

/-- Any inner degeneration constructed for one canonical coarse word transports without loss to
every coarse word of the same exact pushed joint type. -/
theorem cwTotalWeightLocalizedFineTypes_polynomialDegenerates_of_sameCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (left right : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hsame : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n left) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n right))
    {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {targetTensor : Tensor3 K W}
    (hinner : PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n left) fineType).realize
      targetTensor) :
    PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n right) fineType).realize
      targetTensor :=
  (PolynomialDegenerates.of_restricts
    (cwTotalWeightLocalizedFineTypes_isomorphic_of_sameCoarseType
      K q depth n fineType left right hsame).restricts).trans hinner

/-- A whole quotient constituent retains the entire localized fine type-selected tensor. -/
theorem cwTotalWeight_coarseConstituent_to_localizedFineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (target : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (htarget : target ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    Restricts
      ((((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).constituent target)
      (cwTotalWeightLocalizedFineTypes K q depth n target fineType).realize := by
  classical
  simpa only [cwTotalWeightLocalizedFineTypes] using
    (Restricts.coarsenedPositivePower_constituent_to_fineFiberSelect
      (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) n target htarget
      (fun c word ↦ word ∈ positiveTypeClass
        (PositiveWord CWBlock (2 ^ depth - 1)) n (fineType c)))

/-- Indexed form: every already-separated outer quotient constituent keeps its whole localized
fine selected tensor, with exactly the same outer index. -/
theorem cwTotalWeight_indexedCoarseConstituents_to_localizedFineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {I : Type w} [Fintype I]
    (target : I → BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (htarget : ∀ i, target i ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).constituent
            (target i)))
      (Tensor.indexedDirectSum (fun i ↦
        (cwTotalWeightLocalizedFineTypes
          K q depth n (target i) fineType).realize)) := by
  classical
  simpa only [cwTotalWeightLocalizedFineTypes] using
    (Restricts.indexedDirectSum_coarsenedPositivePower_constituent_to_fineFiberSelect
      (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) n target htarget
      (fun c word ↦ word ∈ positiveTypeClass
        (PositiveWord CWBlock (2 ^ depth - 1)) n (fineType c)))

/-- Compose any exact quotient cleanup with localized fine type selection.  This is the direct
consumer interface for compatibility/hashing theorems: the final quotient support cardinality
is untouched, and each output contains all fine typed constituents in its own quotient fiber. -/
theorem cwTotalWeightCleanup_to_localizedFineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {S : Leg → Type w} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    (source : Tensor3 K S)
    (finalSupport : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hfinalSupport : finalSupport ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hcleanup : Restricts source
      (Tensor.indexedDirectSum (fun address : finalSupport ↦
        (((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).constituent
            address.1)))
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    Restricts source
      (Tensor.indexedDirectSum (fun address : finalSupport ↦
        (cwTotalWeightLocalizedFineTypes
          K q depth n address.1 fineType).realize)) :=
  hcleanup.trans
    (cwTotalWeight_indexedCoarseConstituents_to_localizedFineTypes
      K q depth n (fun address : finalSupport ↦ address.1)
      (fun address ↦ hfinalSupport address.2) fineType)

end AlgebraicComplexity.Examples
