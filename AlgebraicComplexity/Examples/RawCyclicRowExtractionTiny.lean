/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RawCyclicRowExtraction
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Tiny semantic client for one-hash raw cyclic-row extraction

This file instantiates the new finite raw-cyclic Mode-B theorem on a one-block partition whose sole
constituent is a pure rank-one scalar tensor.  Its primitive type and cyclic-product type both have
count one, the ambient and marked word families coincide, and the good-seed bound forces at least
one selected address.  The client therefore checks that the theorem's exact-type, one-joint-seed,
raw-partition, arbitrary-child, and tensor-content premises are jointly satisfiable; it is not
merely a restriction to an empty direct sum of zero tensors.

The one-joint-hash specialization is new to the forthcoming legal-hybrid appendix of the
Total-Weight manuscript (`better_bound/paper.tex`).  The ordinary hashing and cleanup argument in
[alman2025more], `papers/sources/2404.16349/constituent.tex:376-440,483-497`, is an ingredient
rather than the statement tested here.
-/

namespace AlgebraicComplexity.Examples.RawCyclicRowExtractionTiny

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommSemiring K]

local instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance twoNeZero : NeZero (2 : ZMod 13) := ⟨by decide⟩

/-- The sole block label on every leg. -/
abbrev OneLabel (_ : Leg) := Unit

/-- Every block space is the scalar module. -/
abbrev OneBlockSpace (_ : Leg) (_ : Unit) := K

/-- The sole three-leg block address. -/
def soleAddress : BlockAddress OneLabel := fun _ ↦ ()

/-- A one-block partition whose sole constituent is the pure scalar rank-one tensor. -/
noncomputable def oneBlockPartition :
    PartitionedTensor (K := K) (A := OneLabel) (OneBlockSpace K) where
  support := {soleAddress}
  constituent := fun _ ↦ pure (K := K) (fun _ : Leg ↦ (1 : K))

/-- The unique supported primitive address. -/
noncomputable def primitiveSupport : (oneBlockPartition K).support :=
  ⟨soleAddress, by simp [oneBlockPartition]⟩

local instance primitiveSupportNonempty : Nonempty (oneBlockPartition K).support :=
  ⟨primitiveSupport K⟩

/-- The unique supported address of the actual three-orientation partition. -/
noncomputable def cyclicSupport : (oneBlockPartition K).symThreePartition.support :=
  ((oneBlockPartition K).symThreeSupportEquiv)
    ((primitiveSupport K, primitiveSupport K), primitiveSupport K)

local instance cyclicSupportNonempty :
    Nonempty (oneBlockPartition K).symThreePartition.support :=
  ⟨cyclicSupport K⟩

/-- The one-letter primitive word used as the reference child. -/
noncomputable def primitiveWord : PositiveWord (oneBlockPartition K).support 0 :=
  (positiveWordEquiv (oneBlockPartition K).support 0).symm
    (fun _ ↦ primitiveSupport K)

/-- The one-letter word in the actual three-orientation support. -/
noncomputable def cyclicWord :
    PositiveWord (oneBlockPartition K).symThreePartition.support 0 :=
  (positiveWordEquiv (oneBlockPartition K).symThreePartition.support 0).symm
    (fun _ ↦ cyclicSupport K)

/-- Unit block labels embed injectively into one common affine-hashing equation. -/
noncomputable def hashEncoding :
    PartitionHashEncoding (R := ZMod 13)
      (oneBlockPartition K).symThreePartition.support where
  encode := fun _c _block ↦ 0
  target := 0
  support_nonempty := ⟨(cyclicSupport K).1, (cyclicSupport K).2⟩
  encode_injective := by
    intro _c left right _h
    exact Subsingleton.elim left right
  legal := by
    intro _address _haddress
    norm_num

/-- The primitive singleton support with its exact count-one profile. -/
noncomputable def primitiveProfile :
    PositiveIntegralProfile (oneBlockPartition K).support where
  alphabet := Finset.univ
  complete := fun _ ↦ Finset.mem_univ _
  count := fun _ ↦ 1
  count_pos := by intro; norm_num

@[simp] theorem primitiveProfile_mass : (primitiveProfile K).mass = 1 := by
  classical
  unfold PositiveIntegralProfile.mass WordType.profileMass primitiveProfile
  have hsupport : Fintype.card (oneBlockPartition K).support = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨primitiveSupport K, fun address ↦ Subsingleton.elim address (primitiveSupport K)⟩
  simpa [Finset.card_univ, hsupport]

private theorem univ_positiveWords_eq_singleton
    {I : Type*} [Fintype I] [DecidableEq I] [Subsingleton I]
    (word : PositiveWord I 0) :
    (Finset.univ : Finset (PositiveWord I 0)) = {word} := by
  ext other
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  apply (positiveWordEquiv I 0).injective
  funext i
  exact Subsingleton.elim _ _

private theorem primitive_reference_type :
    WordType.multiplicity
        (positiveWordEquiv (oneBlockPartition K).support 0 (primitiveWord K)) =
      WordType.proportionalCounts (primitiveProfile K).count
        ((primitiveProfile K).mass ^ 2 * 1) := by
  classical
  funext letter
  rw [show positiveWordEquiv (oneBlockPartition K).support 0 (primitiveWord K) =
      (fun _ ↦ primitiveSupport K) by simp [primitiveWord],
    WordType.multiplicity_const_fin_one]
  have hletter : letter = primitiveSupport K := Subsingleton.elim _ _
  rw [if_pos hletter, primitiveProfile_mass]
  simp [primitiveProfile, WordType.proportionalCounts]

private theorem cyclic_word_type
    (word : PositiveWord (oneBlockPartition K).symThreePartition.support 0) :
    WordType.multiplicity
        (positiveWordEquiv (oneBlockPartition K).symThreePartition.support 0 word) =
      WordType.proportionalCounts
        ((oneBlockPartition K).symThreeSupportProfile (primitiveProfile K)).count 1 := by
  classical
  funext letter
  have hword :
      positiveWordEquiv (oneBlockPartition K).symThreePartition.support 0 word =
        (fun _ ↦ cyclicSupport K) := by
    funext i
    exact Subsingleton.elim _ _
  rw [hword, WordType.multiplicity_const_fin_one]
  have hletter : letter = cyclicSupport K := Subsingleton.elim _ _
  simp [hletter, PartitionedTensor.symThreeSupportProfile,
    PositiveIntegralProfile.reindex, PositiveIntegralProfile.cyclicProduct,
    primitiveProfile, WordType.proportionalCounts]

private theorem competitor_quarter
    (triple : ProgressionHash.LegalTriple (ZMod 13) (Fin 1) (hashEncoding K).target)
    (hmembership : triple ∈ (hashEncoding K).legalTargets 0
      (Finset.univ : Finset
        (PositiveWord (oneBlockPartition K).symThreePartition.support 0))) :
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      ((hashEncoding K).legalTargets 0
        (Finset.univ : Finset
          (PositiveWord (oneBlockPartition K).symThreePartition.support 0)))
      triple).card ≤ Fintype.card (ZMod 13) := by
  classical
  have huniv :
      (Finset.univ : Finset
          (PositiveWord (oneBlockPartition K).symThreePartition.support 0)) =
          {cyclicWord K} :=
    univ_positiveWords_eq_singleton (cyclicWord K)
  have htargets :
      (hashEncoding K).legalTargets 0
          (Finset.univ : Finset
            (PositiveWord (oneBlockPartition K).symThreePartition.support 0)) =
        {(hashEncoding K).legalTriple 0 (cyclicWord K)} := by
    rw [huniv]
    simp [PartitionHashEncoding.legalTargets]
  have htriple : triple = (hashEncoding K).legalTriple 0 (cyclicWord K) := by
    simpa [htargets] using hmembership
  subst triple
  simp [htargets, ProgressionHash.LegalTriple.legwiseCompetitorYIndices,
    ProgressionHash.LegalTriple.legCompetitors]

/-- The one-hash cyclic-row API has a genuinely nonempty concrete instance. -/
theorem exists_tinyRawCyclicRow_nonempty [Nontrivial K] :
    ∃ seed : ProgressionHash.Seed (ZMod 13) (Fin 1),
      Nonempty ((hashEncoding K).markedLegwiseIsolatedPowerAddresses 0
        (Finset.univ : Finset
          (PositiveWord (oneBlockPartition K).symThreePartition.support 0))
        Finset.univ {0} seed) ∧
      Restricts
        (((oneBlockPartition K).symThreePartition.positivePower 0).realize)
        (Tensor.indexedDirectSum
          (fun _selected : (hashEncoding K).markedLegwiseIsolatedPowerAddresses 0
            (Finset.univ : Finset
              (PositiveWord (oneBlockPartition K).symThreePartition.support 0))
            Finset.univ {0} seed ↦
            symThree K
              (((oneBlockPartition K).positivePower 0).constituent
                (positiveSupportWordBlockAddress
                  (oneBlockPartition K).support 0 (primitiveWord K))))) := by
  classical
  let H := hashEncoding K
  let words : Finset
      (PositiveWord (oneBlockPartition K).symThreePartition.support 0) := Finset.univ
  let buckets : Finset (ZMod 13) := {0}
  have hthreeAP : ThreeAPFree (buckets : Set (ZMod 13)) :=
    Set.Subsingleton.threeAPFree (by simp [buckets])
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    H.exists_seed_many_markedLegwiseIsolatedPowerAddresses
      0 words words Finset.Subset.rfl buckets hthreeAP (competitor_quarter K)
  let selected := H.markedLegwiseIsolatedPowerAddresses 0 words words buckets seed
  have hwords : words.Nonempty := by
    exact ⟨cyclicWord K, Finset.mem_univ _⟩
  have hbuckets : buckets.Nonempty := by simp [buckets]
  have hselected : 0 < selected.card := by
    by_contra hzero
    have hcard : selected.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hcard] at hcount
    have hleft : 0 < 3 * words.card * buckets.card := by
      exact mul_pos (mul_pos (by norm_num) (Finset.card_pos.mpr hwords))
        (Finset.card_pos.mpr hbuckets)
    omega
  refine ⟨seed, (Finset.card_pos.mp hselected).to_subtype, ?_⟩
  simpa only [H, words, buckets] using
    (Tensor.Restricts.rawCyclicRow_to_symThreeChildDirectSum
      H 0 1 (primitiveProfile K) (primitiveWord K)
      (primitive_reference_type K) words words Finset.Subset.rfl
      (by intro word _hword; exact cyclic_word_type K word)
      ((oneBlockPartition K).symThreePartition.positivePower 0)
      (H.positivePower_support_eq_modeledLegalTargets
        (oneBlockPartition K).symThreePartition 0)
      (fun _address ↦ rfl) buckets hthreeAP seed)

end AlgebraicComplexity.Examples.RawCyclicRowExtractionTiny
