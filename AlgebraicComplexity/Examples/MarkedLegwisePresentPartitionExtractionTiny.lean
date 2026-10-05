/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedLegwisePresentPartitionExtraction
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Tiny strict-support client for present marked all-leg extraction

This file is a nonvacuity regression for Corollary
`cor:present-marked-all-leg-extraction` of the Total-Weight manuscript,
`better_bound/paper.tex:764-796`.

At depth zero, take the two diagonal Boolean addresses `000` and `111`.  Over `ZMod 3`, encoding
`false` by zero and `true` by one makes both addresses legal with target zero.  For the zero affine
seed and bucket `{0}`, both one-letter words survive, and they share no block on any tensor leg;
therefore both are marked all-leg-isolated.  The actual partition contains only the `000` address.
Thus the present and missing parts are both nonempty, while the generic theorem constructs the
restriction to the indexed direct sum of the one genuinely present constituent.

The proof uses only symbolic reasoning over two-element finite sets.  No finite exhaustive
reduction is used.
-/

namespace AlgebraicComplexity.Examples.MarkedLegwisePresentPartitionExtractionTiny

open AlgebraicComplexity Tensor

local instance twoNeZero : NeZero (2 : ZMod 3) := ⟨by decide⟩

private abbrev Label (_ : Leg) := Bool

private def lowAddress : BlockAddress Label := fun _ ↦ false

private def highAddress : BlockAddress Label := fun _ ↦ true

private def baseSupport : Finset (BlockAddress Label) :=
  {lowAddress, highAddress}

private def lowSupport : baseSupport :=
  ⟨lowAddress, by simp [baseSupport]⟩

private def highSupport : baseSupport :=
  ⟨highAddress, by simp [baseSupport]⟩

private def lowWord : PositiveWord baseSupport 0 := lowSupport

private def highWord : PositiveWord baseSupport 0 := highSupport

private def bothWords : Finset (PositiveWord baseSupport 0) :=
  {lowWord, highWord}

private def bitCode : Bool → ZMod 3
  | false => 0
  | true => 1

private def tinyEncoding :
    PartitionHashEncoding (R := ZMod 3) baseSupport where
  encode := fun _ bit ↦ bitCode bit
  target := 0
  support_nonempty := ⟨lowAddress, by simp [baseSupport]⟩
  encode_injective := by
    intro _ left right h
    cases left <;> cases right
    · rfl
    · norm_num [bitCode] at h
    · norm_num [bitCode] at h
    · rfl
  legal := by
    intro address haddress
    simp only [baseSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
    rcases haddress with haddress | haddress
    · subst address
      norm_num [lowAddress, bitCode]
    · subst address
      change (1 : ZMod 3) + 1 + 1 = 0
      calc
        (1 : ZMod 3) + 1 + 1 = (3 : ZMod 3) := by norm_num
        _ = 0 := ZMod.natCast_self 3

private def zeroSeed : ProgressionHash.Seed (ZMod 3) (Fin 1) where
  offset := 0
  shift := 0
  weights := fun _ ↦ 0

private def lowPowerAddress :
    BlockAddress (fun c ↦ PositiveWord (Label c) 0) :=
  PartitionHashEncoding.supportWordAddress 0 lowWord

private def highPowerAddress :
    BlockAddress (fun c ↦ PositiveWord (Label c) 0) :=
  PartitionHashEncoding.supportWordAddress 0 highWord

private noncomputable def actualPartition :
    PartitionedTensor (K := ZMod 3)
      (A := fun c ↦ PositiveWord (Label c) 0)
      (fun _ _ ↦ ZMod 3) where
  support := {lowPowerAddress}
  constituent := fun _ ↦ pure (K := ZMod 3) (fun _ ↦ 1)

private theorem lowAddress_ne_highAddress : lowAddress ≠ highAddress := by
  intro h
  have hx := congrFun h .X
  simp [lowAddress, highAddress] at hx

private theorem lowWord_ne_highWord : lowWord ≠ highWord := by
  intro h
  apply lowAddress_ne_highAddress
  exact congrArg Subtype.val h

private theorem lowPowerAddress_ne_highPowerAddress :
    lowPowerAddress ≠ highPowerAddress := by
  intro h
  apply lowWord_ne_highWord
  exact PartitionHashEncoding.supportWordAddress_injective
    (A := Label) (support := baseSupport) 0 h

private theorem low_high_do_not_share :
    ¬ ProgressionHash.LegalTriple.SharesLeg
      (tinyEncoding.legalTriple 0 lowWord)
      (tinyEncoding.legalTriple 0 highWord) := by
  rintro ⟨leg, hleg⟩
  have hblock :=
    (tinyEncoding.legalTriple_legIndex_eq_iff 0 lowWord highWord leg).mp hleg
  simp [PartitionHashEncoding.supportWordAddress,
    positiveSupportWordBlockAddress, lowWord, highWord, lowSupport, highSupport,
    lowAddress, highAddress] at hblock

private theorem low_legCompetitors_eq_empty :
    ProgressionHash.LegalTriple.legCompetitors
      (tinyEncoding.legalTargets 0 bothWords)
      (tinyEncoding.legalTriple 0 lowWord) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro other hother
  obtain ⟨herase, hshare⟩ := Finset.mem_filter.mp hother
  obtain ⟨hne, htarget⟩ := Finset.mem_erase.mp herase
  unfold PartitionHashEncoding.legalTargets at htarget
  obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp htarget
  simp only [bothWords, Finset.mem_insert, Finset.mem_singleton] at hword
  rcases hword with hword | hword
  · subst word
    exact hne rfl
  · subst word
    exact low_high_do_not_share hshare

private theorem high_legCompetitors_eq_empty :
    ProgressionHash.LegalTriple.legCompetitors
      (tinyEncoding.legalTargets 0 bothWords)
      (tinyEncoding.legalTriple 0 highWord) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro other hother
  obtain ⟨herase, hshare⟩ := Finset.mem_filter.mp hother
  obtain ⟨hne, htarget⟩ := Finset.mem_erase.mp herase
  unfold PartitionHashEncoding.legalTargets at htarget
  obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp htarget
  simp only [bothWords, Finset.mem_insert, Finset.mem_singleton] at hword
  rcases hword with hword | hword
  · subst word
    apply low_high_do_not_share
    obtain ⟨leg, hleg⟩ := hshare
    exact ⟨leg, hleg.symm⟩
  · subst word
    exact hne rfl

private theorem competitorIndices_eq_empty
    (word : PositiveWord baseSupport 0) (hword : word ∈ bothWords) :
    ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (tinyEncoding.legalTargets 0 bothWords)
      (tinyEncoding.legalTriple 0 word) = ∅ := by
  classical
  simp only [bothWords, Finset.mem_insert, Finset.mem_singleton] at hword
  rcases hword with hword | hword
  · subst word
    simp [ProgressionHash.LegalTriple.legwiseCompetitorYIndices,
      low_legCompetitors_eq_empty]
  · subst word
    simp [ProgressionHash.LegalTriple.legwiseCompetitorYIndices,
      high_legCompetitors_eq_empty]

private theorem zeroSeed_commonBucket (word : PositiveWord baseSupport 0) :
    ProgressionHash.Seed.InCommonBucket
      (tinyEncoding.legalTriple 0 word).xIndex
      (tinyEncoding.legalTriple 0 word).yIndex 0 zeroSeed := by
  constructor <;>
    simp [ProgressionHash.Seed.xHash, ProgressionHash.Seed.yHash,
      ProgressionHash.hashX, ProgressionHash.hashY, ProgressionHash.linear, zeroSeed]

private theorem isolatedTarget_of_mem
    (word : PositiveWord baseSupport 0) (hword : word ∈ bothWords) :
    tinyEncoding.legalTriple 0 word ∈
      ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets
        (tinyEncoding.legalTargets 0 bothWords)
        (tinyEncoding.legalTargets 0 bothWords) {0} zeroSeed := by
  classical
  unfold ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets
    ProgressionHash.Seed.isolatedTargets
  apply Finset.mem_image.mpr
  refine ⟨(tinyEncoding.legalTriple 0 word, (0 : ZMod 3)), ?_, rfl⟩
  unfold ProgressionHash.Seed.isolatedIncidences
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, by simp⟩, ?_⟩
  · unfold PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨word, hword, rfl⟩
  · change zeroSeed ∈ ProgressionHash.Seed.isolatedSeeds
      (tinyEncoding.legalTriple 0 word).xIndex
      (tinyEncoding.legalTriple 0 word).yIndex
      (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (tinyEncoding.legalTargets 0 bothWords)
        (tinyEncoding.legalTriple 0 word)) 0
    rw [competitorIndices_eq_empty word hword]
    simpa [ProgressionHash.Seed.isolatedSeeds] using zeroSeed_commonBucket word

private theorem selectedAddress_of_mem
    (word : PositiveWord baseSupport 0) (hword : word ∈ bothWords) :
    PartitionHashEncoding.supportWordAddress 0 word ∈
      tinyEncoding.markedLegwiseIsolatedPowerAddresses
        0 bothWords bothWords {0} zeroSeed := by
  classical
  unfold PartitionHashEncoding.markedLegwiseIsolatedPowerAddresses
    PartitionHashEncoding.modeledAddresses
  exact Finset.mem_image.mpr
    ⟨tinyEncoding.legalTriple 0 word, isolatedTarget_of_mem word hword,
      tinyEncoding.modeledAddress_legalTriple 0 word⟩

private theorem actualSupport_subset_modeled :
    actualPartition.support ⊆
      tinyEncoding.modeledAddresses 0 (tinyEncoding.legalTargets 0 bothWords) := by
  classical
  intro address haddress
  have haddress' : address = lowPowerAddress := by
    simpa [actualPartition] using haddress
  subst address
  rw [tinyEncoding.modeledAddresses_legalTargets_eq_image]
  exact Finset.mem_image.mpr ⟨lowWord, by simp [bothWords], rfl⟩

private theorem low_mem_present :
    lowPowerAddress ∈ tinyEncoding.presentMarkedLegwiseIsolatedPowerAddresses
      bothWords bothWords {0} zeroSeed actualPartition := by
  classical
  apply Finset.mem_inter.mpr
  refine ⟨by simp [actualPartition], ?_⟩
  exact selectedAddress_of_mem lowWord (by simp [bothWords])

private theorem high_mem_missing :
    highPowerAddress ∈ tinyEncoding.missingMarkedLegwiseIsolatedPowerAddresses
      bothWords bothWords {0} zeroSeed actualPartition := by
  classical
  apply Finset.mem_sdiff.mpr
  refine ⟨selectedAddress_of_mem highWord (by simp [bothWords]), ?_⟩
  simpa [actualPartition] using lowPowerAddress_ne_highPowerAddress.symm

/-- The strict-support interface is jointly satisfiable: one isolated abstract target is present,
one is missing, and the actual partition restricts to the direct sum indexed by its present
targets.

**Proof sketch.** The preceding finite calculation places both diagonal words in the abstract
isolated family.  Intersecting with the singleton actual support retains only the low word.  Apply
the generic present-support all-leg extraction theorem to that concrete partition. -/
theorem strict_support_extraction_nonvacuous :
    Nonempty (tinyEncoding.presentMarkedLegwiseIsolatedPowerAddresses
      bothWords bothWords {0} zeroSeed actualPartition) ∧
    Nonempty (tinyEncoding.missingMarkedLegwiseIsolatedPowerAddresses
      bothWords bothWords {0} zeroSeed actualPartition) ∧
    Restricts actualPartition.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := fun (_ : Leg) (_ : PositiveWord Bool 0) ↦ ZMod 3)
          (tinyEncoding.presentMarkedLegwiseIsolatedPowerAddresses
            bothWords bothWords {0} zeroSeed actualPartition))
        (fun selected : tinyEncoding.presentMarkedLegwiseIsolatedPowerAddresses
            bothWords bothWords {0} zeroSeed actualPartition ↦
          actualPartition.constituent selected.1)) := by
  classical
  refine ⟨⟨⟨lowPowerAddress, low_mem_present⟩⟩,
    ⟨⟨highPowerAddress, high_mem_missing⟩⟩, ?_⟩
  exact Tensor.Restricts.presentModeledTargets_to_presentMarkedLegwiseIsolatedIndexedDirectSum
    tinyEncoding bothWords bothWords Finset.Subset.rfl {0}
      (Set.Subsingleton.threeAPFree (by simp)) zeroSeed actualPartition
      actualSupport_subset_modeled

end AlgebraicComplexity.Examples.MarkedLegwisePresentPartitionExtractionTiny
