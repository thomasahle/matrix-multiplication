/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentedBreaking
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainGroupedStage
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The section 6.3 plain stage, on the localized leaf

`dwz63_plainStage_of_segmentedRepair` asks each retained constituent to restrict onto the *global*
segmented power; no retained constituent can, so its `hleaf` premise is undischargeable.  This
module is the repoint: the leaf is the localized fine fiber over **one reference coarse word**, and
every retained constituent reaches it --- through its own fiber, then the uniformity isomorphism,
then the hashing damage.

Only `hclaim3` is a mathematical hypothesis.  Everything else is bookkeeping about the retained
set: which supported coarse word each retained address comes from (`hword`, `hsupport`) and that
they all have the same type as the reference word (`hsame`).

`[DuanWuZhou2022]`, section 6.3, `hole_lemma.tex`, `global_value.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

noncomputable section

variable {R : Type v} [Field R]

/-- **Every retained address is an address of the coarse positive power.**

The hashing family only ever emits addresses of marked source words
(`exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses`), and every supported joint word
transposes to a supported address.  This is what made `hsupport` a hypothesis rather than a fact;
it is a fact. -/
theorem dwz63_plainJointRetained_mem_positivePowerSupport
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) :
    (a.1 : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support := by
  classical
  obtain ⟨word, _hword, hwordAddress⟩ :=
    (cwSquarePartitionHashEncoding hinj).exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses
      n (dwz63PlainMarginalWords K n t) markedWords B seed a.2
  rw [← hwordAddress,
    PartitionedTensor.positivePower_support_eq_image_positiveSupportWordBlockAddress]
  exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩

/-- **The one common leaf**: the localized segmented fine fiber over a reference coarse word. -/
noncomputable def dwz63ReferenceLeaf (K : Type u) [CommRing K] (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :=
  dwz63SegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)

/-- **Every retained constituent reaches the one reference leaf.**

Its own fiber by `dwz63_hleaf_segmentedFineFiber`, then the uniformity isomorphism of
`dwz63_segmentedFineFiber_isomorphic_position`, then the hashing damage.  The hole set is
arbitrary, so this is a theorem rather than a premise. -/
theorem dwz63_constituent_restricts_brokenReferenceLeaf
    (K : Type u) [CommRing K] (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : positiveWordPositionEquiv
      ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef = w)
    (htarget : positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n w ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support)
    (holes : Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde)) :
    Restricts
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).constituent
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support) n w))
      (dwz63BrokenSegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) holes).realize := by
  subst hσ
  refine (dwz63_hleaf_segmentedFineFiber K n 15
    (dwz63Seg K n (positiveWordPositionEquiv
      ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef))
    alphaTilde
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n
      (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef)) htarget).trans ?_
  refine (Tensor.Isomorphic.restricts
    (dwz63_segmentedFineFiber_isomorphic_position K n alphaTilde wRef σ).symm).trans ?_
  exact dwz63_breaking_segmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) holes

/-- **The section 6.3 plain stage on the localized leaf, without legwise injectivity.**

The re-issue of `dwz63_localizedStage_of_segmentedRepair` onto image 57's grouped opening.
`dwz63_plainRetainedDirectSum` and its false `hlegwise` are gone; the hash now enters only where it
defines the retained family and certifies the two `InjOn` facts, which are supplied here from
`dwz63_x_injOn_plainJointRetained` and `y_injectiveOn_markedXYIsolatedPowerAddresses` rather than
being carried. -/
theorem dwz63_localizedGroupedStage_of_segmentedRepair [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (fine : PartitionedTensor (K := K)
      (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      (PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
    (hfine : Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      fine.realize)
    (a₀ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    (hcover : ∀ s ∈ fine.support,
      ∃ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
        ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
          positiveWordMap (cwSquareDegreeMap c) n (s c))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n →
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → Prop}
    (holes : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde))
    (hholes : ∀ (a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
        (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ (holes a).image Subtype.val →
        usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hambient : ∀ s ∈ fine.support,
      s .Z ∉ (holes (dwz63PlainCoarseGroup
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ s)).image Subtype.val)
    (hleaf : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      Restricts
        (dwz63PlainBrokenGroup fine (dwz63PlainCoarseGroup
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) usefulFor a).realize
        (dwz63BrokenSegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) (holes a)).realize)
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) := by
  classical
  refine (dwz63_plainGroupedStage_of_brokenLeaf fine hfine
    (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀
    (dwz63_x_injOn_plainJointRetained K hinj n t markedWords hmarked B hB seed)
    ((cwSquarePartitionHashEncoding hinj).y_injectiveOn_markedXYIsolatedPowerAddresses
      n (dwz63PlainMarginalWords K n t) markedWords hmarked B hB seed)
    hcover (compatibleWith := compatibleWith) hholes hambient
    (fun a ↦ dwz63BrokenSegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) (holes a))
    hleaf).trans ?_
  simp only [dwz63ReferenceLeaf, dwz63BrokenSegmentedFineFiber, dwz63SegmentedFineFiber]
  exact restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n 15
    (dwz63Seg K n wRef) alphaTilde hclaim3
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
    (fun σ hperm ↦ dwz63_positionRelabel_target_eq K n σ wRef hperm)
    batch hbatch holes hbudget

/-- **`hstage` in the six-orientation shape**, for `DwzLevelTwoCountingStage`.

The plain grouped stage is what `omega_lt_2374631_of_plainStageAndLeaf` consumes directly; this is
the `symSix` form for the counting-stage consumer, with copy count `|β|^6`. -/
theorem dwz63_localizedGroupedSymSixStage_of_segmentedRepair [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (fine : PartitionedTensor (K := K)
      (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      (PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
    (hfine : Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      fine.realize)
    (a₀ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    (hcover : ∀ s ∈ fine.support,
      ∃ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
        ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
          positiveWordMap (cwSquareDegreeMap c) n (s c))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n →
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → Prop}
    (holes : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde))
    (hholes : ∀ (a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
        (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ (holes a).image Subtype.val →
        usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hambient : ∀ s ∈ fine.support,
      s .Z ∉ (holes (dwz63PlainCoarseGroup
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ s)).image Subtype.val)
    (hleaf : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      Restricts
        (dwz63PlainBrokenGroup fine (dwz63PlainCoarseGroup
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) usefulFor a).realize
        (dwz63BrokenSegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) (holes a)).realize)
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : ((β × β) × β) × ((β × β) × β) ↦
          symSix K (dwz63ReferenceLeaf K n alphaTilde wRef).realize)) :=
  restricts_power_symSix_of_plainStage n
    (dwz63_localizedGroupedStage_of_segmentedRepair K hinj n t markedWords hmarked B hB seed
      alphaTilde wRef hclaim3 fine hfine a₀ hcover (compatibleWith := compatibleWith)
      holes hholes hambient hleaf batch hbatch hbudget)

end

end AlgebraicComplexity.Examples
