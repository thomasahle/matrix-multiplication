/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageLeaf
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The section 6.3 stage on the reachable ambient

The four steps, all now hypothesis-free except `hclaim3`:

`plain power → dwz63PreimageFine` (`dwz63_power_restricts_preimageFine`), the grouped direct sum
(`dwz63_preimageFine_restricts_groupedDirectSum`, needing only the hash's two `InjOn`
certificates), the per-fibre leaf step (`dwz63_preimageFiber_restricts_brokenReferenceLeaf`), and
the batched Hole Lemma.

`hfine`, `hcover`, `hambient`, `hholes`, `usefulFor` and `compatibleWith` are all gone; the hole
family is `dwz63ReferenceHoles`, *defined* by the isolation rather than supplied.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The stage, from a reachability hypothesis on the ambient.** -/
theorem dwz63_preimageStage_of_claim3 (K : Type u) [CommRing K] (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (perm : retained → Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : retained,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (hpower : Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (dwz63PreimageFine K n retained).realize)
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : retained → β) (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a : retained // batch a = b},
            (dwz63ReferenceHoles K retained a₀ alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a : retained // batch a = b}) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) := by
  classical
  refine ((hpower.trans
    (dwz63_preimageFine_restricts_groupedDirectSum K a₀ hX hY)).trans
    (Tensor.Restricts.indexedDirectSum fun a ↦
      dwz63_preimageFiber_restricts_brokenReferenceLeaf K a₀ hX hY alphaTilde wRef
        perm hperm a)).trans ?_
  simp only [dwz63ReferenceLeaf, dwz63BrokenFineLeaf, dwz63SegmentedFineFiber]
  exact restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n 15
    (dwz63Seg K n wRef) alphaTilde hclaim3
    (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
    (fun σ hperm' ↦ dwz63_positionRelabel_target_eq K n σ wRef hperm')
    batch hbatch (fun a ↦ dwz63ReferenceHoles K retained a₀ alphaTilde wRef perm a) hbudget

/-! ## At the hashing family -/

section Hash

variable {R : Type v} [Field R]

/-- **The section 6.3 plain stage, with `hclaim3` the only mathematical hypothesis.**

The retained family is the hash's; `hX`, `hY` and the reachability of the ambient are all
discharged inside. -/
theorem dwz63_plainPreimageStage_of_claim3 [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (perm : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b},
            (dwz63ReferenceHoles K _ a₀ alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) :=
  dwz63_preimageStage_of_claim3 K a₀
    (dwz63_x_injOn_plainJointRetained K hinj n t markedWords hmarked B hB seed)
    ((cwSquarePartitionHashEncoding hinj).y_injectiveOn_markedXYIsolatedPowerAddresses
      n (dwz63PlainMarginalWords K n t) markedWords hmarked B hB seed)
    alphaTilde wRef hclaim3 perm hperm
    (dwz63_power_restricts_preimageFine K hinj n t markedWords hmarked B hB seed)
    batch hbatch hbudget

/-- **The six-orientation form**, which is what the batched endpoint consumes. -/
theorem dwz63_plainPreimageSymSixStage_of_claim3 [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (perm : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b},
            (dwz63ReferenceHoles K _ a₀ alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : ((β × β) × β) × ((β × β) × β) ↦
          symSix K (dwz63ReferenceLeaf K n alphaTilde wRef).realize)) :=
  restricts_power_symSix_of_plainStage n
    (dwz63_plainPreimageStage_of_claim3 K hinj n t markedWords hmarked B hB seed a₀
      alphaTilde wRef hclaim3 perm hperm batch hbatch hbudget)

end Hash

end

end AlgebraicComplexity.Examples
