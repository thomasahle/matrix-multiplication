/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutStage
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberIndependenceProof
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The six-orientation section 6.3 stage over `𝒯^{(1)}`, unconditionally

Layer 4 (`AlgebraicComplexity/Examples/`).  Two wrappers on `dwz63_plainCutStage_of_claim3`
(`Examples/DuanWuZhouLevelTwoStepOneCutStage.lean`):

* `dwz63_plainCutSymSixStage_of_claim3` puts it in the six-orientation form the batched endpoint
  consumes.  Symmetrisation is the paper's Step 4/5 packaging of section 6.1 (`:104-121`); the
  Lean bridge is `restricts_power_symSix_of_plainStage`
  (`MatrixMultiplication/SymSixUniformLeaf.lean`).
* `dwz63_plainCutSymSixStage` discharges the one remaining mathematical hypothesis.  `hclaim3` is
  Claim 3 of `[duan2023faster]`'s Hole Lemma (`papers/sources/2210.10173/hole_lemma.tex:111-121`)
  in its segmented form, and `segmentedFiberIndependence`
  (`MatrixMultiplication/SegmentedFiberIndependenceProof.lean`) proves that statement for every
  segmentation and every per-segment type; every other binder is identical in name, order and type.

This is the R1 re-issue of `Examples/DuanWuZhouLevelTwoPreimageStage.lean:134` and
`Examples/DuanWuZhouLevelTwoPreimageStageUnconditional.lean:48` (images 113), which run the same
wrappers on the **uncut** ambient; those modules are superseded and are neither edited nor imported
here.  The single added binder is `hS`.

The output is exactly the shape image 131's `dwz63_exists_seed_stage_marked` returns as its first
conjunct, with `dwz63CutReferenceHoles` in place of the uncut hole family.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121`, with `hole_lemma.tex:111-121, 159-168`, at the
section 6.3 instance (`global_value.tex:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

section Hash

variable {R : Type v} [Field R]

/-- **The six-orientation form** of the section 6.3 stage over `𝒯^{(1)}`, which is what the
batched
endpoint consumes. -/
theorem dwz63_plainCutSymSixStage_of_claim3 [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (n t s : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (perm : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b},
            (dwz63CutReferenceHoles K _ a₀ s alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : ((β × β) × β) × ((β × β) × β) ↦
          symSix K (dwz63ReferenceLeaf K n alphaTilde wRef).realize)) :=
  restricts_power_symSix_of_plainStage n
    (dwz63_plainCutStage_of_claim3 K hinj n t s markedWords hmarked B hB seed a₀ hS
      wRef hclaim3 perm hperm batch hbatch hbudget)

/-- **The section 6.3 six-orientation stage over `𝒯^{(1)}`, with no mathematical hypothesis
left.**

`dwz63_plainCutSymSixStage_of_claim3` with `hclaim3` discharged by `segmentedFiberIndependence`
(Claim 3 of the Hole Lemma, `hole_lemma.tex:111-121`).  Every other binder is unchanged. -/
theorem dwz63_plainCutSymSixStage [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (n t s : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : dwz63PlainJointRetainedSupport K hinj n t markedWords B seed → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b},
            (dwz63CutReferenceHoles K _ a₀ s alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : ((β × β) × β) × ((β × β) × β) ↦
          symSix K (dwz63ReferenceLeaf K n alphaTilde wRef).realize)) :=
  dwz63_plainCutSymSixStage_of_claim3 K hinj n t s markedWords hmarked B hB seed a₀ hS wRef
    (segmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde) perm hperm batch hbatch hbudget

end Hash

end

end AlgebraicComplexity.Examples
