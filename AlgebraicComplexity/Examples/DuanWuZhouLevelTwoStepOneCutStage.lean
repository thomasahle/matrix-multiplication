/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeaf
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLocalizedStage
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair

set_option autoImplicit false

/-!
# The section 6.3 stage, over `𝒯^{(1)}`

Layer 4 (`AlgebraicComplexity/Examples/`).  The four steps of the section 6.3 degeneration, now all
performed after Additional Zeroing-Out **Step 1**:

1. the plain power reaches the reachable fine ambient (`dwz63_power_restricts_preimageFine`,
   image 74);
2. Step 1 cuts it, for free, to `𝒯^{(1)}` (`dwz63_restricts_preimageFine_stepOne`, image 143,
   `[duan2023faster]` `papers/sources/2210.10173/global_value.tex:52-61, 72`);
3. Step 2 splits `𝒯^{(2)}` into one broken copy per retained triple
   (`dwz63_stepOneCut_restricts_groupedDirectSum`, image 149, `:84-89`), and each copy reaches the
   one broken standard-form leaf (`dwz63_cutFiber_restricts_brokenReferenceLeaf`, image 151,
   `:98-102`);
4. the holes are repaired in batches.

Step 4 is the paper's own Step 4 (`:104`, "Fix the holes and degenerate each triple
independently") and it consumes `cor:hole_lemma`
(`papers/sources/2210.10173/hole_lemma.tex:159-168`):

> Assume that we have `s` broken copies of `𝒯^*` named `𝒯'_1, …, 𝒯'_s`, with fractions of
>  non-holes `η_1, …, η_s`.  Then there is a way of degenerating them into `s'` complete copies
> of
> `𝒯^*` …  (`hole_lemma.tex:161-165`)

`:102` is where the paper licenses that use: "`𝒯^*` exactly matches `def:standard_form_tensor`
…
This will allow us to apply the hole lemma".  In Lean the corollary is the parametric engine
`restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched`
(`MatrixMultiplication/SegmentedLocalizedHoleRepair.lean:254`), whose hole family is a bare
parameter; here it is instantiated at image 145's `dwz63CutReferenceHoles`, whose budget image 147
bounds.

This is the R1 re-issue of `Examples/DuanWuZhouLevelTwoPreimageStage.lean` (image 113), which runs
the same four steps on the **uncut** ambient; that module is superseded and is neither edited nor
imported here.  The one new binder is `hS`, which pins `alphaTilde` to the section 6.3 split table
so that the leaf's own blocks are known to survive Step 1 (N4, image 151).

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:52-61, 72, 84-89, 98-104`, with
`hole_lemma.tex:159-168`, at the section 6.3 instance (`global_value.tex:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The section 6.3 stage over `𝒯^{(1)}`, conditional on Claim 3.**

`hclaim3` is Claim 3 of the Hole Lemma (`hole_lemma.tex:111-121`) in its segmented form; `hbudget`
is `cor:hole_lemma`'s non-hole-fraction condition (`hole_lemma.tex:161-165`) at the batch `b`, over
the hole family of `𝒯^{(1)}`.

Proof sketch: compose steps 1-3 (images 74, 143, 149, 151) and finish with the batched hole-repair
engine, exactly as image 113 does on the uncut ambient. -/
theorem dwz63_cutStage_of_claim3 (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _))
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
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
            (dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a : retained // batch a = b}) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) := by
  classical
  refine (((hpower.trans
    (dwz63_restricts_preimageFine_stepOne K n retained a₀ s)).trans
    (dwz63_stepOneCut_restricts_groupedDirectSum K a₀ s hX hY)).trans
    (Tensor.Restricts.indexedDirectSum fun a ↦
      dwz63_cutFiber_restricts_brokenReferenceLeaf K a₀ s hX hY hS wRef perm hperm a)).trans ?_
  simp only [dwz63ReferenceLeaf, dwz63BrokenFineLeaf, dwz63SegmentedFineFiber]
  exact restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n 15
    (dwz63Seg K n wRef) alphaTilde hclaim3
    (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
    (fun σ hperm' ↦ dwz63_positionRelabel_target_eq K n σ wRef hperm')
    batch hbatch
    (fun a ↦ dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a) hbudget

/-! ## At the hashing family -/

section Hash

variable {R : Type v} [Field R]

/-- **The section 6.3 plain stage over `𝒯^{(1)}`**, with `hclaim3` the only mathematical
hypothesis.  The retained family is the hash's; `hX`, `hY` and the reachability of the ambient are
all discharged inside. -/
theorem dwz63_plainCutStage_of_claim3 [NeZero (2 : R)]
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
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) :=
  dwz63_cutStage_of_claim3 K a₀ s
    (dwz63_x_injOn_plainJointRetained K hinj n t markedWords hmarked B hB seed)
    ((cwSquarePartitionHashEncoding hinj).y_injectiveOn_markedXYIsolatedPowerAddresses
      n (dwz63PlainMarginalWords K n t) markedWords hmarked B hB seed)
    hS wRef hclaim3 perm hperm
    (dwz63_power_restricts_preimageFine K hinj n t markedWords hmarked B hB seed)
    batch hbatch hbudget

end Hash

end

end AlgebraicComplexity.Examples
