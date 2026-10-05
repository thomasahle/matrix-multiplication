/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepairGeneral
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberUniformity

set_option autoImplicit false

/-!
# The segmented Hole Lemma on a localized leaf

`MatrixMultiplication/SegmentedHoleRepair.lean` proves the segmented Hole Lemma for the *global*
segmented restricted-splitting power `(P.positivePower n).select (profile.Keeps n seg)`.  A
retained constituent of a coarsened power contains only fine words over its own coarse target, so
it does not restrict onto that global object; the leaf the campaign can actually reach is the
**localized** one, cut down to a single coarse fiber.  This module reproves the Hole Lemma there.

Nothing in the counting changes.  The three ingredients are:

* the leaf is still a single `select` of the ambient positive power, with the fiber condition
  folded into the keep predicate (`coarseningFiber_select_eq_select`), so
  `StructureRelabeling.select` still builds the shuffles;
* Claim 2 needs one extra premise --- the permutation must fix the coarse target --- and gets it
  from `positiveWordMap_position_symm_eq_iff`.  In the `[DuanWuZhou2022]` application that premise
  is *free*: `dwz63_positionRelabel_target_eq` derives it from segment preservation, because the
  segmentation determines the coarse word;
* Claim 1, `SegmentedFiberIndependence` and the budget are untouched.  The localized leaf's
  `Z`-words are a subset of `SegmentedAvailableWord seg α`, so the same budget on the full
  available set remains sufficient.

`[DuanWuZhou2022]`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w x

/-! ## A fiber followed by a selection is a single selection -/

section FiberSelect

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Localizing to one coarse fiber and then selecting is the same as selecting once, with the
fiber condition conjoined legwise onto the keep predicate. -/
theorem Tensor.PartitionedTensor.coarseningFiber_select_eq_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    (P.coarseningFiber f target).select keep =
      P.select (fun c a ↦ f c a = target c ∧ keep c a) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.mem_select_support,
      PartitionedTensor.coarseningFiber_support,
      PartitionedTensor.mem_coarseningFiberSupport]
    constructor
    · rintro ⟨⟨hsource, hmap⟩, hkeep⟩
      exact ⟨hsource, fun c ↦ ⟨congrFun hmap c, hkeep c⟩⟩
    · rintro ⟨hsource, hparts⟩
      exact ⟨⟨hsource, funext fun c ↦ (hparts c).1⟩, fun c ↦ (hparts c).2⟩
  · rfl

end FiberSelect

/-! ## The localized segmented leaf -/

section LocalizedLeaf

variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, DecidableEq (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {n m : ℕ}

/-- The keep predicate of the localized segmented leaf: a fine word is retained when it lies over
the fixed coarse target *and* has the prescribed segment types. -/
def segmentedLocalizedKeep (f : ∀ c, A c → B c) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    ∀ c, PositiveWord (A c) n → Prop :=
  fun c word ↦ positiveWordMap (f c) n word = target c ∧ profile.Keeps n seg c word

noncomputable instance segmentedLocalizedKeepDecidable (f : ∀ c, A c → B c)
    (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (c : Leg) (word : PositiveWord (A c) n) :
    Decidable (segmentedLocalizedKeep f seg profile target c word) :=
  Classical.dec _

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem segmentedLocalizedKeep_iff (f : ∀ c, A c → B c)
    (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (c : Leg) (word : PositiveWord (A c) n) :
    segmentedLocalizedKeep f seg profile target c word ↔
      positiveWordMap (f c) n word = target c ∧ profile.Keeps n seg c word := Iff.rfl

end LocalizedLeaf

section LocalizedPower

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {n m : ℕ}

/-- **The localized segmented restricted-splitting power.**  `[DuanWuZhou2022]`'s `T*` cut down to
the fine words lying over one retained coarse address. -/
noncomputable def Tensor.PartitionedTensor.segmentedLocalizedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) :=
  (P.positivePower n).select (segmentedLocalizedKeep f seg profile target)

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem Tensor.PartitionedTensor.mem_segmentedLocalizedSplittingPower_support
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    address ∈ (P.segmentedLocalizedSplittingPower f n m seg profile target).support ↔
      address ∈ (P.positivePower n).support ∧
        ∀ c, positiveWordMap (f c) n (address c) = target c ∧
          profile.Keeps n seg c (address c) := by
  simp only [PartitionedTensor.segmentedLocalizedSplittingPower,
    PartitionedTensor.mem_select_support, segmentedLocalizedKeep]

/-- The localized leaf really is the fine fiber over the target, selected. -/
theorem Tensor.PartitionedTensor.coarseningFiber_select_eq_segmentedLocalizedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    ((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n) target).select (profile.Keeps n seg) =
      P.segmentedLocalizedSplittingPower f n m seg profile target := by
  classical
  apply PartitionedTensor.ext
  · ext address
    rw [PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_segmentedLocalizedSplittingPower_support,
      PartitionedTensor.coarseningFiber_support,
      PartitionedTensor.mem_coarseningFiberSupport]
    constructor
    · rintro ⟨⟨hsource, hmap⟩, hkeep⟩
      exact ⟨hsource, fun c ↦ ⟨congrFun hmap c, hkeep c⟩⟩
    · rintro ⟨hsource, hparts⟩
      exact ⟨⟨hsource, funext fun c ↦ (hparts c).1⟩, fun c ↦ (hparts c).2⟩
  · rfl

/-! ## Claim 2 on the localized leaf -/

/-- **`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 2, segmented and localized.**

A permutation of word positions that preserves the segmentation *and fixes the coarse target* is a
structure-preserving relabeling of the localized segmented leaf.  The extra premise is what makes
the shuffle an automorphism of a single fiber instead of a map between fibers. -/
noncomputable def Tensor.PartitionedTensor.segmentedLocalizedSplittingShuffle
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i)
    (htarget : positionRelabelBlockAddress B n σ target = target) :
    (P.segmentedLocalizedSplittingPower f n m seg profile target).StructureRelabeling :=
  (PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling P n σ).select
    (segmentedLocalizedKeep f seg profile target) fun c word ↦ by
      rw [PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv]
      refine and_congr ?_
        (SegmentedSplitRestriction.keeps_positionEquiv_symm profile n seg σ hperm c word)
      rw [positiveWordMap_position_symm_eq_iff (f c) n σ word (target c)]
      have hc : positiveWordPositionEquiv (B c) n σ (target c) = target c := congrFun htarget c
      rw [hc]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem Tensor.PartitionedTensor.segmentedLocalizedSplittingShuffle_partEquiv
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m) (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i)
    (htarget : positionRelabelBlockAddress B n σ target = target) (c : Leg) :
    (P.segmentedLocalizedSplittingShuffle f n m seg profile target σ hperm htarget).partEquiv c =
      positiveWordPositionEquiv (A c) n σ :=
  PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv P n σ c

end LocalizedPower

/-! ## The localized segmented Hole Lemma -/

section LocalizedHoleLemma

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The segmented Hole Lemma on a localized leaf.**

Identical in content to `restricts_indexedDirectSum_segmentedHoleRepair`, with the global leaf
replaced by the fine fiber over one coarse target.  The single new premise `htarget` says the
segment-preserving permutations fix that target; `hclaim3` and the budget are unchanged. -/
theorem restricts_indexedDirectSum_segmentedLocalizedHoleRepair
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (htarget : ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ i, seg (σ i) = seg i) →
      positionRelabelBlockAddress B n σ target = target)
    (holes : ι → Finset (SegmentedAvailableWord seg α))
    (hsmall : Fintype.card (SegmentedAvailableWord seg α) * ∏ t, (holes t).card <
      Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card ι) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : ι ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun t ↦ ((P.segmentedLocalizedSplittingPower f n m seg
            (SegmentedSplitRestriction.ofLeg Leg.Z α) target).holeSelect Leg.Z
          fun word ↦ word ∈ (holes t).image Subtype.val).realize)
      (P.segmentedLocalizedSplittingPower f n m seg
        (SegmentedSplitRestriction.ofLeg Leg.Z α) target).realize :=
  restricts_indexedDirectSum_segmentedHoleRepair_general P n m seg α hclaim3
    (segmentedLocalizedKeep f seg (SegmentedSplitRestriction.ofLeg Leg.Z α) target)
    (fun word hword ↦ segmentedKeeps_ofLeg_availability seg α word hword.2)
    (fun φ ↦ P.segmentedLocalizedSplittingShuffle f n m seg
      (SegmentedSplitRestriction.ofLeg Leg.Z α) target
      (segmentPermToPerm seg φ).symm (seg_segmentPermToPerm_symm φ)
      (htarget _ (seg_segmentPermToPerm_symm φ)))
    (fun φ w ↦ by
      rw [PartitionedTensor.segmentedLocalizedSplittingShuffle_partEquiv,
        positiveWordPositionEquiv_symm, Equiv.symm_symm, segmentedAvailableWordShuffle_val])
    holes hsmall

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The batched localized segmented Hole Lemma --- the uniform-leaf shape.**

The regrouping is verbatim the global version's; only the leaf differs. -/
theorem restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
    {retained : Type*} [Fintype retained] [DecidableEq retained]
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (htarget : ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ i, seg (σ i) = seg i) →
      positionRelabelBlockAddress B n σ target = target)
    (batch : retained → β) (hbatch : Function.Surjective batch)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained // batch a = b}) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : retained ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun a ↦ ((P.segmentedLocalizedSplittingPower f n m seg
            (SegmentedSplitRestriction.ofLeg Leg.Z α) target).holeSelect Leg.Z
          fun word ↦ word ∈ (holes a).image Subtype.val).realize)
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun _ ↦ (P.segmentedLocalizedSplittingPower f n m seg
          (SegmentedSplitRestriction.ofLeg Leg.Z α) target).realize) :=
  restricts_indexedDirectSum_segmentedHoleRepair_general_batched P n m seg α hclaim3
    (segmentedLocalizedKeep f seg (SegmentedSplitRestriction.ofLeg Leg.Z α) target)
    (fun word hword ↦ segmentedKeeps_ofLeg_availability seg α word hword.2)
    (fun φ ↦ P.segmentedLocalizedSplittingShuffle f n m seg
      (SegmentedSplitRestriction.ofLeg Leg.Z α) target
      (segmentPermToPerm seg φ).symm (seg_segmentPermToPerm_symm φ)
      (htarget _ (seg_segmentPermToPerm_symm φ)))
    (fun φ w ↦ by
      rw [PartitionedTensor.segmentedLocalizedSplittingShuffle_partEquiv,
        positiveWordPositionEquiv_symm, Equiv.symm_symm, segmentedAvailableWordShuffle_val])
    batch hbatch holes hbudget

end LocalizedHoleLemma

end AlgebraicComplexity
