/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWordShuffle
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingShuffle

/-!
# The segmented Hole Lemma

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This is the analogue of the committed
`Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair`
(`RestrictedSplittingShuffle.lean:274`) for a **segmented** restricted-splitting power: broken
copies whose hole sets satisfy the finite budget degenerate to one intact copy, where availability
is `[DuanWuZhou2022]`'s per-component condition (`hole_lemma.tex:40`) and the shuffling group is
`Sym[n_1] x ... x Sym[n_m]` (`:72-74`).

Nothing here is edited into the milestone's three engine files; this module sits beside them.

## What is proved and what is carried

**Claim 2 is proved.**  `segmentedRestrictedSplittingShuffle` lifts a segment-preserving position
permutation to a `StructureRelabeling` automorphism of the segmented power, exactly as
`PartitionedTensor.restrictedSplittingShuffle` (`:146`) does for the pooled one; the descent is
`StructureRelabeling.select` applied to the segmented Claim 1.  Stated for an arbitrary
segment-preserving `σ` rather than only for those of the form `segmentPermToPerm`, because the
repair argument needs it at the *inverse* of a segmented shuffle.

**Claim 3 is carried.**  `SegmentedFiberIndependence` appears as an explicit hypothesis of the Hole
Lemma and of its batched corollary, and of nothing else.  When the author settles the
shuffle-independence question the discharge is a substitution: no statement below changes shape,
and if the answer goes the other way only that hypothesis is lost, not the construction.

## The conclusion shape the campaign needs

`indexedDirectSum_segmentedHoleRepair` has the committed lemma's shape --- many broken copies to
**one** intact leaf --- because that is what the repair is.  The uniform-leaf shape the rest of the
campaign consumes comes from batching: `indexedDirectSum_segmentedHoleRepair_batched` applies the
repair once per batch and produces

`Restricts (⊕_{a ∈ retained} broken a) (⊕_{b ∈ β} 𝒯*)`,

i.e. `|β|` copies of **one** segmented leaf.  That is exactly the input
`restricts_power_symSix_of_plainStage` consumes, so the count lane's plain-power stage composes
with it directly and yields `hstage` with copy count `|β|^6`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section SegPreserving

variable {n m : ℕ}

/-- The inverse of a segment-preserving permutation preserves segments. -/
theorem segPreserving_symm {seg : Fin n → Fin m} {σ : Equiv.Perm (Fin n)}
    (hperm : ∀ i, seg (σ i) = seg i) (i : Fin n) : seg (σ.symm i) = seg i := by
  have h := hperm (σ.symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- A segmented shuffle, read on positions, preserves segments; so does its inverse. -/
theorem seg_segmentPermToPerm_symm {seg : Fin (n + 1) → Fin m} (φ : SegmentPerm seg)
    (i : Fin (n + 1)) : seg ((segmentPermToPerm seg φ).symm i) = seg i :=
  segPreserving_symm (seg_segmentPermToPerm seg φ) i

end SegPreserving

/-! ## Claim 1 for an arbitrary segment-preserving permutation -/

section ClaimOne

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- Segmented availability is invariant under any segment-preserving position permutation. -/
theorem segmentMultiplicity_positionEquiv (seg : Fin (n + 1) → Fin m)
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i)
    (word : PositiveWord I n) (t : Fin m) :
    segmentMultiplicity seg
        (positiveWordEquiv I n (positiveWordPositionEquiv I n σ word)) t =
      segmentMultiplicity seg (positiveWordEquiv I n word) t := by
  rw [positiveWordEquiv_position_apply]
  exact segmentMultiplicity_comp_perm seg σ hperm (positiveWordEquiv I n word) t

end ClaimOne

/-! ## Claim 2: the segmented shuffle is an automorphism -/

section ClaimTwo

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {n m : ℕ}

omit [∀ c, Fintype (A c)] in
/-- **Claim 1 on the segmented keep predicate.** -/
theorem SegmentedSplitRestriction.keeps_positionEquiv
    (profile : SegmentedSplitRestriction A m) (n : ℕ) (seg : Fin (n + 1) → Fin m)
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i)
    (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n seg c (positiveWordPositionEquiv (A c) n σ word) ↔
      profile.Keeps n seg c word := by
  unfold SegmentedSplitRestriction.Keeps
  refine forall_congr' fun t ↦ ?_
  rw [segmentMultiplicity_positionEquiv seg σ hperm word t]

omit [∀ c, Fintype (A c)] in
/-- The inverse form, which is the shape `StructureRelabeling.select` requires. -/
theorem SegmentedSplitRestriction.keeps_positionEquiv_symm
    (profile : SegmentedSplitRestriction A m) (n : ℕ) (seg : Fin (n + 1) → Fin m)
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i)
    (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n seg c ((positiveWordPositionEquiv (A c) n σ).symm word) ↔
      profile.Keeps n seg c word := by
  rw [positiveWordPositionEquiv_symm]
  exact SegmentedSplitRestriction.keeps_positionEquiv profile n seg σ.symm
    (segPreserving_symm hperm) c word

/-- **`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 2, segmented.**

A segment-preserving permutation of word positions is a structure-preserving relabeling of the
segmented restricted-splitting power.  The descent from the ambient power is
`StructureRelabeling.select` applied to the segmented Claim 1, exactly as in the pooled case
(`RestrictedSplittingShuffle.lean:146`). -/
noncomputable def Tensor.PartitionedTensor.segmentedRestrictedSplittingShuffle
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i) :
    (P.segmentedRestrictedSplittingPower n m seg profile).StructureRelabeling :=
  (PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling P n σ).select
    (profile.Keeps n seg) fun c word ↦ by
      rw [PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv]
      exact SegmentedSplitRestriction.keeps_positionEquiv_symm profile n seg σ hperm c word

@[simp] theorem Tensor.PartitionedTensor.segmentedRestrictedSplittingShuffle_partEquiv
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (σ : Equiv.Perm (Fin (n + 1))) (hperm : ∀ i, seg (σ i) = seg i) (c : Leg) :
    (P.segmentedRestrictedSplittingShuffle n m seg profile σ hperm).partEquiv c =
      positiveWordPositionEquiv (A c) n σ :=
  PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv P n σ c

end ClaimTwo


/-! ## The segmented Hole Lemma -/

section HoleLemma

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

@[simp] theorem segmentedShuffleUniformity_relabel {n m : ℕ}
    {seg : Fin (n + 1) → Fin m} {α : Fin m → A Leg.Z → ℕ}
    (h : SegmentedFiberIndependence seg α) (φ : SegmentPerm seg) :
    (segmentedShuffleUniformity_of_fiberIndependence h).relabel φ =
      segmentedAvailableWordShuffle seg α φ := rfl

/-- **The segmented Hole Lemma.**

Broken copies of the segmented restricted-splitting power whose hole sets satisfy the finite budget
`|avail| * ∏_t |H_t| < |avail|^s` degenerate to one intact copy.  The holes are an **arbitrary**
`Finset` of segmented available blocks per copy --- `[DuanWuZhou2022]`'s joint damage
(`hole_lemma.tex:48`), not a product of per-component hole sets.

`hclaim3` is `[DuanWuZhou2022]`'s Claim 3 for the segmented setting, carried as a hypothesis; every
other ingredient is proved.  The proof is the committed
`indexedDirectSum_restrictedSplittingHoleRepair` (`RestrictedSplittingShuffle.lean:274`) with the
pooled objects replaced by their segmented analogues throughout. -/
theorem restricts_indexedDirectSum_segmentedHoleRepair
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (holes : ι → Finset (SegmentedAvailableWord seg α))
    (hsmall : Fintype.card (SegmentedAvailableWord seg α) * ∏ t, (holes t).card <
      Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card ι) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : ι ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun t ↦ ((P.segmentedRestrictedSplittingPower n m seg
            (SegmentedSplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes t).image Subtype.val).realize)
      (P.segmentedRestrictedSplittingPower n m seg
        (SegmentedSplitRestriction.ofLeg Leg.Z α)).realize := by
  classical
  obtain ⟨shuffle, hshuffle⟩ :=
    exists_segmented_shuffles_avoiding
      (segmentedShuffleUniformity_of_fiberIndependence hclaim3) holes hsmall
  set profile : SegmentedSplitRestriction A m :=
    SegmentedSplitRestriction.ofLeg Leg.Z α with hprofile
  set relabeling : ι →
      (P.segmentedRestrictedSplittingPower n m seg profile).StructureRelabeling :=
    fun t ↦ P.segmentedRestrictedSplittingShuffle n m seg profile
      (segmentPermToPerm seg (shuffle t)).symm
      (seg_segmentPermToPerm_symm (shuffle t)) with hrelabeling
  have havailable : ∀ address ∈ (P.segmentedRestrictedSplittingPower n m seg profile).support,
      ∀ t, segmentMultiplicity seg
        (positiveWordEquiv (A Leg.Z) n (address Leg.Z)) t = α t := by
    intro address haddress
    rw [PartitionedTensor.mem_segmentedRestrictedSplittingPower_support] at haddress
    have hZ := haddress.2 Leg.Z
    rwa [SegmentedSplitRestriction.keeps_iff_of_some
      (fun t ↦ SegmentedSplitRestriction.ofLeg_self (A := A) Leg.Z α t)] at hZ
  set pick : PositiveWord (A Leg.Z) n → ι := fun word ↦
    if h : ∀ t, segmentMultiplicity seg (positiveWordEquiv (A Leg.Z) n word) t = α t then
      (hshuffle ⟨word, h⟩).choose
    else Classical.arbitrary ι with hpick
  refine Restricts.indexedDirectSum_shuffledLegHoleRepair
    (P.segmentedRestrictedSplittingPower n m seg profile) Leg.Z relabeling
    (fun t word ↦ word ∈ (holes t).image Subtype.val) pick ?_
  intro address haddress
  have htype := havailable address haddress
  set available : SegmentedAvailableWord seg α := ⟨address Leg.Z, htype⟩ with havailableDef
  have hpickValue : pick (address Leg.Z) = (hshuffle available).choose := by
    rw [hpick]
    simp only [dif_pos htype]
  have hnotMem :
      segmentedAvailableWordShuffle seg α (shuffle (pick (address Leg.Z))) available ∉
        holes (pick (address Leg.Z)) := by
    rw [hpickValue]
    have h := (hshuffle available).choose_spec
    rwa [segmentedShuffleUniformity_relabel] at h
  have hpartEquiv :
      ((relabeling (pick (address Leg.Z))).partEquiv Leg.Z).symm (address Leg.Z) =
        (segmentedAvailableWordShuffle seg α
          (shuffle (pick (address Leg.Z))) available).1 := by
    rw [hrelabeling]
    rw [PartitionedTensor.segmentedRestrictedSplittingShuffle_partEquiv,
      positiveWordPositionEquiv_symm, Equiv.symm_symm, segmentedAvailableWordShuffle_val]
  rw [hpartEquiv]
  intro hmem
  obtain ⟨other, hother, hvalue⟩ := Finset.mem_image.mp hmem
  exact hnotMem (Subtype.ext hvalue ▸ hother)


/-- **The batched segmented Hole Lemma --- the uniform-leaf shape.**

Applying the repair once per batch turns the broken copies indexed by the retained addresses into
`|β|` copies of **one** intact segmented leaf.  The regrouping is the committed
`Restricts.indexedDirectSum_equiv` / `Restricts.indexedDirectSum_sigma` pair, exactly as in
`AsymmetricGlobalValue.lean:414-441`.

This is the interface the rest of the campaign consumes: composed after a cleanup
`Restricts (Tensor.power T (n+1)) (⊕_{retained} constituent)` and the factorwise `hleaf`, it
produces a plain-power stage onto `|β|` copies of one uniform leaf, which is precisely the input of
`restricts_power_symSix_of_plainStage` and therefore yields `hstage` with copy count `|β|^6`. -/
theorem restricts_indexedDirectSum_segmentedHoleRepair_batched
    {retained : Type*} [Fintype retained] [DecidableEq retained]
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (batch : retained → β) (hbatch : Function.Surjective batch)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card {a : retained // batch a = b}) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : retained ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun a ↦ ((P.segmentedRestrictedSplittingPower n m seg
            (SegmentedSplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes a).image Subtype.val).realize)
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun _ ↦ (P.segmentedRestrictedSplittingPower n m seg
          (SegmentedSplitRestriction.ofLeg Leg.Z α)).realize) := by
  classical
  refine (Tensor.Restricts.indexedDirectSum_equiv
    (J := Σ b : β, {a : retained // batch a = b})
    (U := fun _ ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
    (S := fun ab ↦ ((P.segmentedRestrictedSplittingPower n m seg
        (SegmentedSplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
      fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)
    (Equiv.sigmaFiberEquiv batch).symm fun _ ↦ Restricts.refl _).trans ?_
  refine (Tensor.Restricts.indexedDirectSum_sigma
    (J := fun b : β ↦ {a : retained // batch a = b})
    (S := fun _ _ ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
    (fun ab ↦ ((P.segmentedRestrictedSplittingPower n m seg
        (SegmentedSplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
      fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)).trans ?_
  refine Tensor.Restricts.indexedDirectSum fun b ↦ ?_
  haveI : Nonempty {a : retained // batch a = b} := by
    obtain ⟨a, ha⟩ := hbatch b
    exact ⟨⟨a, ha⟩⟩
  exact restricts_indexedDirectSum_segmentedHoleRepair P n m seg α hclaim3
    (fun a : {a : retained // batch a = b} ↦ holes a.1) (hbudget b)

end HoleLemma

end AlgebraicComplexity