/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepair

set_option autoImplicit false

/-!
# The segmented Hole Lemma over an arbitrary selected leaf

`SegmentedHoleRepair.lean` proves the segmented Hole Lemma for the leaf
`(P.positivePower n).select (profile.Keeps n seg)`, and a localized campaign needs the same
statement for a leaf cut down to one coarse fiber.  The two proofs differ only in the leaf and in
which permutations act on it; everything between --- the shuffle choice, the availability
bookkeeping, the pick function, the descent through
`Restricts.indexedDirectSum_shuffledLegHoleRepair` --- is identical.

This module states the Hole Lemma once, over an arbitrary legwise keep predicate `keep`, given

* `havail`: a retained `Z`-word has the prescribed segment types, so it is a
  `SegmentedAvailableWord`;
* `shuffle₀`: every segment-preserving permutation acts on the selected leaf, by its position
  relabeling.

Both hypotheses are cheap at every call site: `havail` is the `Z` component of the keep predicate
and `shuffle₀` is `StructureRelabeling.select` applied to Claim 1.  The counting --- Claim 3 as
`SegmentedFiberIndependence` and the budget --- is untouched, and note that `havail` runs one way
only: the leaf's `Z`-words need merely be *among* the available words, never all of them, which is
what lets a localized leaf reuse the same budget.

`SegmentedHoleRepair.lean` is frozen milestone machinery and keeps its own proof; this module is
the canonical one for new clients.

`[DuanWuZhou2022]`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section GeneralHoleLemma

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The segmented Hole Lemma, over an arbitrary selected leaf.** -/
theorem restricts_indexedDirectSum_segmentedHoleRepair_general
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (keep : ∀ c, PositiveWord (A c) n → Prop) [∀ c word, Decidable (keep c word)]
    (havail : ∀ word : PositiveWord (A Leg.Z) n, keep Leg.Z word →
      ∀ t, segmentMultiplicity seg (positiveWordEquiv (A Leg.Z) n word) t = α t)
    (shuffle₀ : SegmentPerm seg → ((P.positivePower n).select keep).StructureRelabeling)
    (hshuffleZ : ∀ (φ : SegmentPerm seg) (w : SegmentedAvailableWord seg α),
      ((shuffle₀ φ).partEquiv Leg.Z).symm w.1 =
        (segmentedAvailableWordShuffle seg α φ w).1)
    (holes : ι → Finset (SegmentedAvailableWord seg α))
    (hsmall : Fintype.card (SegmentedAvailableWord seg α) * ∏ t, (holes t).card <
      Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card ι) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : ι ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun t ↦ (((P.positivePower n).select keep).holeSelect Leg.Z
          fun word ↦ word ∈ (holes t).image Subtype.val).realize)
      ((P.positivePower n).select keep).realize := by
  classical
  obtain ⟨shuffle, hshuffle⟩ :=
    exists_segmented_shuffles_avoiding
      (segmentedShuffleUniformity_of_fiberIndependence hclaim3) holes hsmall
  have havailable : ∀ address ∈ ((P.positivePower n).select keep).support,
      ∀ t, segmentMultiplicity seg
        (positiveWordEquiv (A Leg.Z) n (address Leg.Z)) t = α t := by
    intro address haddress
    rw [PartitionedTensor.mem_select_support] at haddress
    exact havail _ (haddress.2 Leg.Z)
  refine Restricts.indexedDirectSum_shuffledLegHoleRepair
    ((P.positivePower n).select keep) Leg.Z (fun t ↦ shuffle₀ (shuffle t))
    (fun t word ↦ word ∈ (holes t).image Subtype.val)
    (fun word ↦
      if h : ∀ t, segmentMultiplicity seg (positiveWordEquiv (A Leg.Z) n word) t = α t then
        (hshuffle ⟨word, h⟩).choose
      else Classical.arbitrary ι) ?_
  intro address haddress
  have htype := havailable address haddress
  have hpickValue :
      (if h : ∀ t, segmentMultiplicity seg
            (positiveWordEquiv (A Leg.Z) n (address Leg.Z)) t = α t then
          (hshuffle ⟨address Leg.Z, h⟩).choose
        else Classical.arbitrary ι) =
      (hshuffle ⟨address Leg.Z, htype⟩).choose := by
    simp only [dif_pos htype]
  rw [hpickValue]
  have hnotMem :
      segmentedAvailableWordShuffle seg α
          (shuffle (hshuffle ⟨address Leg.Z, htype⟩).choose) ⟨address Leg.Z, htype⟩ ∉
        holes (hshuffle ⟨address Leg.Z, htype⟩).choose := by
    have h := (hshuffle ⟨address Leg.Z, htype⟩).choose_spec
    rwa [segmentedShuffleUniformity_relabel] at h
  rw [hshuffleZ (shuffle (hshuffle ⟨address Leg.Z, htype⟩).choose) ⟨address Leg.Z, htype⟩]
  intro hmem
  obtain ⟨other, hother, hvalue⟩ := Finset.mem_image.mp hmem
  exact hnotMem (Subtype.ext hvalue ▸ hother)

/-- **The batched form, over an arbitrary selected leaf.**  Applying the repair once per batch
turns the broken copies indexed by the retained addresses into `|β|` copies of one intact leaf. -/
theorem restricts_indexedDirectSum_segmentedHoleRepair_general_batched
    {retained : Type*} [Fintype retained] [DecidableEq retained]
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
    (keep : ∀ c, PositiveWord (A c) n → Prop) [∀ c word, Decidable (keep c word)]
    (havail : ∀ word : PositiveWord (A Leg.Z) n, keep Leg.Z word →
      ∀ t, segmentMultiplicity seg (positiveWordEquiv (A Leg.Z) n word) t = α t)
    (shuffle₀ : SegmentPerm seg → ((P.positivePower n).select keep).StructureRelabeling)
    (hshuffleZ : ∀ (φ : SegmentPerm seg) (w : SegmentedAvailableWord seg α),
      ((shuffle₀ φ).partEquiv Leg.Z).symm w.1 =
        (segmentedAvailableWordShuffle seg α φ w).1)
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
        fun a ↦ (((P.positivePower n).select keep).holeSelect Leg.Z
          fun word ↦ word ∈ (holes a).image Subtype.val).realize)
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun _ ↦ ((P.positivePower n).select keep).realize) := by
  classical
  refine (Tensor.Restricts.indexedDirectSum_equiv
    (J := Σ b : β, {a : retained // batch a = b})
    (U := fun _ ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
    (S := fun ab ↦ (((P.positivePower n).select keep).holeSelect Leg.Z
      fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)
    (Equiv.sigmaFiberEquiv batch).symm fun _ ↦ Restricts.refl _).trans ?_
  refine (Tensor.Restricts.indexedDirectSum_sigma
    (J := fun b : β ↦ {a : retained // batch a = b})
    (S := fun _ _ ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
    (fun ab ↦ (((P.positivePower n).select keep).holeSelect Leg.Z
      fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)).trans ?_
  refine Tensor.Restricts.indexedDirectSum fun b ↦ ?_
  haveI : Nonempty {a : retained // batch a = b} := by
    obtain ⟨a, ha⟩ := hbatch b
    exact ⟨⟨a, ha⟩⟩
  exact restricts_indexedDirectSum_segmentedHoleRepair_general P n m seg α hclaim3
    keep havail shuffle₀ hshuffleZ (fun a : {a : retained // batch a = b} ↦ holes a.1) (hbudget b)

/-! ## The global leaf, instantiated -/

omit [∀ c, Fintype (A c)] in
/-- The `Z` component of the segmented keep predicate is exactly availability. -/
theorem segmentedKeeps_ofLeg_availability {n m : ℕ} (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (word : PositiveWord (A Leg.Z) n)
    (hword : (SegmentedSplitRestriction.ofLeg (A := A) Leg.Z α).Keeps n seg Leg.Z word) :
    ∀ t, segmentMultiplicity seg (positiveWordEquiv (A Leg.Z) n word) t = α t := by
  rwa [SegmentedSplitRestriction.keeps_iff_of_some
    (fun t ↦ SegmentedSplitRestriction.ofLeg_self (A := A) Leg.Z α t)] at hword

/-- **The batched segmented Hole Lemma on the global leaf, from the general form.**

Same statement as the frozen `restricts_indexedDirectSum_segmentedHoleRepair_batched`; this is the
copy new clients should use, so that the localized and global forms share one proof. -/
theorem restricts_indexedDirectSum_segmentedPowerHoleRepair_batched
    {retained : Type*} [Fintype retained] [DecidableEq retained]
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (α : Fin m → A Leg.Z → ℕ) (hclaim3 : SegmentedFiberIndependence seg α)
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
        fun a ↦ ((P.segmentedRestrictedSplittingPower n m seg
            (SegmentedSplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes a).image Subtype.val).realize)
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun _ ↦ (P.segmentedRestrictedSplittingPower n m seg
          (SegmentedSplitRestriction.ofLeg Leg.Z α)).realize) :=
  restricts_indexedDirectSum_segmentedHoleRepair_general_batched P n m seg α hclaim3
    ((SegmentedSplitRestriction.ofLeg (A := A) Leg.Z α).Keeps n seg)
    (fun word hword ↦ segmentedKeeps_ofLeg_availability seg α word hword)
    (fun φ ↦ P.segmentedRestrictedSplittingShuffle n m seg
      (SegmentedSplitRestriction.ofLeg Leg.Z α) (segmentPermToPerm seg φ).symm
      (seg_segmentPermToPerm_symm φ))
    (fun φ w ↦ by
      rw [PartitionedTensor.segmentedRestrictedSplittingShuffle_partEquiv,
        positiveWordPositionEquiv_symm, Equiv.symm_symm, segmentedAvailableWordShuffle_val])
    batch hbatch holes hbudget

end GeneralHoleLemma

end AlgebraicComplexity
