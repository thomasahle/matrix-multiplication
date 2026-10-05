/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivision
import AlgebraicComplexity.Tensor.PowerZeroUnit

/-!
# Zero-multiplicity regional division

`InterfaceTensorRegionalDivision` proves binary regional division when both regions contain at
least one tensor factor.  Exact recursive certificates also permit a region of multiplicity zero.
Such a region is not represented by a `PositiveWord`: its tensor semantics is the canonical
zeroth power `Tensor.power T 0`.

This file proves the two one-sided boundary cases and the all-zero case.  Together with
`Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision`, these theorems cover every
pair of natural-number child multiplicities.  No region orientation occurs in any hypothesis.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-- Every count in a zero-sample complete-split profile vanishes. -/
theorem CompleteSplitProfile.counts_eq_zero
    {depth total : ℕ} (profile : CompleteSplitProfile depth total 0)
    (word : SplitWord depth) : profile.counts word = 0 := by
  classical
  have hall := Finset.sum_eq_zero_iff.mp profile.sum_counts
  exact hall word (Finset.mem_univ word)

section

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Encoded complete-split selection depends only on the count functions of its profiles. -/
theorem Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles_congr_counts
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (left right : ∀ c,
      CompleteSplitProfile depth (index.count c) (n + 1))
    (hcounts : ∀ c, (left c).counts = (right c).counts) :
    P.selectEncodedCompleteSplitProfiles encode index left =
      P.selectEncodedCompleteSplitProfiles encode index right := by
  apply PartitionedTensor.ext
  · apply Finset.ext
    intro address
    simp only [Tensor.PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support]
    apply and_congr_right
    intro _hsupport
    apply forall_congr'
    intro c
    unfold CompleteSplitProfile.IsConsistent
    rw [hcounts c]
  · rfl

/-- If the left multiplicity is zero, the parent multiplicity is the right multiplicity. -/
theorem ExactInterfaceTermBinaryDivision.parentMultiplicity_eq_right_of_left_zero
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = 0)
    (hright : division.rightMultiplicity = n + 1) :
    parent.multiplicity = n + 1 := by
  rw [division.multiplicity_eq, hleft, hright, Nat.zero_add]

/-- If the right multiplicity is zero, the parent multiplicity is the left multiplicity. -/
theorem ExactInterfaceTermBinaryDivision.parentMultiplicity_eq_left_of_right_zero
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = n + 1)
    (hright : division.rightMultiplicity = 0) :
    parent.multiplicity = n + 1 := by
  rw [division.multiplicity_eq, hleft, hright, Nat.add_zero]

/-- If both child multiplicities vanish, so does the parent multiplicity. -/
theorem ExactInterfaceTermBinaryDivision.parentMultiplicity_eq_zero
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = 0)
    (hright : division.rightMultiplicity = 0) :
    parent.multiplicity = 0 := by
  rw [division.multiplicity_eq, hleft, hright, Nat.zero_add]

/-- The four zero/positive cases exhaust the two child multiplicities.  This is a convenient
dispatcher for clients whose tensor targets depend on the predecessor of each positive
multiplicity. -/
theorem ExactInterfaceTermBinaryDivision.multiplicity_cases
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent) :
    (division.leftMultiplicity = 0 ∧ division.rightMultiplicity = 0) ∨
    (∃ m, division.leftMultiplicity = 0 ∧ division.rightMultiplicity = m + 1) ∨
    (∃ n, division.leftMultiplicity = n + 1 ∧ division.rightMultiplicity = 0) ∨
    (∃ n m, division.leftMultiplicity = n + 1 ∧
      division.rightMultiplicity = m + 1) := by
  cases hleft : division.leftMultiplicity with
  | zero =>
      cases hright : division.rightMultiplicity with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ m => exact Or.inr (Or.inl ⟨m, rfl, rfl⟩)
  | succ n =>
      cases hright : division.rightMultiplicity with
      | zero => exact Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))
      | succ m => exact Or.inr (Or.inr (Or.inr ⟨n, m, rfl, rfl⟩))

/-- Orientation-free binary regional division when the left child has multiplicity zero.  The
left child is the explicit tensor unit `power P.realize 0`; the parent's exact profile equals the
right child's profile because every left count vanishes. -/
theorem Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision_leftZero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = 0)
    (hright : division.rightMultiplicity = n + 1) :
    Restricts
      (P.selectEncodedExactInterfaceTerm encode parent
        (division.parentMultiplicity_eq_right_of_left_zero hleft hright)).realize
      (Tensor.external (Tensor.power P.realize 0)
        (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize) := by
  let hparent := division.parentMultiplicity_eq_right_of_left_zero hleft hright
  let parentProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + 1) :=
    fun c ↦ parent.positivePowerProfile hparent c
  let rightProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + 1) :=
    fun c ↦ division.rightTerm.positivePowerProfile hright c
  have hcounts : ∀ c, (parentProfile c).counts = (rightProfile c).counts := by
    intro c
    funext word
    dsimp [parentProfile, rightProfile,
      ExactInterfaceTermParameters.positivePowerProfile]
    rw [CompleteSplitProfile.counts_cast, CompleteSplitProfile.counts_cast]
    have hzero : (division.leftSplit c).counts word = 0 := by
      let leftProfile : CompleteSplitProfile depth (parent.index.count c) 0 :=
        hleft ▸ division.leftSplit c
      have hz := CompleteSplitProfile.counts_eq_zero leftProfile word
      simpa [leftProfile, CompleteSplitProfile.counts_cast] using hz
    rw [division.split_counts_eq c word, hzero, Nat.zero_add]
  have hselected :
      P.selectEncodedExactInterfaceTerm encode parent hparent =
        P.selectEncodedExactInterfaceTerm encode division.rightTerm hright := by
    exact Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles_congr_counts
      P encode parent.index parentProfile rightProfile hcounts
  have hparentRight : Isomorphic
      (P.selectEncodedExactInterfaceTerm encode parent hparent).realize
      (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize := by
    rw [hselected]
    exact Tensor.Isomorphic.refl _
  exact (hparentRight.trans
    (Tensor.Isomorphic.powerZeroExternalLeft P.realize
      (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize).symm).restricts

/-- Orientation-free binary regional division when the right child has multiplicity zero. -/
theorem Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision_rightZero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = n + 1)
    (hright : division.rightMultiplicity = 0) :
    Restricts
      (P.selectEncodedExactInterfaceTerm encode parent
        (division.parentMultiplicity_eq_left_of_right_zero hleft hright)).realize
      (Tensor.external
        (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize
        (Tensor.power P.realize 0)) := by
  let hparent := division.parentMultiplicity_eq_left_of_right_zero hleft hright
  let parentProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + 1) :=
    fun c ↦ parent.positivePowerProfile hparent c
  let leftProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + 1) :=
    fun c ↦ division.leftTerm.positivePowerProfile hleft c
  have hcounts : ∀ c, (parentProfile c).counts = (leftProfile c).counts := by
    intro c
    funext word
    dsimp [parentProfile, leftProfile,
      ExactInterfaceTermParameters.positivePowerProfile]
    rw [CompleteSplitProfile.counts_cast, CompleteSplitProfile.counts_cast]
    have hzero : (division.rightSplit c).counts word = 0 := by
      let rightProfile : CompleteSplitProfile depth (parent.index.count c) 0 :=
        hright ▸ division.rightSplit c
      have hz := CompleteSplitProfile.counts_eq_zero rightProfile word
      simpa [rightProfile, CompleteSplitProfile.counts_cast] using hz
    rw [division.split_counts_eq c word, hzero, Nat.add_zero]
  have hselected :
      P.selectEncodedExactInterfaceTerm encode parent hparent =
        P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft := by
    exact Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles_congr_counts
      P encode parent.index parentProfile leftProfile hcounts
  have hparentLeft : Isomorphic
      (P.selectEncodedExactInterfaceTerm encode parent hparent).realize
      (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize := by
    rw [hselected]
    exact Tensor.Isomorphic.refl _
  exact (hparentLeft.trans
    (Tensor.Isomorphic.powerZeroExternalRight
      (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize
      P.realize).symm).restricts

/-- Orientation-free binary regional division when both children have multiplicity zero.  All
three exact terms have the canonical tensor-unit semantics. -/
theorem Tensor.Restricts.power_binaryDivision_bothZero
    (P : PartitionedTensor (K := K) (A := A) V)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = 0)
    (hright : division.rightMultiplicity = 0) :
    Restricts
      (Tensor.power P.realize parent.multiplicity)
      (Tensor.external
        (Tensor.power P.realize division.leftMultiplicity)
        (Tensor.power P.realize division.rightMultiplicity)) := by
  rw [division.parentMultiplicity_eq_zero hleft hright, hleft, hright]
  exact (Tensor.Isomorphic.powerZeroExternalLeft P.realize
    (Tensor.power P.realize 0)).symm.restricts

end

end AlgebraicComplexity
