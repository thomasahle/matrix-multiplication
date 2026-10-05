/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization

/-!
# Exact regional division of interface tensors

This module proves the tensor-level form of orientation-free binary regional division.  Two
nonempty consecutive regions whose exact complete-split counts add to a parent profile can be
extracted from the parent selected interface tensor by an actual tensor restriction.  No
orientation or distinctness hypothesis occurs in the statement.

The proof has three reusable layers:

* consecutive positive partitioned powers concatenate exactly, including their dependent block
  spaces and constituents;
* concatenation commutes with arbitrary legwise block selection; and
* exact child profiles imply the parent profile because empirical multiplicities add under
  sequence concatenation.

Positive words represent nonempty regions, so the final theorem assumes the two regional
multiplicities have the forms `n + 1` and `m + 1`.  A future empty-power partition API can extend
the statement to zero-multiplicity regions without changing the positive case proved here.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

set_option maxHeartbeats 400000 in
/-- At every combined block address, concatenating two positive powers gives exactly the
constituent of the combined positive power.  This includes the reassociation maps between the
dependent tensor-product block spaces. -/
theorem PartitionedTensor.appendPositiveWordPartitions_positivePower_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    ∀ (m : ℕ)
      (address : BlockAddress (fun c ↦ PositiveWord (A c) (n + m + 1))),
      (PartitionedTensor.appendPositiveWordPartitions
        (P.positivePower n) (P.positivePower m)).constituent address =
        (P.positivePower (n + m + 1)).constituent address
  | 0, address => by
      unfold PartitionedTensor.appendPositiveWordPartitions
      rw [PartitionedTensor.reindex_constituent]
      change map (fun _c ↦ LinearMap.id)
          (Tensor.external
            ((P.positivePower n).constituent (fun c ↦ (address c).1))
            (P.constituent (fun c ↦ (address c).2))) = _
      rw [map_id]
      rfl
  | m + 1, address => by
      unfold PartitionedTensor.appendPositiveWordPartitions
      rw [PartitionedTensor.reindex_constituent]
      change map (fun c ↦
          ((TensorProduct.assoc K _ _ _).symm.trans
            (TensorProduct.congr
              (positivePowerBlockAppendEquivAt (K := K) (V := V) n m c
                (address c).1)
              (LinearEquiv.refl K _))).toLinearMap)
        (Tensor.external
          ((P.positivePower n).constituent (fun c ↦
            ((positiveWordAppendEquiv (A c) n m).symm (address c).1).1))
          (Tensor.external
            ((P.positivePower m).constituent (fun c ↦
              ((positiveWordAppendEquiv (A c) n m).symm (address c).1).2))
            (P.constituent (fun c ↦ (address c).2)))) = _
      change map (fun c ↦
          (TensorProduct.congr
            (positivePowerBlockAppendEquivAt (K := K) (V := V) n m c
              (address c).1)
            (LinearEquiv.refl K _)).toLinearMap ∘ₗ
          (TensorProduct.assoc K _ _ _).symm.toLinearMap)
        (Tensor.external
          ((P.positivePower n).constituent (fun c ↦
            ((positiveWordAppendEquiv (A c) n m).symm (address c).1).1))
          (Tensor.external
            ((P.positivePower m).constituent (fun c ↦
              ((positiveWordAppendEquiv (A c) n m).symm (address c).1).2))
            (P.constituent (fun c ↦ (address c).2)))) = _
      rw [map_comp]
      simp only [LinearMap.comp_apply]
      rw [map_external_assoc_symm]
      change map (fun c ↦ TensorProduct.map
          (positivePowerBlockAppendEquivAt (K := K) (V := V) n m c
            (address c).1).toLinearMap
          (LinearMap.id (R := K) (M := V c (address c).2)))
        (Tensor.external
          (Tensor.external
            ((P.positivePower n).constituent (fun c ↦
              ((positiveWordAppendEquiv (A c) n m).symm (address c).1).1))
            ((P.positivePower m).constituent (fun c ↦
              ((positiveWordAppendEquiv (A c) n m).symm (address c).1).2)))
          (P.constituent (fun c ↦ (address c).2))) = _
      rw [map_external]
      have ih := P.appendPositiveWordPartitions_positivePower_constituent n m
        (fun c ↦ (address c).1)
      unfold PartitionedTensor.appendPositiveWordPartitions at ih
      rw [PartitionedTensor.reindex_constituent] at ih
      simp only [PartitionedTensor.external, blockAddressCongr_symm_apply] at ih
      let lastTensor :=
        map (fun _c ↦ LinearMap.id)
          (P.constituent (fun c ↦ (address c).2))
      have hstep := congrArg (fun T ↦ Tensor.external T lastTensor) ih
      have htail :
          Tensor.external
              ((P.positivePower (n + m + 1)).constituent
                (fun c ↦ (address c).1))
              lastTensor =
            (P.positivePower (n + (m + 1) + 1)).constituent address := by
        dsimp [lastTensor]
        rw [map_id]
        rfl
      exact hstep.trans htail

/-- Splitting a positive partitioned power into two consecutive nonempty regions and then
concatenating their block words recovers the original partitioned power exactly. -/
theorem PartitionedTensor.appendPositiveWordPartitions_positivePowers
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) :
    PartitionedTensor.appendPositiveWordPartitions
        (P.positivePower n) (P.positivePower m) =
      P.positivePower (n + m + 1) := by
  apply PartitionedTensor.ext
  · exact P.positivePower_external_support_map_append n m
  · funext address
    exact P.appendPositiveWordPartitions_positivePower_constituent n m address

/-- Concatenating two independently selected regional partitions is the selection of combined
words whose left and right pieces satisfy the corresponding regional predicates. -/
theorem PartitionedTensor.appendPositiveWordPartitions_select
    (left : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) (PositivePowerBlockSpace K V n))
    (right : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) m) (PositivePowerBlockSpace K V m))
    (keepLeft : ∀ c, PositiveWord (A c) n → Prop)
    (keepRight : ∀ c, PositiveWord (A c) m → Prop)
    [∀ c word, Decidable (keepLeft c word)]
    [∀ c word, Decidable (keepRight c word)] :
    PartitionedTensor.appendPositiveWordPartitions
        (left.select keepLeft) (right.select keepRight) =
      (PartitionedTensor.appendPositiveWordPartitions left right).select
        (fun c word ↦
          keepLeft c ((positiveWordAppendEquiv (A c) n m).symm word).1 ∧
          keepRight c ((positiveWordAppendEquiv (A c) n m).symm word).2) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.appendPositiveWordPartitions,
      PartitionedTensor.external, blockAddressCongr, blockAddressProductEquiv]
    constructor
    · rintro ⟨⟨hleft, hkeepLeft⟩, hright, hkeepRight⟩
      exact ⟨⟨hleft, hright⟩, fun c ↦ ⟨hkeepLeft c, hkeepRight c⟩⟩
    · rintro ⟨⟨hleft, hright⟩, hkeep⟩
      exact ⟨⟨hleft, fun c ↦ (hkeep c).1⟩, hright, fun c ↦ (hkeep c).2⟩
  · rfl

end AlgebraicComplexity.Tensor

namespace AlgebraicComplexity

open Tensor

universe u v w

/-- Encoded positive words of two exact regional profiles concatenate to a word of their parent
profile whenever the parent counts are the pointwise sums of the child counts. -/
theorem CompleteSplitProfile.matchesEncodedPositiveWord_append
    {depth total n m : ℕ} {A : Type w}
    (parent : CompleteSplitProfile depth total (n + m + 2))
    (left : CompleteSplitProfile depth total (n + 1))
    (right : CompleteSplitProfile depth total (m + 1))
    (hcounts : ∀ word, parent.counts word = left.counts word + right.counts word)
    (encode : A → SplitWord depth)
    (leftWord : PositiveWord A n) (rightWord : PositiveWord A m)
    (hleft : left.MatchesEncodedPositiveWord encode leftWord)
    (hright : right.MatchesEncodedPositiveWord encode rightWord) :
    parent.MatchesEncodedPositiveWord encode
      (positiveWordAppend leftWord m rightWord) := by
  rw [CompleteSplitProfile.matchesEncodedPositiveWord_iff] at hleft hright ⊢
  unfold CompleteSplitProfile.IsConsistent at hleft hright ⊢
  rw [positiveWordEquiv_append]
  have hsize : n + m + 2 = (n + 1) + (m + 1) := by omega
  have hsequence :
      encode ∘
          (Fin.append (positiveWordEquiv A n leftWord)
              (positiveWordEquiv A m rightWord) ∘ Fin.cast hsize) =
        (Fin.append
            (encode ∘ positiveWordEquiv A n leftWord)
            (encode ∘ positiveWordEquiv A m rightWord)) ∘
          Fin.cast hsize := by
    funext i
    simp only [Function.comp_apply]
    let j := Fin.cast hsize i
    change encode (Fin.append (positiveWordEquiv A n leftWord)
        (positiveWordEquiv A m rightWord) j) =
      Fin.append
        (encode ∘ positiveWordEquiv A n leftWord)
        (encode ∘ positiveWordEquiv A m rightWord) j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp [Function.comp_apply]
    · intro k
      simp [Function.comp_apply]
  rw [hsequence, WordType.multiplicity_cast,
    WordType.multiplicity_append, hleft, hright]
  funext word
  exact (hcounts word).symm

/-- Transporting a complete-split profile along an equality of sample counts does not change its
stored count table. -/
@[simp] theorem CompleteSplitProfile.counts_cast
    {depth total samples samples' : ℕ}
    (hsamples : samples = samples')
    (profile : CompleteSplitProfile depth total samples)
    (word : SplitWord depth) :
    (hsamples ▸ profile).counts word = profile.counts word := by
  subst samples'
  rfl

section

variable {K : Type u} [CommSemiring K]
variable {depth n m : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Tensor-level regional division for arbitrary encoded complete-split profiles.  Selecting the
parent profile restricts to the external product of the two selected child profiles. -/
theorem Tensor.Restricts.selectEncodedCompleteSplitProfiles_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (parentProfile : ∀ c,
      CompleteSplitProfile depth (index.count c) (n + m + 2))
    (leftProfile : ∀ c,
      CompleteSplitProfile depth (index.count c) (n + 1))
    (rightProfile : ∀ c,
      CompleteSplitProfile depth (index.count c) (m + 1))
    (hcounts : ∀ c word,
      (parentProfile c).counts word =
        (leftProfile c).counts word + (rightProfile c).counts word) :
    Restricts
      (P.selectEncodedCompleteSplitProfiles encode index parentProfile).realize
      (Tensor.external
        (P.selectEncodedCompleteSplitProfiles encode index leftProfile).realize
        (P.selectEncodedCompleteSplitProfiles encode index rightProfile).realize) := by
  classical
  let parentKeep : ∀ c, PositiveWord (A c) (n + m + 1) → Prop :=
    fun c word ↦ (parentProfile c).MatchesEncodedPositiveWord (encode c) word
  let leftKeep : ∀ c, PositiveWord (A c) n → Prop :=
    fun c word ↦ (leftProfile c).MatchesEncodedPositiveWord (encode c) word
  let rightKeep : ∀ c, PositiveWord (A c) m → Prop :=
    fun c word ↦ (rightProfile c).MatchesEncodedPositiveWord (encode c) word
  let regionalKeep : ∀ c, PositiveWord (A c) (n + m + 1) → Prop :=
    fun c word ↦
      leftKeep c ((positiveWordAppendEquiv (A c) n m).symm word).1 ∧
      rightKeep c ((positiveWordAppendEquiv (A c) n m).symm word).2
  let parentSelected :=
    P.selectEncodedCompleteSplitProfiles encode index parentProfile
  let leftSelected :=
    P.selectEncodedCompleteSplitProfiles encode index leftProfile
  let rightSelected :=
    P.selectEncodedCompleteSplitProfiles encode index rightProfile
  let regionalSelected := (P.positivePower (n + m + 1)).select regionalKeep
  have hregional_parent : ∀ c word, regionalKeep c word → parentKeep c word := by
    intro c word hregional
    let pieces := (positiveWordAppendEquiv (A c) n m).symm word
    have happend : positiveWordAppend pieces.1 m pieces.2 = word := by
      rw [← positiveWordAppendEquiv_apply]
      exact (positiveWordAppendEquiv (A c) n m).apply_symm_apply word
    rw [← happend]
    exact CompleteSplitProfile.matchesEncodedPositiveWord_append
      (parentProfile c) (leftProfile c) (rightProfile c) (hcounts c)
      (encode c) pieces.1 pieces.2 hregional.1 hregional.2
  have hparent_select : parentSelected.select regionalKeep = regionalSelected := by
    change
      (((P.positivePower (n + m + 1)).select parentKeep).select regionalKeep) =
        (P.positivePower (n + m + 1)).select regionalKeep
    apply PartitionedTensor.ext
    · apply Finset.ext
      intro address
      rw [PartitionedTensor.mem_select_support,
        PartitionedTensor.mem_select_support,
        PartitionedTensor.mem_select_support]
      constructor
      · rintro ⟨⟨hsupport, _hparent⟩, hregional⟩
        exact ⟨hsupport, hregional⟩
      · rintro ⟨hsupport, hregional⟩
        exact ⟨⟨hsupport, fun c ↦ hregional_parent c (address c) (hregional c)⟩,
          hregional⟩
    · rfl
  have hparent_regional : Restricts parentSelected.realize regionalSelected.realize :=
    (Tensor.Restricts.partitionedSelect parentSelected regionalKeep).trans
      (Tensor.Restricts.of_eq (congrArg PartitionedTensor.realize hparent_select))
  have happend_selected :
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
        regionalSelected := by
    calc
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
          (PartitionedTensor.appendPositiveWordPartitions
            (P.positivePower n) (P.positivePower m)).select regionalKeep := by
            exact PartitionedTensor.appendPositiveWordPartitions_select
              (P.positivePower n) (P.positivePower m) leftKeep rightKeep
      _ = regionalSelected := by
        rw [P.appendPositiveWordPartitions_positivePowers n m]
  have hexternal_append :
      Isomorphic (Tensor.external leftSelected.realize rightSelected.realize)
        (PartitionedTensor.appendPositiveWordPartitions
          leftSelected rightSelected).realize :=
    (Tensor.Isomorphic.partitionedExternal leftSelected rightSelected).trans
      (Tensor.Isomorphic.partitionedReindex
        (leftSelected.external rightSelected)
        (fun c ↦ positiveWordAppendEquiv (A c) n m)
        (positivePowerBlockAppendEquivAt (K := K) (V := V) n m))
  have hregional_external :
      Restricts regionalSelected.realize
        (Tensor.external leftSelected.realize rightSelected.realize) := by
    have hregional_append :
        Isomorphic regionalSelected.realize
          (PartitionedTensor.appendPositiveWordPartitions
            leftSelected rightSelected).realize := by
      rw [happend_selected]
      exact Tensor.Isomorphic.refl regionalSelected.realize
    exact (hregional_append.trans hexternal_append.symm).restricts
  exact hparent_regional.trans hregional_external

/-- The parent multiplicity of a positive binary division, expressed using the predecessor
parameters of the two positive-word regions. -/
theorem ExactInterfaceTermBinaryDivision.parentMultiplicity_eq
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = n + 1)
    (hright : division.rightMultiplicity = m + 1) :
    parent.multiplicity = n + m + 2 := by
  rw [division.multiplicity_eq, hleft, hright]
  omega

/-- Orientation-free binary regional division for exact encoded interface terms.  If both child
multiplicities are positive, the parent selected tensor restricts to the external product of the
two independently selected child tensors. -/
theorem Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (hleft : division.leftMultiplicity = n + 1)
    (hright : division.rightMultiplicity = m + 1) :
    Restricts
      (P.selectEncodedExactInterfaceTerm encode parent
        (division.parentMultiplicity_eq hleft hright)).realize
      (Tensor.external
        (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize
        (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize) := by
  let parentProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + m + 2) :=
    fun c ↦ parent.positivePowerProfile
      (division.parentMultiplicity_eq hleft hright) c
  let leftProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (n + 1) :=
    fun c ↦ division.leftTerm.positivePowerProfile hleft c
  let rightProfile : ∀ c,
      CompleteSplitProfile depth (parent.index.count c) (m + 1) :=
    fun c ↦ division.rightTerm.positivePowerProfile hright c
  have hcounts : ∀ c word,
      (parentProfile c).counts word =
        (leftProfile c).counts word + (rightProfile c).counts word := by
    intro c word
    dsimp [parentProfile, leftProfile, rightProfile,
      ExactInterfaceTermParameters.positivePowerProfile]
    simpa only [CompleteSplitProfile.counts_cast,
      ExactInterfaceTermBinaryDivision.leftTerm_split,
      ExactInterfaceTermBinaryDivision.rightTerm_split] using
        division.split_counts_eq c word
  exact Tensor.Restricts.selectEncodedCompleteSplitProfiles_binaryDivision
    P encode parent.index parentProfile leftProfile rightProfile hcounts

end

end AlgebraicComplexity
