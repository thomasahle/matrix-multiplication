/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibility
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityContainment
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting

set_option autoImplicit false

/-!
# Compatibility on the total-weight quotient of CW complete-split words

This file separates two operations which must not be conflated.

* Compatibility hashing sees only the total weight of each complete-split word.
* At the selected-tensor level, a variable restriction can recover the entire prescribed fine
  type selection.  At the individual-constituent level used below, it selects one prescribed
  fine typed word while preserving the output index and matrix dimensions.

The whole-selected-tensor operation is the interface which can preserve a later fine extraction;
the one-word constituent corollary must not by itself be counted as an additional inner copy
exponent.  At level two the quotient address is its ordered three-leg shape, so a fixed shape type
already determines the full joint quotient type.  This is the rigidity fact which makes the
total-weight quotient simpler than the pair-sorting quotient.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Coarsening native chunks by total weight changes only the partition, not the tensor. -/
theorem cwTotalWeightChunkCoarsening_isomorphic
    (K : Type u) [CommRing K] (q depth : ℕ) :
    Isomorphic (cwChunkPartitionedTensor K q depth).realize
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).realize := by
  exact Tensor.Isomorphic.partitionedCoarsen
    (cwChunkPartitionedTensor K q depth) (cwTotalWeightChunkCoarsening depth)

/-- Total complementation, regarded as an involutive permutation of the quotient alphabet. -/
def cwCoarseDigitComplementPerm (depth : ℕ) : Equiv.Perm (CWCoarseDigit depth) where
  toFun := cwCoarseDigitComplement depth
  invFun := cwCoarseDigitComplement depth
  left_inv := cwCoarseDigitComplement_involutive depth
  right_inv := cwCoarseDigitComplement_involutive depth

@[simp] theorem cwCoarseDigitComplementPerm_apply (depth : ℕ)
    (digit : CWCoarseDigit depth) :
    cwCoarseDigitComplementPerm depth digit = cwCoarseDigitComplement depth digit :=
  rfl

@[simp] theorem cwCoarseDigitComplementPerm_symm (depth : ℕ) :
    (cwCoarseDigitComplementPerm depth).symm = cwCoarseDigitComplementPerm depth :=
  rfl

/-- Push a raw complete-split profile to total weights. -/
noncomputable def cwTotalWeightPushforwardProfile {depth : ℕ}
    (profile : SplitWord depth → ℕ) : CWCoarseDigit depth → ℕ :=
  WordType.mappedType (cwSplitWordTotalDigit depth) profile

/-- Digitwise complement as an involution on raw complete-split words. -/
def cwRawSplitWordComplement (depth : ℕ) : Equiv.Perm (SplitWord depth) where
  toFun := complementSplitWord
  invFun := complementSplitWord
  left_inv := complementSplitWord_complementSplitWord
  right_inv := complementSplitWord_complementSplitWord

@[simp] theorem cwRawSplitWordComplement_apply (depth : ℕ)
    (word : SplitWord depth) :
    cwRawSplitWordComplement depth word = complementSplitWord word :=
  rfl

@[simp] theorem cwRawSplitWordComplement_symm (depth : ℕ) :
    (cwRawSplitWordComplement depth).symm = cwRawSplitWordComplement depth :=
  rfl

/-- Equivariant pushforward of profiles through two involutions. -/
private theorem mappedType_equivariant_of_involutions
    {I J : Type*} [Fintype I] [Fintype J]
    (sourceComplement : Equiv.Perm I) (targetComplement : Equiv.Perm J)
    (hsource : sourceComplement.symm = sourceComplement)
    (htarget : targetComplement.symm = targetComplement)
    (f : I → J)
    (hnatural : ∀ x, f (sourceComplement x) = targetComplement (f x))
    (left right : I → ℕ)
    (hprofile : ∀ x, left x = right (sourceComplement x)) (y : J) :
    WordType.mappedType f left y =
      WordType.mappedType f right (targetComplement y) := by
  classical
  unfold WordType.mappedType WordType.letterFiber
  rw [Finset.sum_filter, Finset.sum_filter]
  have hsourceInv (x : I) : sourceComplement (sourceComplement x) = x := by
    have h := sourceComplement.apply_symm_apply x
    rw [hsource] at h
    exact h
  have htargetInv (x : J) : targetComplement (targetComplement x) = x := by
    have h := targetComplement.apply_symm_apply x
    rw [htarget] at h
    exact h
  calc
    (∑ x, if f x = y then left x else 0) =
        ∑ x, if f (sourceComplement x) = y then
          left (sourceComplement x) else 0 := by
      exact (Equiv.sum_comp sourceComplement
        (fun x ↦ if f x = y then left x else 0)).symm
    _ = ∑ x, if f x = targetComplement y then right x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hprofile, hsourceInv, hnatural]
      have hiff : targetComplement (f x) = y ↔
          f x = targetComplement y := by
        constructor
        · intro h
          calc
            f x = targetComplement (targetComplement (f x)) :=
              (htargetInv (f x)).symm
            _ = targetComplement y := congrArg targetComplement h
        · intro h
          rw [h, htargetInv]
      simp only [hiff]

/-- Push all exact and pooled compatibility targets to the total-weight alphabet. -/
noncomputable def cwTotalWeightPushforwardTargets
    {Part : Type*} {depth : ℕ} (targets : CompatibilityTargets Part depth) :
    FeatureCompatibilityTargets Part (CWCoarseDigit depth) where
  complement := cwCoarseDigitComplementPerm depth
  complement_symm := cwCoarseDigitComplementPerm_symm depth
  xExact q := cwTotalWeightPushforwardProfile (targets.xExact q)
  yExact q := cwTotalWeightPushforwardProfile (targets.yExact q)
  zExact q := cwTotalWeightPushforwardProfile (targets.zExact q)
  yPooled part total := cwTotalWeightPushforwardProfile
    (targets.yPooled part total)
  zPooled part total := cwTotalWeightPushforwardProfile
    (targets.zPooled part total)
  yBoundary q hq symbol := by
    apply mappedType_equivariant_of_involutions
      (cwRawSplitWordComplement depth)
      (cwCoarseDigitComplementPerm depth)
      (cwRawSplitWordComplement_symm depth) (cwCoarseDigitComplementPerm_symm depth)
      (cwSplitWordTotalDigit depth)
    · exact cwSplitWordTotalDigit_complement depth
    · exact targets.yBoundary q hq
  zBoundaryOfX q hq symbol := by
    apply mappedType_equivariant_of_involutions
      (cwRawSplitWordComplement depth)
      (cwCoarseDigitComplementPerm depth)
      (cwRawSplitWordComplement_symm depth) (cwCoarseDigitComplementPerm_symm depth)
      (cwSplitWordTotalDigit depth)
    · exact cwSplitWordTotalDigit_complement depth
    · exact targets.zBoundaryOfX q hq
  zBoundaryOfY q hq symbol := by
    apply mappedType_equivariant_of_involutions
      (cwRawSplitWordComplement depth)
      (cwCoarseDigitComplementPerm depth)
      (cwRawSplitWordComplement_symm depth) (cwCoarseDigitComplementPerm_symm depth)
      (cwSplitWordTotalDigit depth)
    · exact cwSplitWordTotalDigit_complement depth
    · exact targets.zBoundaryOfY q hq

/-! ## Pushed-profile support and containment -/

/-- Raw `Y` weight support descends to the total-weight quotient. -/
theorem cwTotalWeightPushforwardTargets_isYWeightSupported
    {Part : Type*} {depth : ℕ} (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported) :
    (cwTotalWeightPushforwardTargets rawTargets).IsYWeightSupported Fin.val := by
  intro cell symbol hpositive
  cases cell with
  | boundary q =>
      change 0 < WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.yExact q.1) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          (cwSplitWordTotalDigit depth) (rawTargets.yExact q.1) symbol hpositive
      rw [← hrawSymbol]
      exact hsupported.1 q.1 raw hrawPositive
  | pooled part total =>
      change 0 < WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.yPooled part total) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          (cwSplitWordTotalDigit depth) (rawTargets.yPooled part total) symbol hpositive
      rw [← hrawSymbol]
      exact hsupported.2 part total raw hrawPositive

/-- Raw `Z` weight support descends to the total-weight quotient. -/
theorem cwTotalWeightPushforwardTargets_isZWeightSupported
    {Part : Type*} {depth : ℕ} (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported) :
    (cwTotalWeightPushforwardTargets rawTargets).IsZWeightSupported Fin.val := by
  intro cell symbol hpositive
  cases cell with
  | boundary q =>
      change 0 < WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.zExact q.1) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          (cwSplitWordTotalDigit depth) (rawTargets.zExact q.1) symbol hpositive
      rw [← hrawSymbol]
      exact hsupported.1 q.1 raw hrawPositive
  | pooled part total =>
      change 0 < WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.zPooled part total) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          (cwSplitWordTotalDigit depth) (rawTargets.zPooled part total) symbol hpositive
      rw [← hrawSymbol]
      exact hsupported.2 part total raw hrawPositive

/-- All raw weight-support invariants descend to the total-weight feature targets. -/
theorem cwTotalWeightPushforwardTargets_isWeightSupported
    {Part : Type*} {depth : ℕ} (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported) :
    (cwTotalWeightPushforwardTargets rawTargets).IsWeightSupported Fin.val :=
  ⟨cwTotalWeightPushforwardTargets_isYWeightSupported rawTargets hsupported.2.1,
    cwTotalWeightPushforwardTargets_isZWeightSupported rawTargets hsupported.2.2⟩

/-! ## Boundary relations on the actual coarsened support -/

/-- If the total-weight `Z` label is zero, the total-weight `Y` label is the induced complement
of the `X` label.  The proof lifts once to the genuine CW support; it never chooses a persistent
fine representative of a quotient constituent. -/
theorem cwTotalWeightCoarsenedChunkSupport_yBoundary
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c ↦ CWCoarseDigit depth))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support)
    (hz : (address .Z : ℕ) = 0) :
    address .Y = cwCoarseDigitComplementPerm depth (address .X) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwTotalWeightChunkCoarsening depth c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q depth fine hfine
  have hzRaw : splitWordWeight (cwChunkSplitWord depth (fine .Z)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord depth (fine .Z)) =
          (cwTotalWeightChunkCoarsening depth .Z (fine .Z) : ℕ) := rfl
      _ = (address .Z : ℕ) := congrArg Fin.val (hmapAt .Z)
      _ = 0 := hz
  have hzWord : cwChunkSplitWord depth (fine .Z) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hzRaw
  have hyx : cwChunkSplitWord depth (fine .Y) =
      complementSplitWord (cwChunkSplitWord depth (fine .X)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord depth (fine .X) position)
      (cwChunkSplitWord depth (fine .Y) position)
      (cwChunkSplitWord depth (fine .Z) position)
    · exact hlegal position
    · simpa using congrFun hzWord position
  rw [← hmapAt .Y, ← hmapAt .X]
  change cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .Y)) =
    cwCoarseDigitComplement depth
      (cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .X)))
  rw [hyx, cwSplitWordTotalDigit_complement]

/-- If the total-weight `X` label is zero, `Z` is the induced complement of `Y`. -/
theorem cwTotalWeightCoarsenedChunkSupport_zBoundaryOfX
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c ↦ CWCoarseDigit depth))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support)
    (hx : (address .X : ℕ) = 0) :
    address .Z = cwCoarseDigitComplementPerm depth (address .Y) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwTotalWeightChunkCoarsening depth c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q depth fine hfine
  have hxRaw : splitWordWeight (cwChunkSplitWord depth (fine .X)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord depth (fine .X)) =
          (cwTotalWeightChunkCoarsening depth .X (fine .X) : ℕ) := rfl
      _ = (address .X : ℕ) := congrArg Fin.val (hmapAt .X)
      _ = 0 := hx
  have hxWord : cwChunkSplitWord depth (fine .X) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hxRaw
  have hzy : cwChunkSplitWord depth (fine .Z) =
      complementSplitWord (cwChunkSplitWord depth (fine .Y)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord depth (fine .Y) position)
      (cwChunkSplitWord depth (fine .Z) position)
      (cwChunkSplitWord depth (fine .X) position)
    · simpa [add_assoc, add_left_comm, add_comm] using hlegal position
    · simpa using congrFun hxWord position
  rw [← hmapAt .Z, ← hmapAt .Y]
  change cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .Z)) =
    cwCoarseDigitComplement depth
      (cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .Y)))
  rw [hzy, cwSplitWordTotalDigit_complement]

/-- If the total-weight `Y` label is zero, `Z` is the induced complement of `X`. -/
theorem cwTotalWeightCoarsenedChunkSupport_zBoundaryOfY
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : BlockAddress (fun _c ↦ CWCoarseDigit depth))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).support)
    (hy : (address .Y : ℕ) = 0) :
    address .Z = cwCoarseDigitComplementPerm depth (address .X) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwTotalWeightChunkCoarsening depth c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q depth fine hfine
  have hyRaw : splitWordWeight (cwChunkSplitWord depth (fine .Y)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord depth (fine .Y)) =
          (cwTotalWeightChunkCoarsening depth .Y (fine .Y) : ℕ) := rfl
      _ = (address .Y : ℕ) := congrArg Fin.val (hmapAt .Y)
      _ = 0 := hy
  have hyWord : cwChunkSplitWord depth (fine .Y) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hyRaw
  have hzx : cwChunkSplitWord depth (fine .Z) =
      complementSplitWord (cwChunkSplitWord depth (fine .X)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord depth (fine .X) position)
      (cwChunkSplitWord depth (fine .Z) position)
      (cwChunkSplitWord depth (fine .Y) position)
    · simpa [add_assoc, add_left_comm, add_comm] using hlegal position
    · simpa using congrFun hyWord position
  rw [← hmapAt .Z, ← hmapAt .X]
  change cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .Z)) =
    cwCoarseDigitComplement depth
      (cwSplitWordTotalDigit depth (cwChunkSplitWord depth (fine .X)))
  rw [hzx, cwSplitWordTotalDigit_complement]

/-! ## Quotient-feature model and cleanup -/

/-- Compatibility model whose local symbols are total weights. -/
def cwTotalWeightFeatureCompatibilityModel {Part : Type*} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) :
    FeatureCompatibilityModel
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) Part
      (CWCoarseDigit depth) (n + 1) where
  symbols _c word := positiveWordEquiv (CWCoarseDigit depth) n word
  coarse address sample :=
    { part := partAt sample
      x := (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ)
      y := (positiveWordEquiv (CWCoarseDigit depth) n (address .Y) sample : ℕ)
      z := (positiveWordEquiv (CWCoarseDigit depth) n (address .Z) sample : ℕ) }

@[simp] theorem cwTotalWeightFeatureCompatibilityModel_symbols
    {Part : Type*} (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (c : Leg) (word : PositiveWord (CWCoarseDigit depth) n)
    (sample : Fin (n + 1)) :
    (cwTotalWeightFeatureCompatibilityModel depth n partAt).symbols c word sample =
      positiveWordEquiv (CWCoarseDigit depth) n word sample :=
  rfl

/-- For supported targets, a compatible total-weight `Y` label is literally the `Y` word of
the tested quotient constituent. -/
theorem cwTotalWeight_label_eq_Y_of_featureCompatibleY
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (label : PositiveWord (CWCoarseDigit depth) n)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hcompatible :
      (cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
        (cwTotalWeightPushforwardTargets rawTargets) label address) :
    label = address .Y := by
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  apply Fin.ext
  exact FeatureCompatibilityModel.symbolWeight_eq_coarseY_of_featureCompatibleY
    (cwTotalWeightFeatureCompatibilityModel depth n partAt)
    (cwTotalWeightPushforwardTargets rawTargets) Fin.val
    (cwTotalWeightPushforwardTargets_isYWeightSupported rawTargets hsupported)
    label address hcompatible sample

/-- For supported targets, a compatible total-weight `Z` label is literally the `Z` word of
the tested quotient constituent. -/
theorem cwTotalWeight_label_eq_Z_of_featureCompatibleZ
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (label : PositiveWord (CWCoarseDigit depth) n)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hcompatible :
      (cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleZ
        (cwTotalWeightPushforwardTargets rawTargets) label address) :
    label = address .Z := by
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  apply Fin.ext
  exact FeatureCompatibilityModel.symbolWeight_eq_coarseZ_of_featureCompatibleZ
    (cwTotalWeightFeatureCompatibilityModel depth n partAt)
    (cwTotalWeightPushforwardTargets rawTargets) Fin.val
    (cwTotalWeightPushforwardTargets_isZWeightSupported rawTargets hsupported)
    label address hcompatible sample

/-- Actual positive-power support supplies all three boundary relations required by quotient
feature compatibility. -/
theorem cwTotalWeightFeatureCompatibilityModel_boundaryRelations_of_mem_support
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    (cwTotalWeightFeatureCompatibilityModel depth n partAt).HasYBoundaryRelation
        (cwCoarseDigitComplementPerm depth) address ∧
      (cwTotalWeightFeatureCompatibilityModel depth n partAt).HasZBoundaryRelations
        (cwCoarseDigitComplementPerm depth) address := by
  classical
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  obtain ⟨word, hword⟩ :=
    Q.exists_positiveSupportWord_of_mem_positivePower_support n haddress
  have hsample (sample : Fin (n + 1)) (c : Leg) :
      positiveWordEquiv (CWCoarseDigit depth) n (address c) sample =
        (positiveWordEquiv Q.support n word sample).1 c := by
    rw [← hword]
    exact congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress Q.support n word c) sample
  constructor
  · intro sample hz
    let base : Q.support := positiveWordEquiv Q.support n word sample
    have hzBase : (base.1 .Z : ℕ) = 0 := by
      simpa [cwTotalWeightFeatureCompatibilityModel, base,
        hsample sample .Z] using hz
    have hbase := cwTotalWeightCoarsenedChunkSupport_yBoundary
      K q depth base.1 base.2 hzBase
    simpa [cwTotalWeightFeatureCompatibilityModel, base,
      hsample sample .X, hsample sample .Y] using hbase
  · constructor
    · intro sample hx
      let base : Q.support := positiveWordEquiv Q.support n word sample
      have hxBase : (base.1 .X : ℕ) = 0 := by
        simpa [cwTotalWeightFeatureCompatibilityModel, base,
          hsample sample .X] using hx
      have hbase := cwTotalWeightCoarsenedChunkSupport_zBoundaryOfX
        K q depth base.1 base.2 hxBase
      simpa [cwTotalWeightFeatureCompatibilityModel, base,
        hsample sample .Y, hsample sample .Z] using hbase
    · intro sample hy
      let base : Q.support := positiveWordEquiv Q.support n word sample
      have hyBase : (base.1 .Y : ℕ) = 0 := by
        simpa [cwTotalWeightFeatureCompatibilityModel, base,
          hsample sample .Y] using hy
      have hbase := cwTotalWeightCoarsenedChunkSupport_zBoundaryOfY
        K q depth base.1 base.2 hyBase
      simpa [cwTotalWeightFeatureCompatibilityModel, base,
        hsample sample .X, hsample sample .Z] using hbase

/-- Exact `Y/Z` compatibility cleanup on the total-weight quotient alphabet.  Its hypotheses are
exactly the pushed-forward profile equations counted by the quotient evaluator. -/
theorem cwTotalWeightFeatureYZCompatibilityCleanup_to_indexedDirectSum
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
          (cwTotalWeightPushforwardTargets rawTargets)),
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol) :
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  let P := (Q.positivePower n).withSupport ambient
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let targets := cwTotalWeightPushforwardTargets rawTargets
  apply Tensor.Restricts.partitionedFeatureYZCompatibilityCleanup_to_indexedDirectSum
    P hX model targets
  · intro address haddress
    have hboundary :=
      (cwTotalWeightFeatureCompatibilityModel_boundaryRelations_of_mem_support
        K q depth n partAt address (hambient haddress)).1
    exact ⟨hboundary, (hpassesY address haddress).1,
      (hpassesY address haddress).2⟩
  · intro address haddress
    have hambientAddress : address ∈ ambient :=
      compatibilityIsolatedSupport_subset ambient .Y
        (model.FeatureCompatibleY targets) haddress
    have hboundary :=
      (cwTotalWeightFeatureCompatibilityModel_boundaryRelations_of_mem_support
        K q depth n partAt address (hambient hambientAddress)).2
    exact ⟨hboundary, (hpassesZ address haddress).1,
      (hpassesZ address haddress).2.1,
      (hpassesZ address haddress).2.2⟩

/-! ## Exact finite count -/

/-- `Y` compatibility on total-weight quotient words. -/
abbrev cwTotalWeightCompatibilityY
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth) :=
  (cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
    (cwTotalWeightPushforwardTargets rawTargets)

/-- `Z` compatibility on total-weight quotient words. -/
abbrev cwTotalWeightCompatibilityZ
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth) :=
  (cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleZ
    (cwTotalWeightPushforwardTargets rawTargets)

/-- Support remaining after total-weight quotient `Y` compatibility isolation. -/
noncomputable def cwTotalWeightYIsolatedSupport
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) :=
  compatibilityIsolatedSupport ambient .Y
    (cwTotalWeightCompatibilityY depth n partAt rawTargets)

/-- Support remaining after both total-weight quotient compatibility passes. -/
noncomputable def cwTotalWeightYZIsolatedSupport
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) :=
  compatibilityIsolatedSupport
    (cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient) .Z
    (cwTotalWeightCompatibilityZ depth n partAt rawTargets)

/-- Directed `Y` competitor incidence for the total-weight quotient. -/
noncomputable def cwTotalWeightYCompetitorIncidence
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) : ℕ :=
  compatibilityCompetitorIncidence ambient .Y
    (cwTotalWeightCompatibilityY depth n partAt rawTargets)

/-- Directed `Z` competitor incidence after the total-weight `Y` pass. -/
noncomputable def cwTotalWeightZCompetitorIncidence
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) : ℕ :=
  compatibilityCompetitorIncidence
    (cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient) .Z
    (cwTotalWeightCompatibilityZ depth n partAt rawTargets)

/-- Exact union-bound count for the two quotient compatibility passes.  A subsequent
method-of-types theorem only has to bound the two displayed incidence terms. -/
theorem cwTotalWeight_card_ambient_le_card_YZIsolatedSupport_add_incidences
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) :
    ambient.card ≤
      (cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient).card +
        cwTotalWeightYCompetitorIncidence depth n partAt rawTargets ambient +
        cwTotalWeightZCompetitorIncidence depth n partAt rawTargets ambient := by
  simpa only [cwTotalWeightYZIsolatedSupport, cwTotalWeightYIsolatedSupport,
    cwTotalWeightYCompetitorIncidence, cwTotalWeightZCompetitorIncidence] using
    (card_le_card_YZCompatibilityIsolatedSupport_add_incidences
      ambient (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets))

/-- If certified incidence budgets consume at most half of the ambient quotient family, at
least half the quotient constituents survive. -/
theorem cwTotalWeight_card_ambient_le_two_mul_card_YZIsolatedSupport
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (budgetY budgetZ : ℕ)
    (hbudgetY : cwTotalWeightYCompetitorIncidence
      depth n partAt rawTargets ambient ≤ budgetY)
    (hbudgetZ : cwTotalWeightZCompetitorIncidence
      depth n partAt rawTargets ambient ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ ambient.card) :
    ambient.card ≤
      2 * (cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets ambient).card := by
  simpa only [cwTotalWeightYZIsolatedSupport, cwTotalWeightYIsolatedSupport,
    cwTotalWeightYCompetitorIncidence, cwTotalWeightZCompetitorIncidence] using
    (card_le_two_mul_card_YZCompatibilityIsolatedSupport
      ambient (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
      budgetY budgetZ hbudgetY hbudgetZ hhalf)

/-! ## Whole quotient constituent to the original fine typed leaf -/

/-- End-to-end finite semantic bridge for the total-weight quotient.

Compatibility is counted entirely on total-weight feature words.  Every retained output is a
whole quotient constituent.  The `hshape` premise says that its exact ordered-shape type is the
pushforward of the intended fine joint type; injectivity of the total-weight shape on quotient
support then recovers the full quotient joint type.  The output index and all three matrix
dimensions are unchanged.  This theorem returns one fine typed word per quotient constituent;
any nonzero inner copy exponent must be supplied by a separate nested extraction theorem. -/
theorem cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
          (cwTotalWeightPushforwardTargets rawTargets)),
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    {k : ℕ}
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (n + 1))
    (hshape : ∀ address : cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets ambient,
      ∃ coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n,
        positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n coarseWord = address.1 ∧
          WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.multiplicity
                (positiveWordEquiv
                  (CWTotalWeightCoarseSupport K q depth) n coarseWord)) =
            WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.mappedType
                ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
                  (cwTotalWeightChunkCoarsening depth))
                (WordType.proportionalCounts leaf.profile.count k))) :
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum (fun _address : zSupport ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  classical
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  let P := (Q.positivePower n).withSupport ambient
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let targets := cwTotalWeightPushforwardTargets rawTargets
  let ySupport := compatibilityIsolatedSupport ambient .Y
    (model.FeatureCompatibleY targets)
  let zSupport := compatibilityIsolatedSupport ySupport .Z
    (model.FeatureCompatibleZ targets)
  have hcleanup : Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
    simpa [Q, P, model, targets, ySupport, zSupport,
      cwTotalWeightYZIsolatedSupport, cwTotalWeightYIsolatedSupport,
      cwTotalWeightCompatibilityY, cwTotalWeightCompatibilityZ] using
      cwTotalWeightFeatureYZCompatibilityCleanup_to_indexedDirectSum
        K q depth n partAt rawTargets ambient hambient hX hpassesY hpassesZ
  apply hcleanup.trans
  apply Restricts.indexedDirectSum
  intro address
  obtain ⟨coarseWord, hword, hwordShape⟩ := hshape address
  have hleaf :=
    cwTotalWeight_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeType
      K q depth leaf hdimension coarseWord hlegal hwordShape
  change Restricts ((Q.positivePower n).constituent address.1) _
  rw [← hword]
  exact hleaf

end AlgebraicComplexity.Examples
