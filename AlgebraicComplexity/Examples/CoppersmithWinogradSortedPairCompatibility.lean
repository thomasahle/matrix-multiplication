/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibility
import AlgebraicComplexity.Tensor.HoleRepair

/-!
# Compatibility cleanup and hole repair for the sorted-pair CW quotient

The globally uniform quotient `cwSortedPairChunkCoarsening` sorts each two-digit complete-split
word.  Sorting is noninjective, so compatibility cannot be justified by choosing arbitrary fine
representatives of a quotient label.  This module instead proves the required boundary relations
directly on the support of the coarsened Coppersmith--Winograd tensor.

On the full feature type, the induced complement is the genuine involution
`(a, b) ↦ (rev b, rev a)`.  Its restriction to sorted outputs agrees with sorting the raw
digitwise complement.  Consequently the generic quotient-feature cleanup theorem applies to
arbitrary sample multiplicity and arbitrary region map `partAt`.  The final theorem specializes
the exact eight-way hole-repair identity to the quotient-word alphabet.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- Complement a sorted-pair feature by complementing its digits and reversing their order. -/
def cwSortedPairComplement : Equiv.Perm (SplitWord 1) where
  toFun word position := Fin.rev (word (Fin.rev position))
  invFun word position := Fin.rev (word (Fin.rev position))
  left_inv word := by
    funext position
    simp
  right_inv word := by
    funext position
    simp

@[simp] theorem cwSortedPairComplement_apply (word : SplitWord 1)
    (position : Fin 2) :
    cwSortedPairComplement word position = Fin.rev (word (Fin.rev position)) :=
  rfl

@[simp] theorem cwSortedPairComplement_symm :
    cwSortedPairComplement.symm = cwSortedPairComplement :=
  rfl

theorem cwSortedPairSplitWord_complement (word : SplitWord 1) :
    cwSortedPairSplitWord (complementSplitWord word) =
      cwSortedPairComplement (cwSortedPairSplitWord word) := by
  revert word
  decide

open scoped BigOperators

theorem mappedType_equivariant
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
        (fun x => if f x = y then left x else 0)).symm
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

def cwRawPairComplement : Equiv.Perm (SplitWord 1) where
  toFun := complementSplitWord
  invFun := complementSplitWord
  left_inv := complementSplitWord_complementSplitWord
  right_inv := complementSplitWord_complementSplitWord

@[simp] theorem cwRawPairComplement_apply (word : SplitWord 1) :
    cwRawPairComplement word = complementSplitWord word :=
  rfl

@[simp] theorem cwRawPairComplement_symm :
    cwRawPairComplement.symm = cwRawPairComplement :=
  rfl

noncomputable def cwSortedPairPushforwardProfile
    (profile : SplitWord 1 → ℕ) : SplitWord 1 → ℕ :=
  WordType.mappedType cwSortedPairSplitWord profile

noncomputable def cwSortedPairPushforwardTargets
    {Part : Type*} (targets : CompatibilityTargets Part 1) :
    FeatureCompatibilityTargets Part (SplitWord 1) where
  complement := cwSortedPairComplement
  complement_symm := cwSortedPairComplement_symm
  xExact q := cwSortedPairPushforwardProfile (targets.xExact q)
  yExact q := cwSortedPairPushforwardProfile (targets.yExact q)
  zExact q := cwSortedPairPushforwardProfile (targets.zExact q)
  yPooled part total := cwSortedPairPushforwardProfile
    (targets.yPooled part total)
  zPooled part total := cwSortedPairPushforwardProfile
    (targets.zPooled part total)
  yBoundary q hq symbol := by
    apply mappedType_equivariant cwRawPairComplement cwSortedPairComplement
      cwRawPairComplement_symm cwSortedPairComplement_symm
      cwSortedPairSplitWord
    · exact cwSortedPairSplitWord_complement
    · exact targets.yBoundary q hq
  zBoundaryOfX q hq symbol := by
    apply mappedType_equivariant cwRawPairComplement cwSortedPairComplement
      cwRawPairComplement_symm cwSortedPairComplement_symm
      cwSortedPairSplitWord
    · exact cwSortedPairSplitWord_complement
    · exact targets.zBoundaryOfX q hq
  zBoundaryOfY q hq symbol := by
    apply mappedType_equivariant cwRawPairComplement cwSortedPairComplement
      cwRawPairComplement_symm cwSortedPairComplement_symm
      cwSortedPairSplitWord
    · exact cwSortedPairSplitWord_complement
    · exact targets.zBoundaryOfY q hq

theorem cwSortedPairCoarsenedChunkSupport_yBoundary
    (K : Type*) [CommRing K] (q : ℕ)
    (address : BlockAddress (fun _c ↦ SplitWord 1))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support)
    (hz : splitWordWeight (address .Z) = 0) :
    address .Y = cwSortedPairComplement (address .X) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwSortedPairChunkCoarsening c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q 1 fine hfine
  have hzRaw : splitWordWeight (cwChunkSplitWord 1 (fine .Z)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord 1 (fine .Z)) =
          splitWordWeight (cwSortedPairChunkCoarsening .Z (fine .Z)) :=
        (cwSortedPairChunkCoarsening_total .Z (fine .Z)).symm
      _ = splitWordWeight (address .Z) := congrArg splitWordWeight (hmapAt .Z)
      _ = 0 := hz
  have hzWord : cwChunkSplitWord 1 (fine .Z) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hzRaw
  have hyx : cwChunkSplitWord 1 (fine .Y) =
      complementSplitWord (cwChunkSplitWord 1 (fine .X)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord 1 (fine .X) position)
      (cwChunkSplitWord 1 (fine .Y) position)
      (cwChunkSplitWord 1 (fine .Z) position)
    · exact hlegal position
    · simpa using congrFun hzWord position
  rw [← hmapAt .Y, ← hmapAt .X]
  change cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .Y)) =
    cwSortedPairComplement
      (cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .X)))
  rw [hyx, cwSortedPairSplitWord_complement]

theorem cwSortedPairCoarsenedChunkSupport_zBoundaryOfX
    (K : Type*) [CommRing K] (q : ℕ)
    (address : BlockAddress (fun _c ↦ SplitWord 1))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support)
    (hx : splitWordWeight (address .X) = 0) :
    address .Z = cwSortedPairComplement (address .Y) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwSortedPairChunkCoarsening c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q 1 fine hfine
  have hxRaw : splitWordWeight (cwChunkSplitWord 1 (fine .X)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord 1 (fine .X)) =
          splitWordWeight (cwSortedPairChunkCoarsening .X (fine .X)) :=
        (cwSortedPairChunkCoarsening_total .X (fine .X)).symm
      _ = splitWordWeight (address .X) := congrArg splitWordWeight (hmapAt .X)
      _ = 0 := hx
  have hxWord : cwChunkSplitWord 1 (fine .X) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hxRaw
  have hzy : cwChunkSplitWord 1 (fine .Z) =
      complementSplitWord (cwChunkSplitWord 1 (fine .Y)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord 1 (fine .Y) position)
      (cwChunkSplitWord 1 (fine .Z) position)
      (cwChunkSplitWord 1 (fine .X) position)
    · simpa [add_assoc, add_left_comm, add_comm] using hlegal position
    · simpa using congrFun hxWord position
  rw [← hmapAt .Z, ← hmapAt .Y]
  change cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .Z)) =
    cwSortedPairComplement
      (cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .Y)))
  rw [hzy, cwSortedPairSplitWord_complement]

theorem cwSortedPairCoarsenedChunkSupport_zBoundaryOfY
    (K : Type*) [CommRing K] (q : ℕ)
    (address : BlockAddress (fun _c ↦ SplitWord 1))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support)
    (hy : splitWordWeight (address .Y) = 0) :
    address .Z = cwSortedPairComplement (address .X) := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwSortedPairChunkCoarsening c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    K q 1 fine hfine
  have hyRaw : splitWordWeight (cwChunkSplitWord 1 (fine .Y)) = 0 := by
    calc
      splitWordWeight (cwChunkSplitWord 1 (fine .Y)) =
          splitWordWeight (cwSortedPairChunkCoarsening .Y (fine .Y)) :=
        (cwSortedPairChunkCoarsening_total .Y (fine .Y)).symm
      _ = splitWordWeight (address .Y) := congrArg splitWordWeight (hmapAt .Y)
      _ = 0 := hy
  have hyWord : cwChunkSplitWord 1 (fine .Y) = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hyRaw
  have hzx : cwChunkSplitWord 1 (fine .Z) =
      complementSplitWord (cwChunkSplitWord 1 (fine .X)) := by
    funext position
    apply splitDigit_eq_rev_of_legal_of_right_eq_zero
      (cwChunkSplitWord 1 (fine .X) position)
      (cwChunkSplitWord 1 (fine .Z) position)
      (cwChunkSplitWord 1 (fine .Y) position)
    · simpa [add_assoc, add_left_comm, add_comm] using hlegal position
    · simpa using congrFun hyWord position
  rw [← hmapAt .Z, ← hmapAt .X]
  change cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .Z)) =
    cwSortedPairComplement
      (cwSortedPairSplitWord (cwChunkSplitWord 1 (fine .X)))
  rw [hzx, cwSortedPairSplitWord_complement]

/-- Compatibility model on positive words of pair-sorted quotient labels. -/
def cwSortedPairFeatureCompatibilityModel {Part : Type*} (n : ℕ)
    (partAt : Fin (n + 1) → Part) :
    FeatureCompatibilityModel
      (fun _c ↦ PositiveWord (SplitWord 1) n) Part (SplitWord 1) (n + 1) where
  symbols _c word := positiveWordEquiv (SplitWord 1) n word
  coarse address sample :=
    { part := partAt sample
      x := splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .X) sample)
      y := splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Y) sample)
      z := splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Z) sample) }

@[simp] theorem cwSortedPairFeatureCompatibilityModel_symbols
    {Part : Type*} (n : ℕ) (partAt : Fin (n + 1) → Part)
    (c : Leg) (word : PositiveWord (SplitWord 1) n) (sample : Fin (n + 1)) :
    (cwSortedPairFeatureCompatibilityModel n partAt).symbols c word sample =
      positiveWordEquiv (SplitWord 1) n word sample :=
  rfl

theorem cwSortedPairFeatureCompatibilityModel_boundaryRelations_of_mem_support
    (K : Type*) [CommRing K] (q n : ℕ)
    {Part : Type*} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    (cwSortedPairFeatureCompatibilityModel n partAt).HasYBoundaryRelation
        cwSortedPairComplement address ∧
      (cwSortedPairFeatureCompatibilityModel n partAt).HasZBoundaryRelations
        cwSortedPairComplement address := by
  classical
  let Q := (cwChunkPartitionedTensor K q 1).coarsen
    cwSortedPairChunkCoarsening
  obtain ⟨word, hword⟩ :=
    Q.exists_positiveSupportWord_of_mem_positivePower_support n haddress
  have hsample (sample : Fin (n + 1)) (c : Leg) :
      positiveWordEquiv (SplitWord 1) n (address c) sample =
        (positiveWordEquiv Q.support n word sample).1 c := by
    rw [← hword]
    exact congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress Q.support n word c) sample
  constructor
  · intro sample hz
    let base : Q.support := positiveWordEquiv Q.support n word sample
    have hzBase : splitWordWeight (base.1 .Z) = 0 := by
      simpa [cwSortedPairFeatureCompatibilityModel, base, hsample sample .Z] using hz
    have hbase := cwSortedPairCoarsenedChunkSupport_yBoundary
      K q base.1 base.2 hzBase
    simpa [cwSortedPairFeatureCompatibilityModel, base,
      hsample sample .X, hsample sample .Y] using hbase
  · constructor
    · intro sample hx
      let base : Q.support := positiveWordEquiv Q.support n word sample
      have hxBase : splitWordWeight (base.1 .X) = 0 := by
        simpa [cwSortedPairFeatureCompatibilityModel, base,
          hsample sample .X] using hx
      have hbase := cwSortedPairCoarsenedChunkSupport_zBoundaryOfX
        K q base.1 base.2 hxBase
      simpa [cwSortedPairFeatureCompatibilityModel, base,
        hsample sample .Y, hsample sample .Z] using hbase
    · intro sample hy
      let base : Q.support := positiveWordEquiv Q.support n word sample
      have hyBase : splitWordWeight (base.1 .Y) = 0 := by
        simpa [cwSortedPairFeatureCompatibilityModel, base,
          hsample sample .Y] using hy
      have hbase := cwSortedPairCoarsenedChunkSupport_zBoundaryOfY
        K q base.1 base.2 hyBase
      simpa [cwSortedPairFeatureCompatibilityModel, base,
        hsample sample .X, hsample sample .Z] using hbase

/-- Concrete quotient-feature compatibility cleanup on the pair-sorted level-two CW alphabet.
The only client hypotheses are the exact and pooled profile equations enforced by the two first
zero-outs; all boundary-complement facts follow from actual coarsened support membership. -/
theorem cwSortedPairFeatureYZCompatibilityCleanup_to_indexedDirectSum
    (K : Type*) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
          (cwSortedPairPushforwardTargets rawTargets)),
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol) :
    let Q := (cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening
    let P := (Q.positivePower n).withSupport ambient
    let model := cwSortedPairFeatureCompatibilityModel n partAt
    let targets := cwSortedPairPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  let Q := (cwChunkPartitionedTensor K q 1).coarsen
    cwSortedPairChunkCoarsening
  let P := (Q.positivePower n).withSupport ambient
  let model := cwSortedPairFeatureCompatibilityModel n partAt
  let targets := cwSortedPairPushforwardTargets rawTargets
  apply Tensor.Restricts.partitionedFeatureYZCompatibilityCleanup_to_indexedDirectSum
    P hX model targets
  · intro address haddress
    have hboundary :=
      (cwSortedPairFeatureCompatibilityModel_boundaryRelations_of_mem_support
        K q n partAt address (hambient haddress)).1
    exact ⟨hboundary, (hpassesY address haddress).1,
      (hpassesY address haddress).2⟩
  · intro address haddress
    have hambientAddress : address ∈ ambient :=
      compatibilityIsolatedSupport_subset ambient .Y
        (model.FeatureCompatibleY targets) haddress
    have hboundary :=
      (cwSortedPairFeatureCompatibilityModel_boundaryRelations_of_mem_support
        K q n partAt address (hambient hambientAddress)).2
    exact ⟨hboundary, (hpassesZ address haddress).1,
      (hpassesZ address haddress).2.1,
      (hpassesZ address haddress).2.2⟩

/-- The exact eight-way hole-repair identity specialized to the globally pair-sorted quotient
alphabet.  In particular, the repair labels are the quotient words themselves; no choice of a
fine representative or context-dependent complement map enters this statement. -/
theorem cwSortedPairPositivePower_indexedDirectSum_splitBoxes_to_box
    (K : Type*) [CommRing K] (q n : ℕ)
    {Source : (Leg → Bool) → Leg → Type*}
    [∀ mask c, AddCommMonoid (Source mask c)]
    [∀ mask c, Module K (Source mask c)]
    (target holes : ∀ _c, Finset (PositiveWord (SplitWord 1) n))
    (input : ∀ mask, Tensor3 K (Source mask))
    (hbox : ∀ mask, Restricts (input mask)
      (((((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).box
          (splitBoxParts target holes mask)).realize)) :
    Restricts (Tensor.indexedDirectSum input)
      (((((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).box target).realize) := by
  exact Tensor.Restricts.indexedDirectSum_splitBoxes_to_box
    (((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).positivePower n)
    target holes input hbox

end AlgebraicComplexity.Examples
