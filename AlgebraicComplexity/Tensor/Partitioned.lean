/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCore
import AlgebraicComplexity.Tensor.Restriction
import Mathlib.Algebra.DirectSum.Module

/-!
# Partitioned tensors and variable zeroing

A partitioned tensor is stored as a finite family of typed constituents, each embedded into one
block on every leg.  This certificate-oriented representation makes the support decomposition
part of the data and keeps its realization as an ordinary `Tensor3`.  It is designed to support
laser-method clients without coupling the foundational tensor API to a particular coordinate
basis or optimization format.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Ambient leg spaces obtained by summing all blocks on each leg. -/
abbrev PartitionedSpace (K : Type u) [CommSemiring K]
    (V : ∀ c, A c → Type v)
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)] (c : Leg) :=
  ⨁ a, V c a

/-- Include the three spaces at one block address into the ambient partitioned spaces. -/
noncomputable def blockInclude (s : BlockAddress A) :
    ∀ c, V c (s c) →ₗ[K] PartitionedSpace K V c := by
  classical
  exact fun c ↦ DirectSum.lof K (A c) (V c) (s c)

/-- Realize finitely many typed constituents as one tensor in the partitioned ambient spaces. -/
noncomputable def realizePartition
    (support : Finset (BlockAddress A))
    (constituent : ∀ s : BlockAddress A, Tensor3 K (fun c ↦ V c (s c))) :
    Tensor3 K (PartitionedSpace K V) :=
  ∑ s ∈ support, map (blockInclude (K := K) (V := V) s) (constituent s)

namespace PartitionedTensor

/-- Forget the decomposition and obtain the represented ordinary tensor. -/
noncomputable def realize (P : PartitionedTensor (K := K) (A := A) V) :
    Tensor3 K (PartitionedSpace K V) :=
  realizePartition P.support P.constituent

/-- Two partition certificates realize the same tensor when they have the same finite support
and agree on every supported constituent.  Values of `constituent` away from the support are
deliberately irrelevant. -/
theorem realize_eq_of_support_eq
    (P Q : PartitionedTensor (K := K) (A := A) V)
    (hsupport : P.support = Q.support)
    (hconstituent : ∀ address ∈ P.support,
      P.constituent address = Q.constituent address) :
    P.realize = Q.realize := by
  classical
  unfold realize realizePartition
  rw [hsupport]
  apply Finset.sum_congr rfl
  intro address haddress
  rw [hconstituent address (hsupport ▸ haddress)]

end PartitionedTensor

/-- The block-diagonal linear map that keeps selected blocks and zeros all others. -/
def blockFilter (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    ∀ c, PartitionedSpace K V c →ₗ[K] PartitionedSpace K V c :=
  fun c ↦ DirectSum.lmap fun a ↦
    if keep c a then LinearMap.id else 0

omit [∀ c, Fintype (A c)] in
private theorem blockFilter_comp_blockInclude_of_keep
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (s : BlockAddress A) {c : Leg} (hc : keep c (s c)) :
    blockFilter (K := K) (V := V) keep c ∘ₗ blockInclude (K := K) (V := V) s c =
      blockInclude (K := K) (V := V) s c := by
  ext x
  simp [blockFilter, blockInclude, hc]

omit [∀ c, Fintype (A c)] in
private theorem blockFilter_comp_blockInclude_of_not_keep
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (s : BlockAddress A) {c : Leg} (hc : ¬keep c (s c)) :
    blockFilter (K := K) (V := V) keep c ∘ₗ blockInclude (K := K) (V := V) s c = 0 := by
  ext x
  simp [blockFilter, blockInclude, hc]

omit [∀ c, Fintype (A c)] in
/-- Filtering one embedded constituent either keeps it unchanged or annihilates it. -/
theorem map_blockFilter_block
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (s : BlockAddress A) (T : Tensor3 K (fun c ↦ V c (s c))) :
    map (blockFilter (K := K) (V := V) keep)
        (map (blockInclude (K := K) (V := V) s) T) =
      if ∀ c, keep c (s c) then map (blockInclude (K := K) (V := V) s) T else 0 := by
  classical
  change (map (blockFilter (K := K) (V := V) keep) ∘ₗ
      map (blockInclude (K := K) (V := V) s)) T = _
  rw [← map_comp]
  by_cases hs : ∀ c, keep c (s c)
  · rw [if_pos hs]
    congr 1
    congr 1
    funext c
    exact blockFilter_comp_blockInclude_of_keep keep s (hs c)
  · rw [if_neg hs]
    push Not at hs
    rcases hs with ⟨c, hc⟩
    apply map_eq_zero_of_coord _ T c
    exact blockFilter_comp_blockInclude_of_not_keep keep s hc

/-- Semantic zeroing theorem: a block filter realizes exactly the selected partitioned tensor. -/
theorem map_blockFilter_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    map (blockFilter (K := K) (V := V) keep) P.realize = (P.select keep).realize := by
  classical
  unfold PartitionedTensor.realize realizePartition PartitionedTensor.select
  rw [map_sum]
  simp_rw [map_blockFilter_block]
  rw [Finset.sum_filter]

namespace Restricts

/-- Variable zeroing is an exact tensor restriction. -/
theorem partitionedSelect
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    Restricts P.realize (P.select keep).realize :=
  ⟨blockFilter (K := K) (V := V) keep, map_blockFilter_realize P keep⟩

end Restricts

end AlgebraicComplexity.Tensor
