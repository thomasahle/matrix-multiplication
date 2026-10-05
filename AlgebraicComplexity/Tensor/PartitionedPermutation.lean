/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned

/-!
# Permuting the legs of a partitioned tensor

An orientation permutes not only an ordinary three-legged tensor, but also the block-label family,
the block spaces, every supported address, and each typed constituent of a partition certificate.
This module packages that transport and proves that realization commutes with it exactly.

The construction is useful whenever several cyclic copies of one structured tensor are combined,
notably matrix-multiplication symmetrization and Strassen's C-tensor calculus.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Block labels after permuting the tensor legs by `e`. -/
abbrev PermutedBlockIndex (e : Orientation) (A : Leg → Type w) (c : Leg) :=
  A (e.symm c)

/-- Block spaces after permuting the tensor legs by `e`. -/
abbrev PermutedBlockSpace (e : Orientation) (V : ∀ c, A c → Type v)
    (c : Leg) (a : PermutedBlockIndex e A c) :=
  V (e.symm c) a

/-- Permute all three labels of a full block address. -/
def permuteBlockAddress (e : Orientation) :
    BlockAddress A ≃ BlockAddress (PermutedBlockIndex e A) :=
  Equiv.piCongrLeft' A e

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Reading a permuted address at leg `c` reads the original address at `e⁻¹(c)`. -/
@[simp] theorem permuteBlockAddress_apply
    (e : Orientation) (s : BlockAddress A) (c : Leg) :
    permuteBlockAddress e s c = s (e.symm c) :=
  Equiv.piCongrLeft'_apply A e s c

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Pulling a target address back and then reading it at `e⁻¹(c)` recovers its label at `c`.
This is the dependent form of the expected inverse-address formula. -/
@[simp] theorem permuteBlockAddress_symm_apply_apply
    (e : Orientation) (s : BlockAddress (PermutedBlockIndex e A)) (c : Leg) :
    (permuteBlockAddress e).symm s (e.symm c) = s c :=
  Equiv.piCongrLeft'_symm_apply_apply A e s c

/-- Cast the local source block obtained from an inverse address transport to the corresponding
target block. -/
noncomputable def permuteBlockSpaceCast (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e A)) (c : Leg) :
    V (e.symm c) ((permuteBlockAddress e).symm s (e.symm c)) ≃ₗ[K]
      V (e.symm c) (s c) :=
  LinearEquiv.cast (R := K) (permuteBlockAddress_symm_apply_apply e s c)

private theorem directSumLof_comp_cast
    {ι : Type w} [DecidableEq ι]
    (M : ι → Type v) [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    {a b : ι} (h : a = b) :
    (DirectSum.lof K ι M b).comp (LinearEquiv.cast (R := K) h).toLinearMap =
      DirectSum.lof K ι M a := by
  subst b
  rfl

omit [∀ c, Fintype (A c)] in
/-- Including a transported local block into the permuted ambient direct sum cancels the
dependent cast used to identify its block label. -/
theorem blockInclude_comp_permuteBlockSpaceCast
    (e : Orientation) (s : BlockAddress (PermutedBlockIndex e A)) (c : Leg) :
    (blockInclude (K := K) (V := PermutedBlockSpace e V) s c).comp
      (permuteBlockSpaceCast (K := K) (V := V) e s c).toLinearMap =
      blockInclude (K := K) (V := V) ((permuteBlockAddress e).symm s) (e.symm c) := by
  exact directSumLof_comp_cast
    (K := K) (M := fun a ↦ V (e.symm c) a)
    (permuteBlockAddress_symm_apply_apply e s c)

/-- Transport a partition certificate through a permutation of its three tensor legs. -/
noncomputable def PartitionedTensor.permute
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    PartitionedTensor (K := K) (A := PermutedBlockIndex e A)
      (PermutedBlockSpace e V) where
  support := P.support.map (permuteBlockAddress e).toEmbedding
  constituent s :=
    map (fun c ↦ (permuteBlockSpaceCast (K := K) (V := V) e s c).toLinearMap)
      (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm s)))

/-- The support of a leg-permuted partition is the pointwise permutation of its source support. -/
@[simp] theorem PartitionedTensor.permute_support
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    (P.permute e).support = P.support.map (permuteBlockAddress e).toEmbedding := rfl

/-- Membership in a permuted support is membership of the inverse-transported address in the
source support. -/
@[simp] theorem PartitionedTensor.mem_permute_support
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e A)) :
    s ∈ (P.permute e).support ↔ (permuteBlockAddress e).symm s ∈ P.support := by
  classical
  simp [PartitionedTensor.permute]

/-- A constituent of a leg-permuted partition is the corresponding permuted source constituent. -/
@[simp] theorem PartitionedTensor.permute_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e A)) :
    (P.permute e).constituent s =
      map (fun c ↦ (permuteBlockSpaceCast (K := K) (V := V) e s c).toLinearMap)
        (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm s))) := rfl

/-- At any target address, embedding its transported constituent is the leg permutation of the
embedded constituent at the inverse source address. -/
theorem PartitionedTensor.map_blockInclude_permute_constituent_target
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : Orientation) (s : BlockAddress (PermutedBlockIndex e A)) :
    map (blockInclude (K := K) (V := PermutedBlockSpace e V) s)
        ((P.permute e).constituent s) =
      Tensor.permute e
        (map (blockInclude (K := K) (V := V) ((permuteBlockAddress e).symm s))
          (P.constituent ((permuteBlockAddress e).symm s))) := by
  rw [PartitionedTensor.permute_constituent]
  change
    (map (blockInclude (K := K) (V := PermutedBlockSpace e V) s) ∘ₗ
      map (fun c ↦
        (permuteBlockSpaceCast (K := K) (V := V) e s c).toLinearMap))
        (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm s))) = _
  rw [← map_comp]
  simp_rw [blockInclude_comp_permuteBlockSpaceCast]
  exact PiTensorProduct.map_reindex
    (blockInclude (K := K) (V := V) ((permuteBlockAddress e).symm s)) e
    (P.constituent ((permuteBlockAddress e).symm s))

/-- One forward-transported constituent, included at its permuted block address, is exactly the
leg permutation of the original embedded constituent. -/
theorem PartitionedTensor.map_blockInclude_permute_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : Orientation) (s : BlockAddress A) :
    map (blockInclude (K := K) (V := PermutedBlockSpace e V)
        (permuteBlockAddress e s))
        ((P.permute e).constituent (permuteBlockAddress e s)) =
      Tensor.permute e
        (map (blockInclude (K := K) (V := V) s) (P.constituent s)) := by
  rw [P.map_blockInclude_permute_constituent_target e (permuteBlockAddress e s)]
  exact congrArg (fun T ↦ Tensor.permute e T)
    (congrArg
      (fun source ↦ map (blockInclude (K := K) (V := V) source) (P.constituent source))
      (Equiv.symm_apply_apply (permuteBlockAddress e) s))

/-- Realizing a partition certificate commutes exactly with permuting its tensor legs. -/
theorem PartitionedTensor.permute_realize
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    (P.permute e).realize = Tensor.permute e P.realize := by
  classical
  unfold PartitionedTensor.realize realizePartition PartitionedTensor.permute
  rw [map_sum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s hs
  exact P.map_blockInclude_permute_constituent e s

namespace Isomorphic

/-- Relation-level form: the realization of the permuted certificate is the leg permutation of
the original realization, with no change of coordinates beyond the canonical reindexing. -/
theorem partitionedPermute
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    Isomorphic (Tensor.permute e P.realize) (P.permute e).realize := by
  refine ⟨fun _ ↦ LinearEquiv.refl K _, ?_⟩
  change Tensor.map (fun _ ↦ LinearMap.id) (Tensor.permute e P.realize) =
    (P.permute e).realize
  rw [map_id]
  exact (P.permute_realize e).symm

end Isomorphic

end AlgebraicComplexity.Tensor
