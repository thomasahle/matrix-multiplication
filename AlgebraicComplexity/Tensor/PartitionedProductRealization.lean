/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductCore
import AlgebraicComplexity.Tensor.Partitioned
import AlgebraicComplexity.Tensor.Product
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Direct-sum realization of partitioned external products

The Cartesian-product partition realizes the ordinary external tensor product through the
canonical equivalence distributing tensor products over finite module direct sums.  Commutation
and block-reindexing laws live separately in `Tensor.PartitionedProductReindex`.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Distribute the tensor product of two partitioned ambient spaces into the direct sum of all
pairs of blocks, independently on every leg. -/
noncomputable def partitionExternalEquiv : ∀ c,
    TensorProduct K (PartitionedSpace K V c) (PartitionedSpace K W c) ≃ₗ[K]
      PartitionedSpace K (ProductBlockSpace K V W) c := by
  classical
  exact fun c ↦ TensorProduct.directSum K K (fun a ↦ V c a) (fun b ↦ W c b)

private theorem directSum_lof_apply_decidableEq_irrel
    {R α : Type*} [Semiring R] {M : α → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (d₁ d₂ : DecidableEq α) (i : α) (z : M i) :
    (@DirectSum.lof R _ α M _ _ d₁ i) z =
      (@DirectSum.lof R _ α M _ _ d₂ i) z := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] in
/-- The distribution equivalence carries two included block vectors to their paired block. -/
theorem partitionExternalEquiv_comp_blockIncludes
    (s : BlockAddress A) (t : BlockAddress B) (c : Leg) :
    (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap ∘ₗ
        TensorProduct.map
          (blockInclude (K := K) (V := V) s c)
          (blockInclude (K := K) (V := W) t c) =
      blockInclude (K := K) (V := ProductBlockSpace K V W)
        (blockAddressProductEquiv (A := A) (B := B) (s, t)) c := by
  classical
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, partitionExternalEquiv,
    blockInclude, ProductBlockSpace, ProductBlockIndex]
  convert TensorProduct.directSum_lof_tmul_lof K K
    (M₁ := fun i ↦ V c i) (M₂ := fun j ↦ W c j) (s c) a (t c) b using 1
  · apply congrArg (fun z ↦
      (TensorProduct.directSum K K (fun i ↦ V c i) (fun j ↦ W c j)) z)
    congr 1
  · exact directSum_lof_apply_decidableEq_irrel
      (M := fun q : A c × B c ↦ TensorProduct K (V c q.1) (W c q.2))
      _ _ (s c, t c) (a ⊗ₜ[K] b)

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] in
/-- At tensor level, the distribution equivalence carries an external product of embedded
constituents to the embedded product constituent. -/
theorem map_partitionExternalEquiv_external_blocks
    (s : BlockAddress A) (t : BlockAddress B)
    (T : Tensor3 K (fun c ↦ V c (s c)))
    (S : Tensor3 K (fun c ↦ W c (t c))) :
    map (fun c ↦
        (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
      (Tensor.external
        (map (blockInclude (K := K) (V := V) s) T)
        (map (blockInclude (K := K) (V := W) t) S)) =
      map (blockInclude (K := K) (V := ProductBlockSpace K V W)
        (blockAddressProductEquiv (A := A) (B := B) (s, t)))
        (Tensor.external T S) := by
  rw [← map_external]
  calc
    map (fun c ↦
        (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
      (map (fun c ↦ TensorProduct.map
        (blockInclude (K := K) (V := V) s c)
        (blockInclude (K := K) (V := W) t c)) (Tensor.external T S)) =
        map (fun c ↦
          (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap ∘ₗ
            TensorProduct.map
              (blockInclude (K := K) (V := V) s c)
              (blockInclude (K := K) (V := W) t c)) (Tensor.external T S) := by
          rw [map_comp]
          rfl
    _ = map (blockInclude (K := K) (V := ProductBlockSpace K V W)
          (blockAddressProductEquiv (A := A) (B := B) (s, t)))
        (Tensor.external T S) := by
      congr 2
      funext c
      exact partitionExternalEquiv_comp_blockIncludes
        (K := K) (V := V) (W := W) s t c

/-- The partitioned external product realizes the ordinary external product, up to the canonical
direct-sum distribution equivalence on its three legs. -/
theorem map_partitionExternalEquiv_external_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    map (fun c ↦
        (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
      (Tensor.external P.realize Q.realize) = (P.external Q).realize := by
  classical
  let f : BlockAddress A × BlockAddress B →
      Tensor3 K (PartitionedSpace K (ProductBlockSpace K V W)) := fun q ↦
    map (blockInclude (K := K) (V := ProductBlockSpace K V W)
      (blockAddressProductEquiv (A := A) (B := B) q))
      (Tensor.external (P.constituent q.1) (Q.constituent q.2))
  calc
    map (fun c ↦
        (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
      (Tensor.external P.realize Q.realize) =
        ∑ s ∈ P.support, ∑ t ∈ Q.support, f (s, t) := by
      unfold PartitionedTensor.realize realizePartition
      rw [LinearMap.map_sum₂, map_sum]
      simp_rw [map_sum, map_partitionExternalEquiv_external_blocks]
      rfl
    _ = ∑ q ∈ P.support.product Q.support, f q :=
      (Finset.sum_product P.support Q.support f).symm
    _ = (P.external Q).realize := by
      unfold PartitionedTensor.realize realizePartition PartitionedTensor.external
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro q hq
      rcases q with ⟨s, t⟩
      rfl

namespace Isomorphic

/-- Relation-level form of the partitioned external-product realization theorem. -/
theorem partitionedExternal
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    Isomorphic (Tensor.external P.realize Q.realize) (P.external Q).realize := by
  refine ⟨partitionExternalEquiv (K := K) (V := V) (W := W), ?_⟩
  exact map_partitionExternalEquiv_external_realize P Q

end Isomorphic

end AlgebraicComplexity.Tensor
