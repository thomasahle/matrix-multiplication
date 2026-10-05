/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductCore
import AlgebraicComplexity.Tensor.PartitionedReindex
import AlgebraicComplexity.Tensor.Product

/-!
# Reindexing external products of partitioned tensors

This module gives the factor commutors and proves that block reindexing commutes with partitioned
external products.  Direct-sum realization of the external product is independent and lives in
`Tensor.PartitionedProductRealization`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y z t

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Swap the two labels in every block of a partitioned external product. -/
def productBlockCommEquiv : ∀ c,
    ProductBlockIndex A B c ≃ ProductBlockIndex B A c :=
  fun _ ↦ Equiv.prodComm _ _

/-- Swapping a product-block label is accompanied by the canonical commutativity equivalence
between its two tensor-product factors. -/
noncomputable def productBlockSpaceCommEquiv : ∀ c q,
    ProductBlockSpace K V W c
        ((productBlockCommEquiv (A := A) (B := B) c).symm q) ≃ₗ[K]
      ProductBlockSpace K W V c q :=
  fun c q ↦ TensorProduct.comm K (V c q.2) (W c q.1)

/-- Swap the final two labels of a left-associated triple product, keeping its prefix label
fixed. -/
def productBlockSwapRightEquiv {C : Leg → Type z} : ∀ c,
    ProductBlockIndex (ProductBlockIndex A B) C c ≃
      ProductBlockIndex (ProductBlockIndex A C) B c :=
  fun _ ↦
    { toFun := fun q ↦ ((q.1.1, q.2), q.1.2)
      invFun := fun q ↦ ((q.1.1, q.2), q.1.2)
      left_inv := by rintro ⟨⟨a, b⟩, d⟩; rfl
      right_inv := by rintro ⟨⟨a, d⟩, b⟩; rfl }

/-- Block-space equivalence accompanying `productBlockSwapRightEquiv`. -/
noncomputable def productBlockSpaceSwapRightEquiv
    {C : Leg → Type z} {X : ∀ c, C c → Type t}
    [∀ c d, AddCommMonoid (X c d)] [∀ c d, Module K (X c d)] : ∀ c q,
    ProductBlockSpace K (ProductBlockSpace K V W) X c
        ((productBlockSwapRightEquiv (A := A) (B := B) (C := C) c).symm q) ≃ₗ[K]
      ProductBlockSpace K (ProductBlockSpace K V X) W c q :=
  fun c q ↦ TensorProduct.rightComm K
    (V c q.1.1) (W c q.2) (X c q.1.2)

namespace PartitionedTensor

/-- Reindexing every product block by factor swap carries `P.external Q` exactly to
`Q.external P`.  This records both the support permutation and the constituent-level tensor
commutativity, and is the basic adjacent-chunk permutation used by power relabelings. -/
theorem external_reindex_comm
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    (P.external Q).reindex
        (productBlockCommEquiv (A := A) (B := B))
        (productBlockSpaceCommEquiv (K := K) (V := V) (W := W)) =
      Q.external P := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.external, productBlockCommEquiv,
      blockAddressProductEquiv, and_comm]
  · funext address
    simp only [PartitionedTensor.reindex_constituent, PartitionedTensor.external,
      blockAddressCongr_symm_apply]
    exact map_external_comm _ _

/-- Reindexing an external product independently on its two factors is the external product of
the two reindexed partitions.  This is the product-closure law for structure-preserving
relabelings. -/
theorem external_reindex
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (e : ∀ c, Equiv.Perm (A c))
    (f : ∀ c a, V c ((e c).symm a) ≃ₗ[K] V c a)
    (g : ∀ c, Equiv.Perm (B c))
    (h : ∀ c b, W c ((g c).symm b) ≃ₗ[K] W c b) :
    (P.external Q).reindex
        (fun c ↦ Equiv.prodCongr (e c) (g c))
        (fun c q ↦ TensorProduct.congr (f c q.1) (h c q.2)) =
      (P.reindex e f).external (Q.reindex g h) := by
  classical
  apply PartitionedTensor.ext
  · change
      ((P.support.product Q.support).map
          (blockAddressProductEquiv (A := A) (B := B)).toEmbedding).map
            (blockAddressCongr
              (fun c ↦ Equiv.prodCongr (e c) (g c))).toEmbedding =
        ((P.support.map (blockAddressCongr e).toEmbedding).product
          (Q.support.map (blockAddressCongr g).toEmbedding)).map
            (blockAddressProductEquiv (A := A) (B := B)).toEmbedding
    ext address
    simp [blockAddressProductEquiv]
    rfl
  · funext address
    simp only [PartitionedTensor.reindex_constituent, PartitionedTensor.external,
      blockAddressCongr_symm_apply]
    change map (fun c ↦ TensorProduct.map
        (f c (address c).1).toLinearMap (h c (address c).2).toLinearMap)
      (Tensor.external
        (P.constituent (fun c ↦ (e c).symm (address c).1))
        (Q.constituent (fun c ↦ (g c).symm (address c).2))) = _
    rw [map_external]
    rfl

/-- Reindexing a left-associated triple external product by the right commutor swaps its final
two factors exactly. -/
theorem external_reindex_swap_right
    {C : Leg → Type z} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    {X : ∀ c, C c → Type t}
    [∀ c d, AddCommMonoid (X c d)] [∀ c d, Module K (X c d)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    ((P.external Q).external R).reindex
        (productBlockSwapRightEquiv (A := A) (B := B) (C := C))
        (productBlockSpaceSwapRightEquiv
          (K := K) (V := V) (W := W) (X := X)) =
      (P.external R).external Q := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.external, PartitionedTensor.reindex,
      productBlockSwapRightEquiv, blockAddressProductEquiv,
      and_assoc, and_left_comm, and_comm]
  · funext address
    simp only [PartitionedTensor.reindex_constituent, PartitionedTensor.external,
      blockAddressCongr_symm_apply]
    exact map_external_swap_right _ _ _

end PartitionedTensor

end AlgebraicComplexity.Tensor
