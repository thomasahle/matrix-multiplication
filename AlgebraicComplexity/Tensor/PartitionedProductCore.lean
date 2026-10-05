/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCore
import AlgebraicComplexity.Tensor.ProductCore

/-!
# Finite support core for external products of partitioned tensors

This module defines product block labels/spaces and the Cartesian-product partition.  Reindexing,
direct-sum distribution, and realization of the ambient tensor product remain in
`Tensor.PartitionedProduct`, which re-exports this core.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Block labels of an external product pair the labels on each tensor leg. -/
abbrev ProductBlockIndex (A : Leg → Type w) (B : Leg → Type x) (c : Leg) :=
  A c × B c

/-- Block spaces of an external product are factorwise tensor products. -/
abbrev ProductBlockSpace (K : Type u) [CommSemiring K]
    (V : ∀ c, A c → Type v) (W : ∀ c, B c → Type y)
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
    (c : Leg) (q : ProductBlockIndex A B c) :=
  TensorProduct K (V c q.1) (W c q.2)

/-- Pairing full block addresses is equivalent to pairing their labels independently on each
leg. -/
def blockAddressProductEquiv :
    BlockAddress A × BlockAddress B ≃ BlockAddress (ProductBlockIndex A B) where
  toFun q c := (q.1 c, q.2 c)
  invFun q := (fun c ↦ (q c).1, fun c ↦ (q c).2)
  left_inv q := by
    rcases q with ⟨s, t⟩
    rfl
  right_inv q := by
    rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem blockAddressProductEquiv_apply_fst
    (s : BlockAddress A) (t : BlockAddress B) (c : Leg) :
    (blockAddressProductEquiv (A := A) (B := B) (s, t) c).1 = s c := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem blockAddressProductEquiv_apply_snd
    (s : BlockAddress A) (t : BlockAddress B) (c : Leg) :
    (blockAddressProductEquiv (A := A) (B := B) (s, t) c).2 = t c := rfl

namespace PartitionedTensor

/-- The partitioned external product.  The construction keeps precisely the products of
supported constituents. -/
noncomputable def external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    PartitionedTensor (K := K) (A := ProductBlockIndex A B)
      (ProductBlockSpace K V W) where
  support := (P.support.product Q.support).map
    (blockAddressProductEquiv (A := A) (B := B)).toEmbedding
  constituent q := Tensor.external
    (P.constituent (fun c ↦ (q c).1))
    (Q.constituent (fun c ↦ (q c).2))

/-- Product-support membership is coordinatewise membership in the source supports. -/
@[simp] theorem mem_external_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (q : BlockAddress (ProductBlockIndex A B)) :
    q ∈ (P.external Q).support ↔
      (fun c ↦ (q c).1) ∈ P.support ∧ (fun c ↦ (q c).2) ∈ Q.support := by
  classical
  simp [external, blockAddressProductEquiv]

/-- The product support is the Cartesian product of the two source supports. -/
@[simp] theorem card_external_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    (P.external Q).support.card = P.support.card * Q.support.card := by
  simp [external]

end PartitionedTensor

end AlgebraicComplexity.Tensor
