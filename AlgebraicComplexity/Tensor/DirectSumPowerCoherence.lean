/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.DirectSum
import AlgebraicComplexity.Tensor.PowerCoherence
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Coherence for powers of binary direct sums

Layer 1 (`AlgebraicComplexity/Tensor/`). This module contains the tensor isomorphisms shared by
two mathematically different consumers of the Pascal expansion of `(A ⊞ B)^{⊗n}`:

* `Tensor/AsymptoticRankCalculus.lean` uses the expansion to prove a rank-growth upper bound;
* `Tensor/DirectSumPower.lean` uses it constructively to assemble finite value certificates.

The shared declarations distribute an external product over a binary direct sum, peel the final
factor from a power beside an arbitrary prefix, and absorb a newly read `A` or `B` into the
corresponding prefix power. They are basis-free and valid over every commutative semiring.  The
transposition of the last two factors of a triple product that they rest on is
`Tensor.Isomorphic.external_swapRight` of `Tensor/Product.lean`.

Keeping these structural laws here prevents a finite tensor extraction from importing
asymptotic rank merely to reassociate tensor products.
-/

namespace AlgebraicComplexity.Tensor

universe u v w z

variable {K : Type u} [CommSemiring K]
variable {U : Leg → Type z} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- The external product distributes over a binary direct sum on every leg.

Proof sketch: the direct sum is the sum of the two included summands, the external product is
additive in that argument, and on each summand the leg equivalence `TensorProduct.prodRight`
turns `id ⊗ inl` into `inl`. -/
theorem map_external_directSum (X : Tensor3 K U) (A : Tensor3 K V) (B : Tensor3 K W) :
    map (fun c ↦ (TensorProduct.prodRight K K (U c) (V c) (W c)).toLinearMap)
        (external X (directSum A B)) =
      directSum (external X A) (external X B) := by
  have hid : map (fun c ↦ LinearMap.id (R := K) (M := U c)) X = X := by simp
  have hXA : external X (map (includeLeft (K := K) (V := V) (W := W)) A) =
      map (fun c ↦ TensorProduct.map (LinearMap.id (R := K) (M := U c))
        (includeLeft (K := K) (V := V) (W := W) c)) (external X A) := by
    rw [map_external, hid]
  have hXB : external X (map (includeRight (K := K) (V := V) (W := W)) B) =
      map (fun c ↦ TensorProduct.map (LinearMap.id (R := K) (M := U c))
        (includeRight (K := K) (V := V) (W := W) c)) (external X B) := by
    rw [map_external, hid]
  have e1 : (fun c ↦ (TensorProduct.prodRight K K (U c) (V c) (W c)).toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.id (R := K) (M := U c))
        (includeLeft (K := K) (V := V) (W := W) c)) =
      includeLeft (K := K) (V := fun c ↦ TensorProduct K (U c) (V c))
        (W := fun c ↦ TensorProduct K (U c) (W c)) := by
    funext c
    ext x y <;> simp
  have e2 : (fun c ↦ (TensorProduct.prodRight K K (U c) (V c) (W c)).toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.id (R := K) (M := U c))
        (includeRight (K := K) (V := V) (W := W) c)) =
      includeRight (K := K) (V := fun c ↦ TensorProduct K (U c) (V c))
        (W := fun c ↦ TensorProduct K (U c) (W c)) := by
    funext c
    ext x y <;> simp
  rw [directSum, external_add_right, LinearMap.map_add, directSum, hXA, hXB,
    map_map_comp, map_map_comp, e1, e2]

/-- Distributivity of the external product over a binary direct sum, as a legwise isomorphism. -/
theorem Isomorphic.external_directSum (X : Tensor3 K U) (A : Tensor3 K V) (B : Tensor3 K W) :
    Isomorphic (Tensor.external X (directSum A B))
      (directSum (Tensor.external X A) (Tensor.external X B)) := by
  refine ⟨fun c ↦ TensorProduct.prodRight K K (U c) (V c) (W c), ?_⟩
  simpa [PiTensorProduct.congr] using map_external_directSum X A B

/-- Peeling off the last factor of a tensor power sitting to the right of a fixed prefix. -/
theorem Isomorphic.external_power_succ (Y : Tensor3 K U) (D : Tensor3 K V) (n : ℕ) :
    Isomorphic (Tensor.external Y (Tensor.power D (n + 1)))
      (Tensor.external (Tensor.external Y (Tensor.power D n)) D) :=
  ((Isomorphic.refl Y).external ((isomorphic_external_power D n 1).symm.trans
      ((Isomorphic.refl (Tensor.power D n)).external (Isomorphic.power_one D)))).trans
    (Isomorphic.external_assoc_symm Y (Tensor.power D n) D)

/-- **Absorbing one freshly read `A` into the mixed prefix.**  `(A^{⊗k} ⊠ B^{⊗m} ⊠ D^{⊗n}) ⊠ A`
is the same prefix with one more `A`. -/
theorem Isomorphic.externalPrefix_absorb_left (A : Tensor3 K V) (B : Tensor3 K W)
    (D : Tensor3 K U) (k m n : ℕ) :
    Isomorphic
      (Tensor.external
        (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
          (Tensor.power D n)) A)
      (Tensor.external (Tensor.external (Tensor.power A (k + 1)) (Tensor.power B m))
        (Tensor.power D n)) :=
  (Isomorphic.external_swapRight (Tensor.external (Tensor.power A k) (Tensor.power B m))
      (Tensor.power D n) A).trans
    ((((Isomorphic.external_swapRight (Tensor.power A k) (Tensor.power B m) A).trans
        ((((Isomorphic.refl (Tensor.power A k)).external
              (Isomorphic.power_one A).symm).trans
          (isomorphic_external_power A k 1)).external
            (Isomorphic.refl (Tensor.power B m)))).external
      (Isomorphic.refl (Tensor.power D n))))

/-- **Absorbing one freshly read `B` into the mixed prefix.** -/
theorem Isomorphic.externalPrefix_absorb_right (A : Tensor3 K V) (B : Tensor3 K W)
    (D : Tensor3 K U) (k m n : ℕ) :
    Isomorphic
      (Tensor.external
        (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
          (Tensor.power D n)) B)
      (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B (m + 1)))
        (Tensor.power D n)) :=
  (Isomorphic.external_swapRight (Tensor.external (Tensor.power A k) (Tensor.power B m))
      (Tensor.power D n) B).trans
    (((Isomorphic.external_assoc (Tensor.power A k) (Tensor.power B m) B).trans
      ((Isomorphic.refl (Tensor.power A k)).external
        ((((Isomorphic.refl (Tensor.power B m)).external
              (Isomorphic.power_one B).symm).trans
          (isomorphic_external_power B m 1))))).external
      (Isomorphic.refl (Tensor.power D n)))

end AlgebraicComplexity.Tensor
