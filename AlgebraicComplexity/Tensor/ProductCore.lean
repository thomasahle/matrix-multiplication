/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Basic

/-!
# Lightweight core for factorwise tensor products

This module contains the external-product definition and the elementary laws needed by leaf
assembly: pure tensors, linearity, and finite sums.  The larger `Tensor.Product` module re-exports
this core and adds compatibility with legwise maps, restriction, commutation, and associativity.

Keeping this boundary small prevents clients that only multiply explicit tensor leaves from
loading the full product theorem object file.
-/

namespace AlgebraicComplexity.Tensor

universe u v w v' w'

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- The factorwise external product of two three-legged tensors. -/
def external :
    Tensor3 K V →ₗ[K] Tensor3 K W →ₗ[K]
      Tensor3 K (fun i ↦ TensorProduct K (V i) (W i)) :=
  PiTensorProduct.map₂ (fun i ↦ TensorProduct.mk K (V i) (W i))

/-- The external product of two pure tensors pairs their vectors leg by leg. -/
@[simp] theorem external_pure (x : ∀ i, V i) (y : ∀ i, W i) :
    external (pure x) (pure y) = pure (fun i ↦ x i ⊗ₜ[K] y i) := by
  exact PiTensorProduct.map₂_tprod_tprod _ x y

/-- An external product is zero when its left factor is zero. -/
@[simp] theorem external_zero_left (T : Tensor3 K W) :
    external (0 : Tensor3 K V) T = 0 := by
  exact LinearMap.map_zero₂ external T

/-- An external product is zero when its right factor is zero. -/
@[simp] theorem external_zero_right (T : Tensor3 K V) :
    external T (0 : Tensor3 K W) = 0 := by
  exact LinearMap.map_zero (external T)

/-- The external product distributes over addition in its left argument. -/
theorem external_add_left (T₁ T₂ : Tensor3 K V) (S : Tensor3 K W) :
    external (T₁ + T₂) S = external T₁ S + external T₂ S := by
  exact LinearMap.map_add₂ external T₁ T₂ S

/-- The external product distributes over addition in its right argument. -/
theorem external_add_right (T : Tensor3 K V) (S₁ S₂ : Tensor3 K W) :
    external T (S₁ + S₂) = external T S₁ + external T S₂ := by
  exact LinearMap.map_add (external T) S₁ S₂

/-- A scalar in the left factor can be pulled outside the external product. -/
theorem external_smul_left (r : K) (T : Tensor3 K V) (S : Tensor3 K W) :
    external (r • T) S = r • external T S := by
  exact LinearMap.map_smul₂ external r T S

/-- A scalar in the right factor can be pulled outside the external product. -/
theorem external_smul_right (r : K) (T : Tensor3 K V) (S : Tensor3 K W) :
    external T (r • S) = r • external T S := by
  exact LinearMap.map_smul (external T) r S

/-- Linearity in the first argument over a finite type-indexed sum. -/
theorem external_fintypeSum_left {I : Type*} [Fintype I]
    (T : I → Tensor3 K V) (S : Tensor3 K W) :
    external (∑ i, T i) S = ∑ i, external (T i) S := by
  simp

/-- Linearity in the second argument over a finite type-indexed sum. -/
theorem external_fintypeSum_right {I : Type*} [Fintype I]
    (T : Tensor3 K V) (S : I → Tensor3 K W) :
    external T (∑ i, S i) = ∑ i, external T (S i) := by
  simp

/-- Bilinearity expands an external product of finite sums into a double sum. -/
theorem external_sum_sum {I J : Type*} [Fintype I] [Fintype J]
    (T : I → Tensor3 K V) (S : J → Tensor3 K W) :
    external (∑ i, T i) (∑ j, S j) =
      ∑ i, ∑ j, external (T i) (S j) := by
  rw [LinearMap.map_sum₂]
  simp_rw [map_sum]

end AlgebraicComplexity.Tensor
