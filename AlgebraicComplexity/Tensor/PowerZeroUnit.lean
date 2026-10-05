/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PowerFamily

/-!
# The tensor unit as a zeroth tensor power

The zeroth tensor power has one scalar degree of freedom on every leg.  This module identifies
those spaces with the base ring and proves that the canonical zeroth-power tensor is a genuine
left and right unit for the three-legged external product, even when the other tensor has
unrelated leg spaces.

These laws complement `powerMul_power`: they expose the unit at the ordinary `Tensor.external`
interface needed by clients whose zero-weight factors and positive factors have heterogeneous
target spaces.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- A zeroth tensor-power leg is canonically the scalar module. -/
def powerZeroScalarEquiv (c : Leg) : PowerSpace K V 0 c ≃ₗ[K] K :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

@[simp] theorem powerZeroScalarEquiv_powerUnit (c : Leg) :
    powerZeroScalarEquiv (K := K) (V := V) c (powerUnit (K := K) (V := V) c) = 1 := by
  unfold powerZeroScalarEquiv powerUnit
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) (R := K)
    (s := fun _ : Fin 0 ↦ V c) (@Fin.elim0 (V c))

/-- Remove a canonical zeroth-power tensor factor on the left. -/
def powerZeroExternalLeftEquiv (c : Leg) :
    TensorProduct K (PowerSpace K V 0 c) (W c) ≃ₗ[K] W c :=
  (TensorProduct.congr
    (powerZeroScalarEquiv (K := K) (V := V) c)
    (LinearEquiv.refl K (W c))).trans
      (TensorProduct.lid K (W c))

/-- Remove a canonical zeroth-power tensor factor on the right. -/
def powerZeroExternalRightEquiv (c : Leg) :
    TensorProduct K (W c) (PowerSpace K V 0 c) ≃ₗ[K] W c :=
  (TensorProduct.congr
    (LinearEquiv.refl K (W c))
    (powerZeroScalarEquiv (K := K) (V := V) c)).trans
      (TensorProduct.rid K (W c))

/-- The left unitor carries the external product of a canonical zeroth power and an arbitrary
tensor to that tensor. -/
theorem map_powerZeroExternalLeftEquiv
    (T : Tensor3 K V) (S : Tensor3 K W) :
    map (fun c ↦
      (powerZeroExternalLeftEquiv (K := K) (V := V) (W := W) c).toLinearMap)
        (external (Tensor.power T 0) S) = S := by
  rw [power_zero]
  refine PiTensorProduct.induction_on S ?_ ?_
  · intro a x
    rw [external_smul_right, LinearMap.map_smul]
    simp [powerZeroExternalLeftEquiv, powerZeroScalarEquiv, powerUnit]
  · intro S₁ S₂ h₁ h₂
    simp only [LinearMap.map_add, h₁, h₂]

/-- The right unitor carries the external product of an arbitrary tensor and a canonical zeroth
power to that tensor. -/
theorem map_powerZeroExternalRightEquiv
    (S : Tensor3 K W) (T : Tensor3 K V) :
    map (fun c ↦
      (powerZeroExternalRightEquiv (K := K) (V := V) (W := W) c).toLinearMap)
        (external S (Tensor.power T 0)) = S := by
  rw [power_zero]
  refine PiTensorProduct.induction_on S ?_ ?_
  · intro a x
    rw [external_smul_left, LinearMap.map_smul]
    simp [powerZeroExternalRightEquiv, powerZeroScalarEquiv, powerUnit]
  · intro S₁ S₂ h₁ h₂
    simp only [LinearMap.add_apply, LinearMap.map_add, h₁, h₂]

namespace Isomorphic

/-- A canonical zeroth tensor power is a left unit for `Tensor.external`. -/
theorem powerZeroExternalLeft
    (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.external (Tensor.power T 0) S) S :=
  ⟨powerZeroExternalLeftEquiv (K := K) (V := V) (W := W),
    map_powerZeroExternalLeftEquiv T S⟩

/-- A canonical zeroth tensor power is a right unit for `Tensor.external`. -/
theorem powerZeroExternalRight
    (S : Tensor3 K W) (T : Tensor3 K V) :
    Isomorphic (Tensor.external S (Tensor.power T 0)) S :=
  ⟨powerZeroExternalRightEquiv (K := K) (V := V) (W := W),
    map_powerZeroExternalRightEquiv S T⟩

end Isomorphic

namespace PowerRestriction

/-- The zeroth power, packaged as the identity restriction of a source tensor.  This is the
empty-factor base case for recursive products whose positive cases use `PowerRestriction.external`.
-/
noncomputable def zero (T : Tensor3 K V) : PowerRestriction.{u, v, v} T where
  exponent := 0
  Target := LegModuleFamily.of (PowerSpace K V 0)
  target := power T 0
  restricts := Restricts.refl _

@[simp] theorem zero_exponent (T : Tensor3 K V) : (zero T).exponent = 0 :=
  rfl

@[simp] theorem zero_target (T : Tensor3 K V) : (zero T).target = power T 0 :=
  rfl

end PowerRestriction

end AlgebraicComplexity.Tensor
