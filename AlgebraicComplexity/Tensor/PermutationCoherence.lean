/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Restriction

/-!
# Coherence and cancellation for tensor-leg permutations

Leg permutations form an action on three-tensors, but dependent leg-space reindexing means that
two propositionally equal orientations need not produce definitionally equal tensor types.  The
right public interface is therefore a tensor equality for composition and a legwise isomorphism
for orientation congruence and inverse cancellation.

These laws are independent of matrix multiplication and replace client-specific case splits over
the six orientations.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Applying a composite orientation is the same as applying its two factors successively. -/
theorem permute_composite_apply (e₁ e₂ : Orientation) (T : Tensor3 K V) :
    Tensor.permute (K := K) (V := V) (e₁.trans e₂) T =
      Tensor.permute e₂ (Tensor.permute e₁ T) := by
  rw [← permute_trans]
  rfl

namespace Isomorphic

/-- Equal orientations give isomorphic permuted tensors.  This is an isomorphism rather than an
equality because the two dependent ambient leg families are only propositionally equal. -/
theorem permute_orientation_congr {e f : Orientation} (h : e = f) (T : Tensor3 K V) :
    Isomorphic (Tensor.permute e T) (Tensor.permute f T) := by
  subst f
  exact Isomorphic.refl _

/-- Permuting by the identity orientation returns a tensor isomorphic to the original tensor.

The statement is kept at the isomorphism level because the permuted ambient family is written as
`fun c ↦ V ((Equiv.refl Leg).symm c)`, which need not elaborate as definitionally identical to
`V` in a dependent client. -/
theorem cancel_permute_refl (T : Tensor3 K V) :
    Isomorphic (Tensor.permute (Equiv.refl Leg) T) T := by
  have h : Tensor.permute (Equiv.refl Leg) T = T := by
    rw [Tensor.permute_refl]
    rfl
  exact Isomorphic.of_eq h

/-- Permuting by `e` and then by `e.symm` returns a tensor isomorphic to the original tensor. -/
theorem cancel_permute_symm_left (e : Orientation) (T : Tensor3 K V) :
    Isomorphic (Tensor.permute e.symm (Tensor.permute e T)) T := by
  let f : ∀ c, V (e.symm (e c)) ≃ₗ[K] V c := fun c ↦
    LinearEquiv.cast (R := K) (e.symm_apply_apply c)
  refine ⟨f, ?_⟩
  change Tensor.map (fun c ↦ (f c).toLinearMap)
      (Tensor.permute e.symm (Tensor.permute e T)) = T
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp only [map_smul, Tensor.permute_pure, Tensor.map_pure]
    congr 2
    funext c
    simp only [f, Equiv.symm_symm]
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    change (LinearEquiv.cast (R := K) (M := V) (e.symm_apply_apply c))
      (x (e.symm (e c))) = x c
    rw [LinearEquiv.cast_apply]
    apply cast_eq_iff_heq.mpr
    exact (Sigma.mk.inj_iff.mp
      (congrArg (fun i ↦ (⟨i, x i⟩ : Sigma V)) hc)).2
  · intro T₁ T₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- Permuting first by `e.symm` and then by `e` also returns a tensor isomorphic to the original
tensor. -/
theorem cancel_permute_symm_right (e : Orientation) (T : Tensor3 K V) :
    Isomorphic (Tensor.permute e (Tensor.permute e.symm T)) T :=
  -- `Equiv.symm_symm` holds definitionally, so this is the left law at `e.symm`.
  cancel_permute_symm_left e.symm T

end Isomorphic
end AlgebraicComplexity.Tensor
