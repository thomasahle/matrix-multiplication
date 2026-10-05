/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceRestriction
import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceFusion

/-!
# Retyping explicit one-slice restrictions as C-tensor constituents

This optional bridge turns the exposed maps of a `OneSliceRestriction T d` into maps whose target
is the canonical C-tensor constituent space.  It is deliberately separate from the core
one-slice API: positive-power and CW clients that only need explicit maps and shared-`Z`
coherence do not need to import the larger C-tensor fusion development.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {T : Tensor3 K V} {d : ℕ}

namespace OneSliceRestriction

/-- Retype the explicit maps into the canonical C-tensor constituent spaces. -/
noncomputable def constituentMap (C : OneSliceRestriction T d) : ∀ c,
    V c →ₗ[K]
      CTensor.ConstituentSpace
        (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) c :=
  fun c ↦ (CTensor.oneSliceConstituentEquiv K d c).symm.toLinearMap ∘ₗ C.legMap c

/-- Retyping into the canonical C-tensor spaces preserves equality of shared `Z` maps.

Although the middle dimensions may differ, the `Z` space of `⟨1,d,1⟩` is always the same
one-coordinate space. -/
theorem constituentMap_Z_congr
    {d' : ℕ} (C : OneSliceRestriction T d) (C' : OneSliceRestriction T d')
    (h : C.legMap .Z = C'.legMap .Z) :
    C.constituentMap .Z = C'.constituentMap .Z := by
  change
    (CTensor.oneSliceConstituentEquiv K 1 .Z).symm.toLinearMap ∘ₗ C.legMap .Z =
      (CTensor.oneSliceConstituentEquiv K 1 .Z).symm.toLinearMap ∘ₗ C'.legMap .Z
  rw [h]

/-- The retyped maps carry the source to the canonical C-tensor one-slice constituent exactly. -/
theorem map_constituentMap (C : OneSliceRestriction T d) :
    Tensor.map C.constituentMap T = CTensor.oneSliceConstituent K d := by
  have hforward :
      Tensor.map
          (fun c ↦ (CTensor.oneSliceConstituentEquiv K d c).toLinearMap)
          (CTensor.oneSliceConstituent K d) =
        matrixMultiplication (K := K) 1 d 1 := by
    unfold CTensor.oneSliceConstituent matrixMultiplication
    rw [map_sum]
    simp only [Tensor.map_pure]
    simp [Fintype.sum_prod_type]
  show Tensor.map
      (fun c ↦ (CTensor.oneSliceConstituentEquiv K d c).symm.toLinearMap ∘ₗ C.legMap c) T =
      CTensor.oneSliceConstituent K d
  rw [Tensor.map_comp, LinearMap.comp_apply, C.map_eq, ← hforward]
  change
    (PiTensorProduct.congr
      (fun c ↦ (CTensor.oneSliceConstituentEquiv K d c).symm))
      ((PiTensorProduct.congr (CTensor.oneSliceConstituentEquiv K d))
        (CTensor.oneSliceConstituent K d)) =
      CTensor.oneSliceConstituent K d
  exact LinearEquiv.symm_apply_apply
    (PiTensorProduct.congr (CTensor.oneSliceConstituentEquiv K d)) _

end OneSliceRestriction

end AlgebraicComplexity
