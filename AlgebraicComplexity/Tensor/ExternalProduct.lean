import AlgebraicComplexity.Tensor.Basic

set_option linter.style.header false

/-!
# External products of trilinear tensors

The external product pairs corresponding coordinates:

`(X ⊗ Y ⊗ Z) × (X' ⊗ Y' ⊗ Z') → (X ⊗ X') ⊗ (Y ⊗ Y') ⊗ (Z ⊗ Z')`.

Mathlib's `TensorProduct.map₂` supplies the required bilinear map without any basis choices.
-/

open scoped TensorProduct

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable
    {K X Y Z X' Y' Z' X'' Y'' Z'' : Type u}
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [AddCommMonoid X''] [AddCommMonoid Y''] [AddCommMonoid Z'']
    [Module K X] [Module K Y] [Module K Z]
    [Module K X'] [Module K Y'] [Module K Z']
    [Module K X''] [Module K Y''] [Module K Z'']

/-- Pair two inner tensor coordinates, `(Y ⊗ Z)` and `(Y' ⊗ Z')`. -/
def pairInner :
    (Y ⊗[K] Z) →ₗ[K] (Y' ⊗[K] Z') →ₗ[K] (Y ⊗[K] Y') ⊗[K] (Z ⊗[K] Z') :=
  TensorProduct.map₂ (TensorProduct.mk K Y Y') (TensorProduct.mk K Z Z')

/-- The external product of two right-associated trilinear tensors. -/
def externalProduct :
    TriTensor K X Y Z →ₗ[K]
      TriTensor K X' Y' Z' →ₗ[K]
        TriTensor K (X ⊗[K] X') (Y ⊗[K] Y') (Z ⊗[K] Z') :=
  TensorProduct.map₂ (TensorProduct.mk K X X') pairInner

@[simp]
theorem pairInner_pure (y : Y) (z : Z) (y' : Y') (z' : Z') :
    pairInner (y ⊗ₜ[K] z) (y' ⊗ₜ[K] z') =
      (y ⊗ₜ[K] y') ⊗ₜ[K] (z ⊗ₜ[K] z') :=
  rfl

@[simp]
theorem externalProduct_pure
    (x : X) (y : Y) (z : Z) (x' : X') (y' : Y') (z' : Z') :
    externalProduct (pure x y z) (pure x' y' z') =
      pure (x ⊗ₜ[K] x') (y ⊗ₜ[K] y') (z ⊗ₜ[K] z') :=
  rfl

@[simp]
theorem externalProduct_zero_left (S : TriTensor K X' Y' Z') :
    externalProduct (0 : TriTensor K X Y Z) S = 0 := by
  simp [externalProduct]

@[simp]
theorem externalProduct_zero_right (T : TriTensor K X Y Z) :
    externalProduct T (0 : TriTensor K X' Y' Z') = 0 := by
  simp [externalProduct]

@[simp]
theorem externalProduct_add_left
    (T₁ T₂ : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    externalProduct (T₁ + T₂) S = externalProduct T₁ S + externalProduct T₂ S := by
  simp [externalProduct]

@[simp]
theorem externalProduct_add_right
    (T : TriTensor K X Y Z) (S₁ S₂ : TriTensor K X' Y' Z') :
    externalProduct T (S₁ + S₂) = externalProduct T S₁ + externalProduct T S₂ := by
  simp [externalProduct]

@[simp]
theorem externalProduct_smul_left
    (c : K) (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    externalProduct (c • T) S = c • externalProduct T S := by
  simp [externalProduct]

@[simp]
theorem externalProduct_smul_right
    (c : K) (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    externalProduct T (c • S) = c • externalProduct T S := by
  simp [externalProduct]

end TriTensor
end AlgebraicComplexity
