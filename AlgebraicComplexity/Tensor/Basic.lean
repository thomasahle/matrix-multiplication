import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map

set_option linter.style.header false

/-!
# Trilinear tensors

A small algebraic-complexity layer on top of Mathlib's module tensor product.
We right-associate three tensor factors throughout.
-/

namespace AlgebraicComplexity

universe u

/-- A right-associated trilinear tensor over `K`. -/
abbrev TriTensor
    (K X Y Z : Type u)
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module K X] [Module K Y] [Module K Z] :=
  X ⊗[K] (Y ⊗[K] Z)

namespace TriTensor

variable
    {K X Y Z X' Y' Z' X'' Y'' Z'' : Type u}
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [AddCommMonoid X''] [AddCommMonoid Y''] [AddCommMonoid Z'']
    [Module K X] [Module K Y] [Module K Z]
    [Module K X'] [Module K Y'] [Module K Z']
    [Module K X''] [Module K Y''] [Module K Z'']

/-- A pure trilinear tensor. -/
def pure (x : X) (y : Y) (z : Z) : TriTensor K X Y Z :=
  x ⊗ₜ[K] (y ⊗ₜ[K] z)

/-- Apply one linear map in each coordinate of a trilinear tensor. -/
def map3 (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z') :
    TriTensor K X Y Z →ₗ[K] TriTensor K X' Y' Z' :=
  TensorProduct.map f (TensorProduct.map g h)

@[simp]
theorem map3_pure (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z')
    (x : X) (y : Y) (z : Z) :
    map3 f g h (pure x y z) = pure (f x) (g y) (h z) :=
  rfl

@[simp]
theorem map3_id :
    map3 (LinearMap.id : X →ₗ[K] X)
      (LinearMap.id : Y →ₗ[K] Y)
      (LinearMap.id : Z →ₗ[K] Z) = LinearMap.id := by
  simp [map3]

/-- Three-coordinate maps compose coordinatewise. -/
theorem map3_comp
    (f₁ : X →ₗ[K] X') (g₁ : Y →ₗ[K] Y') (h₁ : Z →ₗ[K] Z')
    (f₂ : X' →ₗ[K] X'') (g₂ : Y' →ₗ[K] Y'') (h₂ : Z' →ₗ[K] Z'') :
    map3 (f₂.comp f₁) (g₂.comp g₁) (h₂.comp h₁) =
      (map3 f₂ g₂ h₂).comp (map3 f₁ g₁ h₁) := by
  apply TensorProduct.ext_threefold'
  intro x y z
  rfl

/-- Swap the first two tensor coordinates. -/
def swapXY : TriTensor K X Y Z ≃ₗ[K] TriTensor K Y X Z :=
  TensorProduct.leftComm K X Y Z

/-- Swap the final two tensor coordinates. -/
def swapYZ : TriTensor K X Y Z ≃ₗ[K] TriTensor K X Z Y :=
  TensorProduct.congr (LinearEquiv.refl K X) (TensorProduct.comm K Y Z)

/-- Cyclically rotate `X,Y,Z` to `Y,Z,X`. -/
def cycleLeft : TriTensor K X Y Z ≃ₗ[K] TriTensor K Y Z X :=
  swapXY (K := K) (X := X) (Y := Y) (Z := Z) ≪≫ₗ
    swapYZ (K := K) (X := Y) (Y := X) (Z := Z)

/-- Cyclically rotate `X,Y,Z` to `Z,X,Y`. -/
def cycleRight : TriTensor K X Y Z ≃ₗ[K] TriTensor K Z X Y :=
  (cycleLeft (K := K) (X := Z) (Y := X) (Z := Y)).symm

@[simp]
theorem swapXY_pure (x : X) (y : Y) (z : Z) :
    (swapXY (K := K) (X := X) (Y := Y) (Z := Z)) (pure x y z) = pure y x z :=
  rfl

@[simp]
theorem swapYZ_pure (x : X) (y : Y) (z : Z) :
    (swapYZ (K := K) (X := X) (Y := Y) (Z := Z)) (pure x y z) = pure x z y :=
  rfl

@[simp]
theorem cycleLeft_pure (x : X) (y : Y) (z : Z) :
    (cycleLeft (K := K) (X := X) (Y := Y) (Z := Z)) (pure x y z) = pure y z x :=
  rfl

@[simp]
theorem cycleRight_pure (x : X) (y : Y) (z : Z) :
    (cycleRight (K := K) (X := X) (Y := Y) (Z := Z)) (pure x y z) = pure z x y :=
  rfl

end TriTensor
end AlgebraicComplexity
