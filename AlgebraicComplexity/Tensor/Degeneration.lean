/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Polynomial

/-!
# Constructive one-parameter tensor degeneration

A polynomial family of linear maps is stored coefficientwise.  Applying one such family on each
tensor leg produces a polynomial tensor path.  `PolynomialDegenerates T S` asserts that this path
has leading term `S`, i.e. it is exactly `ε^d S + O(ε^(d+1))` for some natural degree `d`.

This is the basis-free semantic layer.  Coordinate weight (monomial) certificates are built on
top of it rather than being baked into the definition.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- A polynomial family of linear maps, represented by its finitely many coefficients. -/
abbrev PolynomialLinearMap (K : Type u) [CommSemiring K]
    (M : Type v) (N : Type w)
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N] :=
  PolynomialVector (M →ₗ[K] N)

namespace PolynomialLinearMap

/-- The polynomial monomial `ε^d f`. -/
noncomputable def monomial {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (d : ℕ) (f : M →ₗ[K] N) : PolynomialLinearMap K M N :=
  PolynomialVector.monomial d f

/-- A constant family of linear maps. -/
noncomputable def constant {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) : PolynomialLinearMap K M N :=
  monomial 0 f

/-- Apply every coefficient map to a fixed vector. -/
noncomputable def applyVector {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) (x : M) : PolynomialVector N :=
  Finsupp.mapRange (fun f : M →ₗ[K] N ↦ f x) (by simp) A

/-- The degree-`d` coefficient of `applyVector A x` is the coefficient map `A d` applied to
`x`. -/
@[simp] theorem applyVector_coeff {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) (x : M) (d : ℕ) :
    applyVector A x d = A d x := by
  simp [applyVector]

/-- Applying the zero polynomial map family to any vector gives the zero polynomial vector. -/
@[simp] theorem applyVector_zero {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (x : M) : applyVector (0 : PolynomialLinearMap K M N) x = 0 := by
  ext
  simp

/-- Applying a sum of polynomial map families is the sum of the separate applications. -/
theorem applyVector_add {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A B : PolynomialLinearMap K M N) (x : M) :
    applyVector (A + B) x = applyVector A x + applyVector B x := by
  ext
  simp

/-- Applying a polynomial map family commutes with scaling the input vector. -/
theorem applyVector_smul {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) (r : K) (x : M) :
    applyVector A (r • x) = r • applyVector A x := by
  ext
  simp

/-- Applying the monomial family `ε^d f` to `x` gives the monomial vector `ε^d (f x)`. -/
@[simp] theorem applyVector_monomial {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (d : ℕ) (f : M →ₗ[K] N) (x : M) :
    applyVector (PolynomialVector.monomial d f) x =
      PolynomialVector.monomial d (f x) := by
  ext
  simp [applyVector, PolynomialVector.monomial]

/-- Cauchy product of polynomial map families, using the tensor product of their coefficient
maps. -/
noncomputable def tensor
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (A : PolynomialLinearMap K M M') (B : PolynomialLinearMap K N N') :
    PolynomialLinearMap K (TensorProduct K M N) (TensorProduct K M' N') :=
  PolynomialVector.convolution
    (TensorProduct.mapBilinear (RingHom.id K) M N M' N') A B

/-- The Cauchy tensor product with the zero family as left factor is the zero family. -/
@[simp] theorem tensor_zero_left
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (B : PolynomialLinearMap K N N') :
    tensor (0 : PolynomialLinearMap K M M') B = 0 := by
  simp [tensor]

/-- The Cauchy tensor product with the zero family as right factor is the zero family. -/
@[simp] theorem tensor_zero_right
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (A : PolynomialLinearMap K M M') :
    tensor A (0 : PolynomialLinearMap K N N') = 0 := by
  simp [tensor]

/-- The Cauchy tensor product of map families is additive in its left factor. -/
theorem tensor_add_left
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (A₁ A₂ : PolynomialLinearMap K M M') (B : PolynomialLinearMap K N N') :
    tensor (A₁ + A₂) B = tensor A₁ B + tensor A₂ B := by
  exact PolynomialVector.convolution_add_left _ _ _ _

/-- The Cauchy tensor product of map families is additive in its right factor. -/
theorem tensor_add_right
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (A : PolynomialLinearMap K M M') (B₁ B₂ : PolynomialLinearMap K N N') :
    tensor A (B₁ + B₂) = tensor A B₁ + tensor A B₂ := by
  exact PolynomialVector.convolution_add_right _ _ _ _

/-- The Cauchy tensor product of the monomial families `ε^i f` and `ε^j g` is the monomial
family `ε^(i+j) (f ⊗ g)`. -/
@[simp] theorem tensor_monomial
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (i j : ℕ) (f : M →ₗ[K] M') (g : N →ₗ[K] N') :
    tensor (PolynomialVector.monomial i f) (PolynomialVector.monomial j g) =
      PolynomialVector.monomial (i + j) (TensorProduct.map f g) := by
  exact PolynomialVector.convolution_monomial _ _ _ _ _

/-- Applying a tensor product of polynomial map families to a pure tensor is the Cauchy product
of the separately transformed vectors. -/
theorem applyVector_tensor_tmul
    {M N M' N' : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid M'] [Module K M'] [AddCommMonoid N'] [Module K N']
    (A : PolynomialLinearMap K M M') (B : PolynomialLinearMap K N N')
    (x : M) (y : N) :
    applyVector (tensor A B) (x ⊗ₜ[K] y) =
      PolynomialVector.convolution (TensorProduct.mk K M' N')
        (applyVector A x) (applyVector B y) := by
  classical
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ =>
      rw [tensor_add_left, applyVector_add, applyVector_add,
        PolynomialVector.convolution_add_left, h₁, h₂]
  | single i f =>
      induction B using Finsupp.induction_linear with
      | zero => simp
      | add B₁ B₂ h₁ h₂ =>
          rw [tensor_add_right, applyVector_add, applyVector_add,
            PolynomialVector.convolution_add_right, h₁, h₂]
      | single j g =>
          change applyVector
              (PolynomialVector.convolution
                (TensorProduct.mapBilinear (RingHom.id K) M N M' N')
                (PolynomialVector.monomial i f) (PolynomialVector.monomial j g))
              (x ⊗ₜ[K] y) =
            PolynomialVector.convolution (TensorProduct.mk K M' N')
              (applyVector (PolynomialVector.monomial i f) x)
              (applyVector (PolynomialVector.monomial j g) y)
          rw [PolynomialVector.convolution_monomial, applyVector_monomial,
            applyVector_monomial, applyVector_monomial,
            PolynomialVector.convolution_monomial]
          simp

/-- Replace the parameter by `ε^d` in a polynomial family of linear maps. -/
noncomputable def dilate {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (d : ℕ) (A : PolynomialLinearMap K M N) : PolynomialLinearMap K M N :=
  PolynomialVector.dilation d A

/-- Apply a polynomial family of linear maps to a polynomial vector, convolving their degrees. -/
noncomputable def applyPolynomial {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) (P : PolynomialVector M) : PolynomialVector N :=
  PolynomialVector.convolution LinearMap.applyₗ.flip A P

/-- Applying the zero map family to a polynomial vector gives the zero polynomial vector. -/
@[simp] theorem applyPolynomial_zero_left {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (P : PolynomialVector M) :
    applyPolynomial (0 : PolynomialLinearMap K M N) P = 0 := by
  simp [applyPolynomial]

/-- Applying a polynomial map family to the zero polynomial vector gives zero. -/
@[simp] theorem applyPolynomial_zero_right {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) : applyPolynomial A 0 = 0 := by
  simp [applyPolynomial]

/-- Polynomial application is additive in the map family. -/
theorem applyPolynomial_add_left {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A B : PolynomialLinearMap K M N) (P : PolynomialVector M) :
    applyPolynomial (A + B) P = applyPolynomial A P + applyPolynomial B P := by
  exact PolynomialVector.convolution_add_left _ _ _ _

/-- Polynomial application is additive in the polynomial vector argument. -/
theorem applyPolynomial_add_right {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (A : PolynomialLinearMap K M N) (P Q : PolynomialVector M) :
    applyPolynomial A (P + Q) = applyPolynomial A P + applyPolynomial A Q := by
  exact PolynomialVector.convolution_add_right _ _ _ _

/-- Applying the monomial family `ε^i f` to the monomial vector `ε^j a` gives the monomial
vector `ε^(i+j) (f a)`. -/
@[simp] theorem applyPolynomial_monomial {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (i j : ℕ) (f : M →ₗ[K] N) (a : M) :
    applyPolynomial (PolynomialVector.monomial i f)
        (PolynomialVector.monomial j a) =
      PolynomialVector.monomial (i + j) (f a) := by
  exact PolynomialVector.convolution_monomial _ _ _ _ _

/-- Cauchy composition of two polynomial families of linear maps. -/
noncomputable def comp
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (B : PolynomialLinearMap K N P) (A : PolynomialLinearMap K M N) :
    PolynomialLinearMap K M P :=
  PolynomialVector.convolution (LinearMap.llcomp K M N P) B A

/-- Cauchy composition with the zero outer family is the zero family. -/
@[simp] theorem comp_zero_left
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (A : PolynomialLinearMap K M N) :
    comp (0 : PolynomialLinearMap K N P) A = 0 := by
  simp [comp]

/-- Cauchy composition with the zero inner family is the zero family. -/
@[simp] theorem comp_zero_right
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (B : PolynomialLinearMap K N P) :
    comp B (0 : PolynomialLinearMap K M N) = 0 := by
  simp [comp]

/-- Cauchy composition is additive in the outer (second-applied) family. -/
theorem comp_add_left
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (B₁ B₂ : PolynomialLinearMap K N P) (A : PolynomialLinearMap K M N) :
    comp (B₁ + B₂) A = comp B₁ A + comp B₂ A := by
  exact PolynomialVector.convolution_add_left _ _ _ _

/-- Cauchy composition is additive in the inner (first-applied) family. -/
theorem comp_add_right
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (B : PolynomialLinearMap K N P) (A₁ A₂ : PolynomialLinearMap K M N) :
    comp B (A₁ + A₂) = comp B A₁ + comp B A₂ := by
  exact PolynomialVector.convolution_add_right _ _ _ _

/-- Evaluation respects Cauchy composition of polynomial linear-map families. -/
theorem applyVector_comp
    {M : Type v} {N : Type w} {P : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P]
    (B : PolynomialLinearMap K N P) (A : PolynomialLinearMap K M N) (x : M) :
    applyVector (comp B A) x = applyPolynomial B (applyVector A x) := by
  classical
  induction B using Finsupp.induction_linear with
  | zero => simp
  | add B₁ B₂ h₁ h₂ =>
      rw [comp_add_left, applyVector_add, applyPolynomial_add_left, h₁, h₂]
  | single i f =>
      induction A using Finsupp.induction_linear with
      | zero => simp
      | add A₁ A₂ h₁ h₂ =>
          rw [comp_add_right, applyVector_add, applyVector_add,
            applyPolynomial_add_right, h₁, h₂]
      | single j g =>
          change applyVector
              (comp (PolynomialVector.monomial i f)
                (PolynomialVector.monomial j g)) x =
            applyPolynomial (PolynomialVector.monomial i f)
              (applyVector (PolynomialVector.monomial j g) x)
          rw [comp, PolynomialVector.convolution_monomial,
            applyVector_monomial, applyVector_monomial,
            applyPolynomial_monomial]
          rfl

end PolynomialLinearMap

/-- Apply polynomial map families independently on the three tensor legs.

The six nested finite sums are hidden inside three `Finsupp.sum`s.  A coefficient choice
`(dx,dy,dz)` contributes in total degree `dx + dy + dz`.
-/
noncomputable def polynomialTransform
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T : Tensor3 K V) : PolynomialTensor K W :=
  (A .X).sum fun dx fx ↦
    (A .Y).sum fun dy fy ↦
      (A .Z).sum fun dz fz ↦
        PolynomialVector.monomial (dx + dy + dz)
          (map (ofLegs fx fy fz) T)

/-- On a pure tensor, polynomial transformation is convolution of the transformed vectors. -/
theorem polynomialTransform_pure
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) (x : ∀ c, V c) :
    polynomialTransform A (pure (K := K) x) =
      polynomialPure (K := K)
        (fun c ↦ PolynomialLinearMap.applyVector (A c) (x c)) := by
  classical
  simp [polynomialTransform, polynomialPure, PolynomialLinearMap.applyVector,
    Finsupp.sum_mapRange_index, Nat.add_assoc]

/-- Polynomial transformation is additive in its `X` map family. -/
theorem polynomialTransform_add_maps_X
    (A₁ A₂ : PolynomialLinearMap K (V .X) (W .X))
    (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs (A₁ + A₂) AY AZ) T =
      polynomialTransform (ofLegs A₁ AY AZ) T +
        polynomialTransform (ofLegs A₂ AY AZ) T := by
  classical
  simp [polynomialTransform, Finsupp.sum_add_index', map_ofLegs_add_X,
    PolynomialVector.monomial_add, ofLegs]

/-- Polynomial transformation is additive in its `Y` map family. -/
theorem polynomialTransform_add_maps_Y
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (A₁ A₂ : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs AX (A₁ + A₂) AZ) T =
      polynomialTransform (ofLegs AX A₁ AZ) T +
        polynomialTransform (ofLegs AX A₂ AZ) T := by
  classical
  simp [polynomialTransform, Finsupp.sum_add_index', Finsupp.sum_add,
    map_ofLegs_add_Y, PolynomialVector.monomial_add, ofLegs]

/-- Polynomial transformation is additive in its `Z` map family. -/
theorem polynomialTransform_add_maps_Z
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (A₁ A₂ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs AX AY (A₁ + A₂)) T =
      polynomialTransform (ofLegs AX AY A₁) T +
        polynomialTransform (ofLegs AX AY A₂) T := by
  classical
  simp [polynomialTransform, Finsupp.sum_add_index', Finsupp.sum_add,
    map_ofLegs_add_Z, PolynomialVector.monomial_add, ofLegs]

/-- A zero map family on the `X` leg transforms every tensor to the zero path. -/
@[simp] theorem polynomialTransform_zero_maps_X
    (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs 0 AY AZ) T = 0 := by
  classical
  simp [polynomialTransform, ofLegs]

/-- A zero map family on the `Y` leg transforms every tensor to the zero path. -/
@[simp] theorem polynomialTransform_zero_maps_Y
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs AX 0 AZ) T = 0 := by
  classical
  simp [polynomialTransform, ofLegs]

/-- A zero map family on the `Z` leg transforms every tensor to the zero path. -/
@[simp] theorem polynomialTransform_zero_maps_Z
    (AX : PolynomialLinearMap K (V .X) (W .X))
    (AY : PolynomialLinearMap K (V .Y) (W .Y)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs AX AY 0) T = 0 := by
  classical
  simp [polynomialTransform, ofLegs]

/-- Polynomial transformation sends the zero tensor to the zero path. -/
@[simp] theorem polynomialTransform_zero
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) :
    polynomialTransform A (0 : Tensor3 K V) = 0 := by
  classical
  simp [polynomialTransform]

/-- Polynomial transformation is additive in the tensor argument. -/
theorem polynomialTransform_add
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T S : Tensor3 K V) :
    polynomialTransform A (T + S) =
      polynomialTransform A T + polynomialTransform A S := by
  classical
  simp [polynomialTransform, Finsupp.sum_add]

/-- Polynomial transformation commutes with scalar multiplication of the tensor. -/
theorem polynomialTransform_smul
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (r : K) (T : Tensor3 K V) :
    polynomialTransform A (r • T) = r • polynomialTransform A T := by
  classical
  simp [polynomialTransform, PolynomialVector.monomial_smul, Finsupp.smul_sum]

/-- Extend polynomial transformation linearly from fixed tensors to polynomial tensor paths.
An input coefficient in degree `d` shifts every output degree by `d`. -/
noncomputable def polynomialTransformPath
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (P : PolynomialTensor K W) : PolynomialTensor K U :=
  P.sum fun d T ↦ PolynomialVector.shift d (polynomialTransform B T)

/-- Path transformation sends the zero polynomial tensor path to the zero path. -/
@[simp] theorem polynomialTransformPath_zero
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c)) :
    polynomialTransformPath B (0 : PolynomialTensor K W) = 0 := by
  simp [polynomialTransformPath]

/-- Path transformation is additive in the input path. -/
theorem polynomialTransformPath_add
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (P Q : PolynomialTensor K W) :
    polynomialTransformPath B (P + Q) =
      polynomialTransformPath B P + polynomialTransformPath B Q := by
  classical
  simp [polynomialTransformPath, Finsupp.sum_add_index',
    polynomialTransform_add, PolynomialVector.shift_add]

/-- Path transformation commutes with scalar multiplication of the input path. -/
theorem polynomialTransformPath_smul
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (r : K) (P : PolynomialTensor K W) :
    polynomialTransformPath B (r • P) = r • polynomialTransformPath B P := by
  classical
  simp [polynomialTransformPath, Finsupp.sum_smul_index',
    polynomialTransform_smul, PolynomialVector.shift_smul, Finsupp.smul_sum]

/-- On the one-coefficient path `ε^d T`, path transformation is the transform of `T` with all
degrees shifted up by `d`. -/
@[simp] theorem polynomialTransformPath_monomial
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (d : ℕ) (T : Tensor3 K W) :
    polynomialTransformPath B (PolynomialVector.monomial d T) =
      PolynomialVector.shift d (polynomialTransform B T) := by
  simp [polynomialTransformPath, PolynomialVector.monomial]

/-- Path transformation is additive in its `X` map family. -/
theorem polynomialTransformPath_add_maps_X
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B₁ B₂ : PolynomialLinearMap K (W .X) (U .X))
    (BY : PolynomialLinearMap K (W .Y) (U .Y))
    (BZ : PolynomialLinearMap K (W .Z) (U .Z))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs (B₁ + B₂) BY BZ) P =
      polynomialTransformPath (ofLegs B₁ BY BZ) P +
        polynomialTransformPath (ofLegs B₂ BY BZ) P := by
  classical
  simp [polynomialTransformPath, polynomialTransform_add_maps_X,
    PolynomialVector.shift_add, Finsupp.sum_add]

/-- Path transformation is additive in its `Y` map family. -/
theorem polynomialTransformPath_add_maps_Y
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BX : PolynomialLinearMap K (W .X) (U .X))
    (B₁ B₂ : PolynomialLinearMap K (W .Y) (U .Y))
    (BZ : PolynomialLinearMap K (W .Z) (U .Z))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs BX (B₁ + B₂) BZ) P =
      polynomialTransformPath (ofLegs BX B₁ BZ) P +
        polynomialTransformPath (ofLegs BX B₂ BZ) P := by
  classical
  simp [polynomialTransformPath, polynomialTransform_add_maps_Y,
    PolynomialVector.shift_add, Finsupp.sum_add]

/-- Path transformation is additive in its `Z` map family. -/
theorem polynomialTransformPath_add_maps_Z
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BX : PolynomialLinearMap K (W .X) (U .X))
    (BY : PolynomialLinearMap K (W .Y) (U .Y))
    (B₁ B₂ : PolynomialLinearMap K (W .Z) (U .Z))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs BX BY (B₁ + B₂)) P =
      polynomialTransformPath (ofLegs BX BY B₁) P +
        polynomialTransformPath (ofLegs BX BY B₂) P := by
  classical
  simp [polynomialTransformPath, polynomialTransform_add_maps_Z,
    PolynomialVector.shift_add, Finsupp.sum_add]

/-- A zero map family on the `X` leg sends every path to the zero path. -/
@[simp] theorem polynomialTransformPath_zero_maps_X
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BY : PolynomialLinearMap K (W .Y) (U .Y))
    (BZ : PolynomialLinearMap K (W .Z) (U .Z))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs 0 BY BZ) P = 0 := by
  classical
  simp [polynomialTransformPath]

/-- A zero map family on the `Y` leg sends every path to the zero path. -/
@[simp] theorem polynomialTransformPath_zero_maps_Y
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BX : PolynomialLinearMap K (W .X) (U .X))
    (BZ : PolynomialLinearMap K (W .Z) (U .Z))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs BX 0 BZ) P = 0 := by
  classical
  simp [polynomialTransformPath]

/-- A zero map family on the `Z` leg sends every path to the zero path. -/
@[simp] theorem polynomialTransformPath_zero_maps_Z
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BX : PolynomialLinearMap K (W .X) (U .X))
    (BY : PolynomialLinearMap K (W .Y) (U .Y))
    (P : PolynomialTensor K W) :
    polynomialTransformPath (ofLegs BX BY 0) P = 0 := by
  classical
  simp [polynomialTransformPath]

/-- Applying polynomial map families to a polynomial pure tensor acts independently on its three
polynomial vectors. -/
theorem polynomialTransformPath_polynomialPure_ofLegs
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (BX : PolynomialLinearMap K (W .X) (U .X))
    (BY : PolynomialLinearMap K (W .Y) (U .Y))
    (BZ : PolynomialLinearMap K (W .Z) (U .Z))
    (xX : PolynomialVector (W .X)) (xY : PolynomialVector (W .Y))
    (xZ : PolynomialVector (W .Z)) :
    polynomialTransformPath (ofLegs BX BY BZ)
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      polynomialPure (K := K) (ofLegs
        (PolynomialLinearMap.applyPolynomial BX xX)
        (PolynomialLinearMap.applyPolynomial BY xY)
        (PolynomialLinearMap.applyPolynomial BZ xZ)) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [polynomialPure_add_X, polynomialTransformPath_add,
        PolynomialLinearMap.applyPolynomial_add_right, ha, hb]
  | single ax vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [polynomialPure_add_Y, polynomialTransformPath_add,
            PolynomialLinearMap.applyPolynomial_add_right, ha, hb]
      | single ay vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [polynomialPure_add_Z, polynomialTransformPath_add,
                PolynomialLinearMap.applyPolynomial_add_right, ha, hb]
          | single az vz =>
              induction BX using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb =>
                  simp [polynomialTransformPath_add_maps_X,
                    PolynomialLinearMap.applyPolynomial_add_left,
                    polynomialPure_add_X, ha, hb]
              | single bx fx =>
                  induction BY using Finsupp.induction_linear with
                  | zero => simp
                  | add a b ha hb =>
                      simp [polynomialTransformPath_add_maps_Y,
                        PolynomialLinearMap.applyPolynomial_add_left,
                        polynomialPure_add_Y, ha, hb]
                  | single byDeg fy =>
                      induction BZ using Finsupp.induction_linear with
                      | zero => simp
                      | add a b ha hb =>
                          simp [polynomialTransformPath_add_maps_Z,
                            PolynomialLinearMap.applyPolynomial_add_left,
                            polynomialPure_add_Z, ha, hb]
                      | single bz fz =>
                          change polynomialTransformPath
                              (ofLegs
                                (PolynomialVector.monomial bx fx)
                                (PolynomialVector.monomial byDeg fy)
                                (PolynomialVector.monomial bz fz))
                              (polynomialPure (K := K) (ofLegs
                                (PolynomialVector.monomial ax vx)
                                (PolynomialVector.monomial ay vy)
                                (PolynomialVector.monomial az vz))) =
                            polynomialPure (K := K) (ofLegs
                              (PolynomialLinearMap.applyPolynomial
                                (PolynomialVector.monomial bx fx)
                                (PolynomialVector.monomial ax vx))
                              (PolynomialLinearMap.applyPolynomial
                                (PolynomialVector.monomial byDeg fy)
                                (PolynomialVector.monomial ay vy))
                              (PolynomialLinearMap.applyPolynomial
                                (PolynomialVector.monomial bz fz)
                                (PolynomialVector.monomial az vz)))
                          simp only [polynomialPure_monomial,
                            polynomialTransformPath_monomial,
                            polynomialTransform_pure,
                            PolynomialLinearMap.applyPolynomial_monomial]
                          have hvec :
                              (fun c ↦ PolynomialLinearMap.applyVector (K := K)
                                (ofLegs
                                  (V := fun c ↦ PolynomialLinearMap K (W c) (U c))
                                  (PolynomialVector.monomial bx fx)
                                  (PolynomialVector.monomial byDeg fy)
                                  (PolynomialVector.monomial bz fz) c)
                                (ofLegs vx vy vz c)) =
                                ofLegs (V := fun c ↦ PolynomialVector (U c))
                                  (PolynomialVector.monomial bx (fx vx))
                                  (PolynomialVector.monomial byDeg (fy vy))
                                  (PolynomialVector.monomial bz (fz vz)) := by
                            funext c
                            cases c <;> simp
                          rw [hvec, polynomialPure_monomial,
                            PolynomialVector.shift_monomial]
                          rw [show ax + ay + az + (bx + byDeg + bz) =
                            (bx + ax) + (byDeg + ay) + (bz + az) by omega]

/-- Coordinate-free form of `polynomialTransformPath_polynomialPure_ofLegs`. -/
theorem polynomialTransformPath_polynomialPure
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (x : ∀ c, PolynomialVector (W c)) :
    polynomialTransformPath B (polynomialPure (K := K) x) =
      polynomialPure (K := K)
        (fun c ↦ PolynomialLinearMap.applyPolynomial (B c) (x c)) := by
  rw [← ofLegs_eta B, ← ofLegs_eta x]
  exact polynomialTransformPath_polynomialPure_ofLegs _ _ _ _ _ _

/-- On pure tensors, Cauchy composition of polynomial map families agrees with successive
polynomial transformation. -/
theorem polynomialTransform_comp_pure
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (x : ∀ c, V c) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.comp (B c) (A c))
        (pure x) =
      polynomialTransformPath B (polynomialTransform A (pure x)) := by
  rw [polynomialTransform_pure, polynomialTransform_pure,
    polynomialTransformPath_polynomialPure]
  congr 1
  funext c
  exact PolynomialLinearMap.applyVector_comp (B c) (A c) (x c)

/-- Cauchy composition of polynomial map families agrees with successive transformation. -/
theorem polynomialTransform_comp
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T : Tensor3 K V) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.comp (B c) (A c)) T =
      polynomialTransformPath B (polynomialTransform A T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    rw [polynomialTransform_smul, polynomialTransform_smul,
      polynomialTransformPath_smul]
    congr 1
    exact polynomialTransform_comp_pure B A x
  · intro T S hT hS
    rw [polynomialTransform_add, polynomialTransform_add,
      polynomialTransformPath_add, hT, hS]

namespace PolynomialLinearMap

/-- Evaluation commutes with parameter dilation. -/
theorem applyVector_dilate {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (d : ℕ) (A : PolynomialLinearMap K M N) (x : M) :
    applyVector (dilate d A) x =
      PolynomialVector.dilation d (applyVector A x) := by
  exact (Finsupp.mapDomain_mapRange (fun n ↦ d * n) A
    (fun f : M →ₗ[K] N ↦ f x) (by simp) (by simp)).symm

end PolynomialLinearMap

/-- Dilating all three polynomial vectors of a polynomial pure tensor dilates its total degree. -/
theorem polynomialPure_dilation_ofLegs
    (N : ℕ)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs
        (PolynomialVector.dilation N xX)
        (PolynomialVector.dilation N xY)
        (PolynomialVector.dilation N xZ)) =
      PolynomialVector.dilation N
        (polynomialPure (K := K) (ofLegs xX xY xZ)) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [PolynomialVector.dilation_add, polynomialPure_add_X, ha, hb]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [PolynomialVector.dilation_add, polynomialPure_add_Y, ha, hb]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [PolynomialVector.dilation_add, polynomialPure_add_Z, ha, hb]
          | single dz vz =>
              change polynomialPure (K := K) (ofLegs
                  (PolynomialVector.dilation N (PolynomialVector.monomial dx vx))
                  (PolynomialVector.dilation N (PolynomialVector.monomial dy vy))
                  (PolynomialVector.dilation N (PolynomialVector.monomial dz vz))) =
                PolynomialVector.dilation N
                  (polynomialPure (K := K) (ofLegs
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy)
                    (PolynomialVector.monomial dz vz)))
              simp only [PolynomialVector.dilation_monomial, polynomialPure_monomial]
              simp [Nat.mul_add, Nat.add_assoc]

/-- Coordinate-free form of `polynomialPure_dilation_ofLegs`. -/
theorem polynomialPure_dilation (N : ℕ)
    (x : ∀ c, PolynomialVector (V c)) :
    polynomialPure (K := K) (fun c ↦ PolynomialVector.dilation N (x c)) =
      PolynomialVector.dilation N (polynomialPure (K := K) x) := by
  rw [← ofLegs_eta x]
  exact polynomialPure_dilation_ofLegs N _ _ _

/-- Dilating every map family dilates the resulting pure tensor path. -/
theorem polynomialTransform_dilate_pure
    (N : ℕ) (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (x : ∀ c, V c) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.dilate N (A c)) (pure x) =
      PolynomialVector.dilation N (polynomialTransform A (pure x)) := by
  rw [polynomialTransform_pure, polynomialTransform_pure]
  simp_rw [PolynomialLinearMap.applyVector_dilate]
  exact polynomialPure_dilation N _

/-- Replacing `ε` by `ε^N` in all map families dilates the total transformed path. -/
theorem polynomialTransform_dilate
    (N : ℕ) (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T : Tensor3 K V) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.dilate N (A c)) T =
      PolynomialVector.dilation N (polynomialTransform A T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    rw [polynomialTransform_smul, polynomialTransform_smul,
      PolynomialVector.dilation_smul]
    congr 1
    exact polynomialTransform_dilate_pure N A x
  · intro T S hT hS
    rw [polynomialTransform_add, polynomialTransform_add,
      PolynomialVector.dilation_add, hT, hS]

namespace HasLeadingTerm

/-- Successive degeneration paths compose after dilating the first parameter by `e + 1`.
The dilation gap prevents higher-order errors in the first path from reaching the new leading
degree.

Given a path `P` in the middle space with leading term `S` in degree `d`, and map families `B`
from the middle space into the final space such that transforming `S` by `B` has leading term
`R` in degree `e`, the path obtained by dilating `P` by `e + 1` and then applying `B` pathwise
has leading term `R` in degree `(e + 1) * d + e`.

Proof sketch: Dilating `P` by `N = e + 1` places its coefficients in degrees `N * k`, with the
leading coefficient `S` moved to degree `a = N * d`; by the dilation-gap lemma every other
coefficient of the dilated path vanishes below the boundary `N * (d + 1) = a + e + 1`.
Applying `B` pathwise shifts the transform of each coefficient up by its degree, so the leading
coefficient contributes `shift a (polynomialTransform B S)`, whose coefficients in the window
`[a, a + e]` are exactly the first `e + 1` coefficients of `polynomialTransform B S`: the value
`R` in degree `a + e` and zeros below it.  Every other coefficient of the dilated path sits at
degree `a + e + 1` or higher and cannot contribute at or below `a + e`.  Splitting the
transformed sum at the single index `a` (legitimate because `S ≠ 0` keeps `a` in the support)
therefore yields leading term `R` in degree `(e + 1) * d + e`. -/
theorem transformPath_dilation
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    {P : PolynomialTensor K W} {d : ℕ} {S : Tensor3 K W}
    (hP : HasLeadingTerm P d S)
    (B : ∀ c, PolynomialLinearMap K (W c) (U c))
    {e : ℕ} {R : Tensor3 K U}
    (hB : HasLeadingTerm (polynomialTransform B S) e R)
    (hS : S ≠ 0) :
    HasLeadingTerm
      (polynomialTransformPath B (PolynomialVector.dilation (e + 1) P))
      ((e + 1) * d + e) R := by
  let a := (e + 1) * d
  let boundary := (e + 1) * (d + 1)
  have hab : a + e < boundary := by
    dsimp [a, boundary]
    rw [Nat.mul_add]
    omega
  have haCoeff : PolynomialVector.dilation (e + 1) P a = S := by
    dsimp [a]
    exact (PolynomialVector.dilation_coeff (by omega) P d).trans hP.coeff
  constructor
  · rw [polynomialTransformPath, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single a]
    · rw [haCoeff]
      change PolynomialVector.shift a (polynomialTransform B S) (a + e) = R
      rw [PolynomialVector.shift_apply, if_pos (Nat.le_add_right a e),
        Nat.add_sub_cancel_left]
      exact hB.coeff
    · intro n hn hna
      have hkn : a + e < n := by
        by_contra hnot
        have hnle : n ≤ a + e := Nat.le_of_not_gt hnot
        have hnBoundary : n < boundary := hnle.trans_lt hab
        have hnzero : PolynomialVector.dilation (e + 1) P n = 0 :=
          hP.dilation_gap hnBoundary hna
        exact hn hnzero
      rw [PolynomialVector.shift_apply, if_neg (Nat.not_le_of_gt hkn)]
    · intro hazero
      exact (hS (haCoeff.symm.trans hazero)).elim
  · intro k hk
    rw [polynomialTransformPath, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single a]
    · rw [haCoeff]
      change PolynomialVector.shift a (polynomialTransform B S) k = 0
      rw [PolynomialVector.shift_apply]
      by_cases hak : a ≤ k
      · rw [if_pos hak]
        have hdiff : k - a < e := by omega
        exact hB.lower_coeff hdiff
      · rw [if_neg hak]
    · intro n hn hna
      have hkn : k < n := by
        by_contra hnot
        have hnle : n ≤ k := Nat.le_of_not_gt hnot
        have hnBoundary : n < boundary := hnle.trans_lt (hk.trans hab)
        have hnzero : PolynomialVector.dilation (e + 1) P n = 0 :=
          hP.dilation_gap hnBoundary hna
        exact hn hnzero
      rw [PolynomialVector.shift_apply, if_neg (Nat.not_le_of_gt hkn)]
    · intro hazero
      exact (hS (haCoeff.symm.trans hazero)).elim

end HasLeadingTerm

/-- Polynomial tensor-map products transform an external product of pure tensors as expected. -/
theorem polynomialTransform_external_pure
    {U U' : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    [∀ i, AddCommMonoid (U' i)] [∀ i, Module K (U' i)]
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (B : ∀ c, PolynomialLinearMap K (U c) (U' c))
    (x : ∀ c, V c) (y : ∀ c, U c) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.tensor (A c) (B c))
        (external (pure x) (pure y)) =
      polynomialExternal (polynomialTransform A (pure x))
        (polynomialTransform B (pure y)) := by
  rw [external_pure, polynomialTransform_pure, polynomialTransform_pure,
    polynomialTransform_pure, polynomialExternal_polynomialPure]
  congr 1
  funext c
  exact PolynomialLinearMap.applyVector_tensor_tmul (A c) (B c) (x c) (y c)

/-- Polynomial transformation commutes with external tensor products when the map families are
combined coefficientwise by Cauchy product. -/
theorem polynomialTransform_external
    {U U' : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    [∀ i, AddCommMonoid (U' i)] [∀ i, Module K (U' i)]
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (B : ∀ c, PolynomialLinearMap K (U c) (U' c))
    (T : Tensor3 K V) (S : Tensor3 K U) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.tensor (A c) (B c))
        (external T S) =
      polynomialExternal (polynomialTransform A T) (polynomialTransform B S) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      rw [external_smul_left, external_smul_right, external_pure,
        polynomialTransform_smul, polynomialTransform_smul,
        polynomialTransform_smul, polynomialTransform_smul,
        polynomialExternal_smul_left, polynomialExternal_smul_right, smul_smul]
      rw [← smul_smul]
      exact congrArg (fun z ↦ a • b • z)
        (by simpa using polynomialTransform_external_pure A B x y)
    · intro S₁ S₂ h₁ h₂
      rw [external_add_right, polynomialTransform_add, polynomialTransform_add,
        polynomialExternal_add_right, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    rw [external_add_left, polynomialTransform_add, polynomialTransform_add,
      polynomialExternal_add_left, h₁, h₂]

/-- Polynomial transformation commutes with finite list sums. -/
theorem polynomialTransform_list_sum
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (terms : List (Tensor3 K V)) :
    polynomialTransform A terms.sum =
      (terms.map (polynomialTransform A)).sum := by
  induction terms with
  | nil => simp
  | cons T terms ih => simp [polynomialTransform_add, ih]

/-- Polynomial transformation commutes with sums indexed by a finite type. -/
theorem polynomialTransform_fintype_sum {I : Type*} [Fintype I]
    (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T : I → Tensor3 K V) :
    polynomialTransform A (∑ i, T i) = ∑ i, polynomialTransform A (T i) := by
  classical
  have hfinset : ∀ s : Finset I,
      polynomialTransform A (∑ i ∈ s, T i) =
        ∑ i ∈ s, polynomialTransform A (T i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, polynomialTransform_add, Finset.sum_insert hi, ih]
  simpa using hfinset Finset.univ

/-- Constant polynomial map families recover ordinary tensor restriction. -/
theorem polynomialTransform_constant (f : ∀ c, V c →ₗ[K] W c)
    (T : Tensor3 K V) :
    polynomialTransform (fun c ↦ PolynomialLinearMap.constant (f c)) T =
      PolynomialVector.constant (map f T) := by
  classical
  simp [polynomialTransform, PolynomialLinearMap.constant,
    PolynomialLinearMap.monomial, PolynomialVector.constant,
    PolynomialVector.monomial]

/-- Constructive polynomial degeneration by independent maps on the three legs. -/
def PolynomialDegenerates (T : Tensor3 K V) (S : Tensor3 K W) : Prop :=
  ∃ (A : ∀ c, PolynomialLinearMap K (V c) (W c)) (d : ℕ),
    HasLeadingTerm (polynomialTransform A T) d S

/-- A polynomial degeneration with its leading degree retained in the proposition.

Keeping this degree visible is essential when the degeneration is tensor-powered: the degree
then grows linearly, so coefficient extraction incurs only a polynomial overhead. -/
def PolynomialDegeneratesAt (d : ℕ) (T : Tensor3 K V) (S : Tensor3 K W) : Prop :=
  ∃ A : ∀ c, PolynomialLinearMap K (V c) (W c),
    HasLeadingTerm (polynomialTransform A T) d S

/-- Order-style notation: `S ⊴ T` means that `T` polynomially degenerates to `S`. -/
scoped infix:50 " ⊴ " => fun S T ↦ PolynomialDegenerates T S

namespace PolynomialDegeneratesAt

/-- Forgetting the displayed leading degree gives an ordinary polynomial degeneration. -/
theorem toPolynomialDegenerates {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) : PolynomialDegenerates T S := by
  rcases h with ⟨A, hA⟩
  exact ⟨A, d, hA⟩

/-- Every exact restriction is a degree-zero polynomial degeneration. -/
theorem of_restricts {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : PolynomialDegeneratesAt 0 T S := by
  rcases h with ⟨f, rfl⟩
  refine ⟨fun c ↦ PolynomialLinearMap.constant (f c), ?_⟩
  rw [polynomialTransform_constant]
  exact HasLeadingTerm.monomial 0 (map f T)

/-- Every tensor polynomially degenerates to itself with leading degree zero. -/
theorem refl (T : Tensor3 K V) : PolynomialDegeneratesAt 0 T T :=
  of_restricts (Restricts.refl T)

/-- Every tensor degenerates to itself with displayed leading degree one.

This positive-degree form is useful when synchronizing a finite family of otherwise unrelated
degenerations: unlike degree zero, positive degrees can be brought to a common multiple by
dilating the degeneration parameter.

Proof sketch: multiply the identity map on the `X` leg by `ε`, and use constant identity maps
on `Y` and `Z`.  Trilinearity makes the transformed tensor exactly the monomial `ε T`. -/
theorem refl_one (T : Tensor3 K V) : PolynomialDegeneratesAt 1 T T := by
  let A : ∀ c, PolynomialLinearMap K (V c) (V c) :=
    ofLegs (PolynomialLinearMap.monomial 1 LinearMap.id)
      (PolynomialLinearMap.constant LinearMap.id)
      (PolynomialLinearMap.constant LinearMap.id)
  refine ⟨A, ?_⟩
  have hmap : map (ofLegs (LinearMap.id : V .X →ₗ[K] V .X)
      (LinearMap.id : V .Y →ₗ[K] V .Y)
      (LinearMap.id : V .Z →ₗ[K] V .Z)) T = T := by
    rw [show ofLegs (LinearMap.id : V .X →ₗ[K] V .X)
        (LinearMap.id : V .Y →ₗ[K] V .Y)
        (LinearMap.id : V .Z →ₗ[K] V .Z) =
        (fun c ↦ LinearMap.id (R := K) (M := V c)) by
      funext c
      cases c <;> rfl]
    rw [map_id]
    rfl
  have htransform : polynomialTransform A T = PolynomialVector.monomial 1 T := by
    ext d
    simp [A, PolynomialLinearMap.constant, polynomialTransform,
      PolynomialLinearMap.monomial, PolynomialVector.monomial, hmap]
  rw [htransform]
  exact HasLeadingTerm.monomial 1 T

/-- Degree-aware transitivity.  The gap construction dilates the first path by `e + 1`, so the
composite leading degree is `(e + 1) * d + e`.

If `T` polynomially degenerates to `S` with leading degree `d`, and `S` polynomially
degenerates to `R` with leading degree `e`, then `T` polynomially degenerates to `R` with
leading degree `(e + 1) * d + e`.

Proof sketch: Take witnessing map families `A` (transforming `T` to a path with leading term
`S` in degree `d`) and `B` (transforming `S` to a path with leading term `R` in degree `e`).
The composite witness is `fun c ↦ (B c).comp (dilate (e + 1) (A c))`: by
`polynomialTransform_comp` and `polynomialTransform_dilate`, transforming `T` by this family
first dilates the `A`-path by `e + 1` and then applies `B` pathwise.  The dilation opens a gap
of `e + 1` degrees between the leading coefficient `S` and the higher-order error terms of the
`A`-path, so those errors cannot interfere with the `e + 1` low-order coefficients contributed
by `B` applied to `S`; `HasLeadingTerm.transformPath_dilation` then gives leading term `R` in
degree `(e + 1) * d + e`.  In the degenerate case `S = 0` the second leading term forces
`R = 0`, and the zero map family is a witness. -/
theorem trans
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    {d e : ℕ} {T : Tensor3 K V} {S : Tensor3 K W} {R : Tensor3 K U}
    (hTS : PolynomialDegeneratesAt d T S) (hSR : PolynomialDegeneratesAt e S R) :
    PolynomialDegeneratesAt ((e + 1) * d + e) T R := by
  rcases hTS with ⟨A, hA⟩
  rcases hSR with ⟨B, hB⟩
  by_cases hS : S = 0
  · subst S
    have hR : R = 0 := by
      have hcoeff := hB.coeff
      rw [polynomialTransform_zero] at hcoeff
      exact hcoeff.symm
    subst R
    let Z : ∀ c, PolynomialLinearMap K (V c) (U c) := fun _ ↦ 0
    refine ⟨Z, ?_⟩
    have htransform : polynomialTransform Z T = 0 := by
      rw [← ofLegs_eta Z]
      exact polynomialTransform_zero_maps_X (Z .Y) (Z .Z) T
    rw [htransform]
    exact HasLeadingTerm.zero _
  · refine ⟨fun c ↦ PolynomialLinearMap.comp (B c)
        (PolynomialLinearMap.dilate (e + 1) (A c)), ?_⟩
    rw [polynomialTransform_comp, polynomialTransform_dilate]
    exact hA.transformPath_dilation B hB hS

/-- Displayed leading degrees add under external tensor products. -/
theorem external
    {U U' : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    [∀ i, AddCommMonoid (U' i)] [∀ i, Module K (U' i)]
    {d e : ℕ} {T : Tensor3 K V} {T' : Tensor3 K W}
    {S : Tensor3 K U} {S' : Tensor3 K U'}
    (hT : PolynomialDegeneratesAt d T T') (hS : PolynomialDegeneratesAt e S S') :
    PolynomialDegeneratesAt (d + e) (Tensor.external T S) (Tensor.external T' S') := by
  rcases hT with ⟨A, hA⟩
  rcases hS with ⟨B, hB⟩
  refine ⟨fun c ↦ PolynomialLinearMap.tensor (A c) (B c), ?_⟩
  rw [polynomialTransform_external]
  exact hA.external hB

end PolynomialDegeneratesAt

namespace PolynomialDegenerates

/-- Every polynomial degeneration has some displayed leading degree. -/
theorem exists_at {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) : ∃ d, PolynomialDegeneratesAt d T S := by
  rcases h with ⟨A, d, hA⟩
  exact ⟨d, A, hA⟩

/-- Every polynomial degeneration can be represented at a strictly positive displayed degree.

Proof sketch: recover any displayed degree `d`, then compose with the degree-one identity
degeneration of the target.  Degree-aware transitivity produces degree `2d+1`. -/
theorem exists_at_pos {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) :
    ∃ d, 0 < d ∧ PolynomialDegeneratesAt d T S := by
  obtain ⟨d, hd⟩ := h.exists_at
  refine ⟨2 * d + 1, by omega, ?_⟩
  simpa using hd.trans (PolynomialDegeneratesAt.refl_one S)

/-- Every exact restriction is a polynomial degeneration: if legwise maps carry the source `T`
to the target `S`, then `T` polynomially degenerates to `S`.  This is the degree-forgetting
corollary of `PolynomialDegeneratesAt.of_restricts`, whose constant map family displays leading
degree zero. -/
theorem of_restricts {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : PolynomialDegenerates T S :=
  (PolynomialDegeneratesAt.of_restricts h).toPolynomialDegenerates

/-- Every tensor polynomially degenerates to itself. -/
theorem refl (T : Tensor3 K V) : PolynomialDegenerates T T :=
  of_restricts (Restricts.refl T)

/-- Polynomial degeneration is transitive: if the source `T` polynomially degenerates to `S`
and `S` polynomially degenerates to `R`, then `T` polynomially degenerates to `R`.

Proof sketch: this is the degree-forgetting corollary of `PolynomialDegeneratesAt.trans`.
Recover displayed leading degrees `d` and `e` for the two given degenerations, apply the
degree-aware transitivity — which dilates the first path by `e + 1` before composing the map
families, producing leading degree `(e + 1) * d + e` — and then forget that degree again. -/
theorem trans
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    {T : Tensor3 K V} {S : Tensor3 K W} {R : Tensor3 K U}
    (hTS : PolynomialDegenerates T S) (hSR : PolynomialDegenerates S R) :
    PolynomialDegenerates T R := by
  obtain ⟨d, hd⟩ := hTS.exists_at
  obtain ⟨e, he⟩ := hSR.exists_at
  exact (hd.trans he).toPolynomialDegenerates

/-- Polynomial degenerations are compatible with external tensor products: if `T` degenerates
to `T'` and `S` degenerates to `S'`, then `external T S` degenerates to `external T' S'`.  This
is the degree-forgetting corollary of `PolynomialDegeneratesAt.external`, which combines the two
map families by legwise Cauchy product and adds the displayed leading degrees. -/
theorem external
    {U U' : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    [∀ i, AddCommMonoid (U' i)] [∀ i, Module K (U' i)]
    {T : Tensor3 K V} {T' : Tensor3 K W}
    {S : Tensor3 K U} {S' : Tensor3 K U'}
    (hT : PolynomialDegenerates T T') (hS : PolynomialDegenerates S S') :
    PolynomialDegenerates (Tensor.external T S) (Tensor.external T' S') := by
  obtain ⟨d, hd⟩ := hT.exists_at
  obtain ⟨e, he⟩ := hS.exists_at
  exact (hd.external he).toPolynomialDegenerates

end PolynomialDegenerates

/-- Termwise description of dilating a sum of polynomial pure tensors by `e + 1` and then
applying the map families `B` pathwise; used by `BorderRankLE.of_polynomialDegenerates` to
transform a border-rank certificate term by term. -/
private theorem polynomialTransformPath_dilation_list
    (B : ∀ c, PolynomialLinearMap K (V c) (W c)) (e : ℕ)
    (terms : List (∀ c, PolynomialVector (V c))) :
    (terms.map fun x ↦ polynomialPure (K := K) (fun c ↦
        PolynomialLinearMap.applyPolynomial (B c)
          (PolynomialVector.dilation (e + 1) (x c)))).sum =
      polynomialTransformPath B
        (PolynomialVector.dilation (e + 1)
          (terms.map (polynomialPure (K := K))).sum) := by
  induction terms with
  | nil => simp
  | cons x terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [PolynomialVector.dilation_add, polynomialTransformPath_add, ih,
        ← polynomialPure_dilation, polynomialTransformPath_polynomialPure]

namespace BorderRankLE

/-- Constructive border rank is monotone under polynomial degeneration.  The certificate path is
dilated before applying the degeneration maps, using the same gap construction as transitivity. -/
theorem of_polynomialDegenerates {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : BorderRankLE r T) (hTS : PolynomialDegenerates T S) :
    BorderRankLE r S := by
  rcases hT with ⟨d, terms, hlen, hlead⟩
  rcases hTS with ⟨B, e, hB⟩
  by_cases hzero : T = 0
  · subst T
    have hS : S = 0 := by
      have hcoeff := hB.coeff
      rw [polynomialTransform_zero] at hcoeff
      exact hcoeff.symm
    subst S
    exact BorderRankLE.zero.mono (Nat.zero_le r)
  · let newTerms : List (∀ c, PolynomialVector (W c)) :=
      terms.map fun x c ↦ PolynomialLinearMap.applyPolynomial (B c)
        (PolynomialVector.dilation (e + 1) (x c))
    refine ⟨(e + 1) * d + e, newTerms, ?_, ?_⟩
    · simpa [newTerms] using hlen
    · have hleading := hlead.transformPath_dilation B hB hzero
      have hpath :
          (newTerms.map (polynomialPure (K := K))).sum =
            polynomialTransformPath B
              (PolynomialVector.dilation (e + 1)
                (terms.map (polynomialPure (K := K))).sum) := by
        simpa [newTerms, List.map_map, Function.comp_def] using
          polynomialTransformPath_dilation_list B e terms
      rw [hpath]
      exact hleading

/-- Constructive border rank is monotone under exact restriction. -/
theorem of_restricts {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : BorderRankLE r T) (hTS : Restricts T S) : BorderRankLE r S :=
  hT.of_polynomialDegenerates (PolynomialDegenerates.of_restricts hTS)

/-- Applying legwise linear maps cannot increase constructive border rank. -/
theorem map {r : ℕ} {T : Tensor3 K V} (hT : BorderRankLE r T)
    (f : ∀ c, V c →ₗ[K] W c) : BorderRankLE r (Tensor.map f T) :=
  hT.of_restricts ⟨f, rfl⟩

/-- Constructive border-rank bounds are invariant under legwise linear isomorphism. -/
theorem isomorphic {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hTS : Isomorphic T S) : BorderRankLE r T ↔ BorderRankLE r S := by
  constructor
  · intro hT
    exact hT.of_restricts hTS.restricts
  · intro hS
    exact hS.of_restricts hTS.symm.restricts

/-- Constructive border rank is subadditive under binary direct sums. -/
theorem directSum
    {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    {r s : ℕ} {T : Tensor3 K V} {S : Tensor3 K U}
    (hT : BorderRankLE r T) (hS : BorderRankLE s S) :
    BorderRankLE (r + s) (Tensor.directSum T S) := by
  exact (hT.map includeLeft).add (hS.map includeRight)

end BorderRankLE

namespace RankLE

/-- A rank certificate followed by a degree-aware polynomial degeneration gives a border-rank
certificate at that same displayed degree. -/
theorem borderAt_of_polynomialDegeneratesAt {r d : ℕ}
    {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE r T) (hTS : PolynomialDegeneratesAt d T S) :
    BorderRankLEAt r d S := by
  rcases hT with ⟨terms, hlen, hdecomp⟩
  rcases hTS with ⟨A, hlead⟩
  let polynomialTerms : List (∀ c, PolynomialVector (W c)) :=
    terms.map fun x c ↦ PolynomialLinearMap.applyVector (A c) (x c)
  refine ⟨polynomialTerms, ?_, ?_⟩
  · simpa [polynomialTerms] using hlen
  · have hpath :
        (polynomialTerms.map (polynomialPure (K := K))).sum =
          polynomialTransform A T := by
      rw [hdecomp, polynomialTransform_list_sum]
      simp [polynomialTerms, List.map_map, Function.comp_def,
        polynomialTransform_pure]
    rw [hpath]
    exact hlead

/-- A rank certificate followed by a polynomial degeneration gives a border-rank certificate. -/
theorem border_of_polynomialDegenerates {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE r T) (hTS : PolynomialDegenerates T S) : BorderRankLE r S := by
  rcases hTS.exists_at with ⟨d, hd⟩
  exact (hT.borderAt_of_polynomialDegeneratesAt hd).toBorderRankLE

/-- Ordinary rank is an upper bound for constructive border rank. -/
theorem toBorderRankLE {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T) :
    BorderRankLE r T :=
  hT.border_of_polynomialDegenerates (PolynomialDegenerates.refl T)

end RankLE

end AlgebraicComplexity.Tensor
