/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Rank

/-!
# Polynomial paths of tensors

This file provides the constructive polynomial language used for border-rank and degeneration
certificates.  A polynomial vector is represented by its finitely supported coefficient function.
The pure tensor of three polynomial vectors is formed by convolution of degrees.

Keeping coefficients in the original modules, rather than choosing bases or moving to a
topological closure, makes certificates exact and usable over arbitrary commutative semirings.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- A polynomial with coefficients in an additive module. -/
abbrev PolynomialVector (M : Type*) [Zero M] := ℕ →₀ M

/-- A polynomial path in a three-legged tensor space. -/
abbrev PolynomialTensor (K : Type u) [CommSemiring K] (V : Leg → Type v)
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)] :=
  PolynomialVector (Tensor3 K V)

namespace PolynomialVector

/-- The monomial `ε^d v`. -/
noncomputable def monomial {M : Type*} [Zero M] (d : ℕ) (v : M) : PolynomialVector M :=
  Finsupp.single d v

/-- A constant polynomial vector. -/
noncomputable def constant {M : Type*} [Zero M] (v : M) : PolynomialVector M :=
  monomial 0 v

/-- Apply a linear map coefficientwise to a polynomial vector. -/
noncomputable def mapLinear {M N : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) : PolynomialVector M →ₗ[K] PolynomialVector N :=
  Finsupp.mapRange.linearMap f

/-- The degree-`d` coefficient of `mapLinear f P` is `f` applied to the degree-`d` coefficient
of `P`. -/
@[simp] theorem mapLinear_apply {M N : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) (P : PolynomialVector M) (d : ℕ) :
    mapLinear f P d = f (P d) := by
  rfl

/-- Applying a linear map coefficientwise sends the monomial `ε^d x` to `ε^d (f x)`. -/
@[simp] theorem mapLinear_monomial {M N : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) (d : ℕ) (x : M) :
    mapLinear f (monomial d x) = monomial d (f x) := by
  ext
  simp [mapLinear, monomial]

/-- The coefficient of the monomial `ε^d v` in its own degree `d` is `v`. -/
@[simp] theorem monomial_coeff_same {M : Type*} [Zero M] (d : ℕ) (v : M) :
    monomial d v d = v := by
  simp [monomial]

/-- The monomial `ε^d v` has coefficient zero in every degree `e ≠ d`. -/
@[simp] theorem monomial_coeff_of_ne {M : Type*} [Zero M]
    {d e : ℕ} (h : e ≠ d) (v : M) : monomial d v e = 0 := by
  simp [monomial, h]

/-- The monomial with zero coefficient is the zero polynomial vector. -/
@[simp] theorem monomial_zero {M : Type*} [AddZeroClass M] (d : ℕ) :
    monomial d (0 : M) = 0 := by
  simp [monomial]

/-- Monomial formation in a fixed degree is additive in the coefficient. -/
@[simp] theorem monomial_add {M : Type*} [AddZeroClass M] (d : ℕ) (v w : M) :
    monomial d (v + w) = monomial d v + monomial d w := by
  exact Finsupp.single_add d v w

/-- Monomial formation in a fixed degree commutes with scalar multiplication. -/
@[simp] theorem monomial_smul {M : Type*} [AddCommMonoid M] [Module K M]
    (r : K) (d : ℕ) (v : M) :
    monomial d (r • v) = r • monomial d v := by
  ext
  simp [monomial]

/-- Cauchy convolution of polynomial vectors through a bilinear map. -/
noncomputable def convolution
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P)
    (f : PolynomialVector M) (g : PolynomialVector N) : PolynomialVector P :=
  f.sum fun i x ↦ g.sum fun j y ↦ monomial (i + j) (B x y)

/-- Convolution through a bilinear map with the zero polynomial vector on the left is zero. -/
@[simp] theorem convolution_zero_left
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) (g : PolynomialVector N) :
    convolution B 0 g = 0 := by
  simp [convolution]

/-- Convolution through a bilinear map with the zero polynomial vector on the right is zero. -/
@[simp] theorem convolution_zero_right
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) (f : PolynomialVector M) :
    convolution B f 0 = 0 := by
  simp [convolution]

/-- Convolution through a bilinear map is additive in its left argument. -/
theorem convolution_add_left
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P)
    (f₁ f₂ : PolynomialVector M) (g : PolynomialVector N) :
    convolution B (f₁ + f₂) g = convolution B f₁ g + convolution B f₂ g := by
  classical
  simp [convolution, Finsupp.sum_add_index']

/-- Convolution through a bilinear map is additive in its right argument. -/
theorem convolution_add_right
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P)
    (f : PolynomialVector M) (g₁ g₂ : PolynomialVector N) :
    convolution B f (g₁ + g₂) = convolution B f g₁ + convolution B f g₂ := by
  classical
  simp [convolution, Finsupp.sum_add_index']

/-- Convolution through a bilinear map commutes with scalar multiplication of the left
argument. -/
theorem convolution_smul_left
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) (r : K)
    (f : PolynomialVector M) (g : PolynomialVector N) :
    convolution B (r • f) g = r • convolution B f g := by
  classical
  simp [convolution, Finsupp.sum_smul_index', monomial, Finsupp.smul_sum]

/-- Convolution through a bilinear map commutes with scalar multiplication of the right
argument. -/
theorem convolution_smul_right
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) (r : K)
    (f : PolynomialVector M) (g : PolynomialVector N) :
    convolution B f (r • g) = r • convolution B f g := by
  classical
  simp [convolution, Finsupp.sum_smul_index', monomial, Finsupp.smul_sum]

/-- The convolution of the monomials `ε^i x` and `ε^j y` is the monomial `ε^(i+j) (B x y)`:
degrees add and coefficients multiply through the bilinear map. -/
@[simp] theorem convolution_monomial
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) (i j : ℕ) (x : M) (y : N) :
    convolution B (monomial i x) (monomial j y) = monomial (i + j) (B x y) := by
  classical
  simp [convolution, monomial]

/-- Coefficient formula for polynomial-vector convolution. -/
theorem convolution_coeff
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P)
    (f : PolynomialVector M) (g : PolynomialVector N) (n : ℕ) :
    convolution B f g n =
      ∑ i ∈ f.support, ∑ j ∈ g.support,
        if i + j = n then B (f i) (g j) else 0 := by
  classical
  simp [convolution, monomial, Finsupp.sum, Finsupp.single_apply, eq_comm]

/-- Substitute `ε^N` for `ε`, multiplying every supported degree by `N`. -/
noncomputable def dilation {M : Type*} [AddCommMonoid M]
    (N : ℕ) (P : PolynomialVector M) : PolynomialVector M :=
  Finsupp.mapDomain (fun d ↦ N * d) P

/-- Dilation by `N` sends the monomial `ε^d x` to `ε^(N*d) x`. -/
@[simp] theorem dilation_monomial {M : Type*} [AddCommMonoid M]
    (N d : ℕ) (x : M) :
    dilation N (monomial d x) = monomial (N * d) x := by
  simp [dilation, monomial]

/-- Dilation of the zero polynomial vector is zero. -/
@[simp] theorem dilation_zero {M : Type*} [AddCommMonoid M] (N : ℕ) :
    dilation N (0 : PolynomialVector M) = 0 := by
  simp [dilation]

/-- Dilation is additive in the polynomial vector. -/
theorem dilation_add {M : Type*} [AddCommMonoid M]
    (N : ℕ) (P Q : PolynomialVector M) :
    dilation N (P + Q) = dilation N P + dilation N Q := by
  exact Finsupp.mapDomain_add

/-- Dilation commutes with scalar multiplication. -/
theorem dilation_smul {M : Type*} [AddCommMonoid M] [Module K M]
    (N : ℕ) (r : K) (P : PolynomialVector M) :
    dilation N (r • P) = r • dilation N P := by
  exact Finsupp.mapDomain_smul r P

/-- For positive `N`, the coefficient of `dilation N P` in degree `N * d` is the coefficient of
`P` in degree `d`. -/
theorem dilation_coeff {M : Type*} [AddCommMonoid M]
    {N : ℕ} (hN : 0 < N) (P : PolynomialVector M) (d : ℕ) :
    dilation N P (N * d) = P d := by
  exact Finsupp.mapDomain_apply (fun _ _ h ↦ Nat.mul_left_cancel hN h) P d

/-- Multiply a polynomial vector by the scalar monomial `ε^n`. -/
noncomputable def shift {M : Type*} [AddCommMonoid M]
    (n : ℕ) (P : PolynomialVector M) : PolynomialVector M :=
  Finsupp.mapDomain (fun d ↦ n + d) P

/-- Coefficients of a shifted polynomial vector. -/
theorem shift_apply {M : Type*} [AddCommMonoid M]
    (n : ℕ) (P : PolynomialVector M) (k : ℕ) :
    shift n P k = if n ≤ k then P (k - n) else 0 := by
  by_cases hnk : n ≤ k
  · have hk : n + (k - n) = k := Nat.add_sub_of_le hnk
    rw [if_pos hnk, ← hk, shift]
    simpa using Finsupp.mapDomain_apply
      (f := fun d ↦ n + d) (fun _ _ h ↦ Nat.add_left_cancel h) P (k - n)
  · rw [shift]
    rw [Finsupp.mapDomain_of_not_mem_image_support]
    · simp [hnk]
    · rintro ⟨d, hd, hEq⟩
      apply hnk
      rw [← hEq]
      exact Nat.le_add_right n d

/-- Shifting by `n` sends the monomial `ε^d x` to `ε^(n+d) x`. -/
@[simp] theorem shift_monomial {M : Type*} [AddCommMonoid M]
    (n d : ℕ) (x : M) :
    shift n (monomial d x) = monomial (n + d) x := by
  simp [shift, monomial]

/-- Shifting the zero polynomial vector gives zero. -/
@[simp] theorem shift_zero {M : Type*} [AddCommMonoid M] (n : ℕ) :
    shift n (0 : PolynomialVector M) = 0 := by
  simp [shift]

/-- Shifting is additive in the polynomial vector. -/
theorem shift_add {M : Type*} [AddCommMonoid M]
    (n : ℕ) (P Q : PolynomialVector M) :
    shift n (P + Q) = shift n P + shift n Q := by
  exact Finsupp.mapDomain_add

/-- Shifting commutes with scalar multiplication. -/
theorem shift_smul {M : Type*} [AddCommMonoid M] [Module K M]
    (n : ℕ) (r : K) (P : PolynomialVector M) :
    shift n (r • P) = r • shift n P := by
  exact Finsupp.mapDomain_smul r P

end PolynomialVector

open PolynomialVector

/-- Convolutional pure tensor of three polynomial vectors. -/
noncomputable def polynomialPure (x : ∀ c, PolynomialVector (V c)) : PolynomialTensor K V :=
  (x .X).sum fun dx vx ↦
    (x .Y).sum fun dy vy ↦
      (x .Z).sum fun dz vz ↦
        monomial (dx + dy + dz) (pure (K := K) (ofLegs vx vy vz))

/-- The pure tensor of three monomials is the corresponding tensor monomial. -/
@[simp] theorem polynomialPure_monomial (dx dy dz : ℕ)
    (x : V .X) (y : V .Y) (z : V .Z) :
    polynomialPure (K := K)
        (ofLegs (monomial dx x) (monomial dy y) (monomial dz z)) =
      monomial (dx + dy + dz) (pure (K := K) (ofLegs x y z)) := by
  classical
  simp [polynomialPure, monomial, ofLegs]

/-- The convolutional pure tensor is additive in its `X` polynomial vector. -/
@[simp] theorem polynomialPure_add_X (x₁ x₂ : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs (x₁ + x₂) y z) =
      polynomialPure (K := K) (ofLegs x₁ y z) +
        polynomialPure (K := K) (ofLegs x₂ y z) := by
  classical
  simp [polynomialPure, Finsupp.sum_add_index', ofLegs]

/-- The convolutional pure tensor is additive in its `Y` polynomial vector. -/
@[simp] theorem polynomialPure_add_Y (x : PolynomialVector (V .X))
    (y₁ y₂ : PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x (y₁ + y₂) z) =
      polynomialPure (K := K) (ofLegs x y₁ z) +
        polynomialPure (K := K) (ofLegs x y₂ z) := by
  classical
  simp [polynomialPure, Finsupp.sum_add_index', ofLegs]

/-- The convolutional pure tensor is additive in its `Z` polynomial vector. -/
@[simp] theorem polynomialPure_add_Z (x : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) (z₁ z₂ : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x y (z₁ + z₂)) =
      polynomialPure (K := K) (ofLegs x y z₁) +
        polynomialPure (K := K) (ofLegs x y z₂) := by
  classical
  simp [polynomialPure, Finsupp.sum_add_index', ofLegs]

/-- The convolutional pure tensor vanishes when its `X` polynomial vector is zero. -/
@[simp] theorem polynomialPure_zero_X (y : PolynomialVector (V .Y))
    (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs 0 y z) = 0 := by
  simp [polynomialPure, ofLegs]

/-- The convolutional pure tensor vanishes when its `Y` polynomial vector is zero. -/
@[simp] theorem polynomialPure_zero_Y (x : PolynomialVector (V .X))
    (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x 0 z) = 0 := by
  simp [polynomialPure, ofLegs]

/-- The convolutional pure tensor vanishes when its `Z` polynomial vector is zero. -/
@[simp] theorem polynomialPure_zero_Z (x : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) :
    polynomialPure (K := K) (ofLegs x y 0) = 0 := by
  simp [polynomialPure, ofLegs]

/-- Constant polynomial vectors produce a constant pure tensor. -/
@[simp] theorem polynomialPure_constant (x : V .X) (y : V .Y) (z : V .Z) :
    polynomialPure (K := K)
        (ofLegs (constant x) (constant y) (constant z)) =
      constant (pure (K := K) (ofLegs x y z)) := by
  simp [constant]

/-- Coordinate-family form of `polynomialPure_constant`. -/
@[simp] theorem polynomialPure_constant_family (x : ∀ c, V c) :
    polynomialPure (K := K) (fun c ↦ constant (x c)) =
      constant (pure (K := K) x) := by
  rw [← ofLegs_eta x]
  convert polynomialPure_constant (K := K) (x .X) (x .Y) (x .Z) using 1
  congr 1
  funext c
  cases c <;> rfl

/-- Explicit three-leg form of coefficientwise naturality for polynomial pure tensors. -/
private theorem polynomialPure_mapLinear_ofLegs
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (fX : V .X →ₗ[K] W .X) (fY : V .Y →ₗ[K] W .Y) (fZ : V .Z →ₗ[K] W .Z)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear (Tensor.map (ofLegs fX fY fZ))
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      polynomialPure (K := K) (ofLegs
        (PolynomialVector.mapLinear fX xX)
        (PolynomialVector.mapLinear fY xY)
        (PolynomialVector.mapLinear fZ xZ)) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb => simp [ha, hb]
          | single dz vz =>
              change PolynomialVector.mapLinear (Tensor.map (ofLegs fX fY fZ))
                    (polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx)
                      (PolynomialVector.monomial dy vy)
                      (PolynomialVector.monomial dz vz))) =
                  polynomialPure (K := K) (ofLegs
                    (PolynomialVector.mapLinear fX (PolynomialVector.monomial dx vx))
                    (PolynomialVector.mapLinear fY (PolynomialVector.monomial dy vy))
                    (PolynomialVector.mapLinear fZ (PolynomialVector.monomial dz vz)))
              rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial]
              simp only [PolynomialVector.mapLinear_monomial]
              rw [polynomialPure_monomial, Tensor.map_pure]
              congr 2
              funext c
              cases c <;> rfl

/-- Legwise linear maps commute with polynomial pure tensors, coefficient by coefficient. -/
theorem polynomialPure_mapLinear
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (f : ∀ c, V c →ₗ[K] W c)
    (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear (Tensor.map f) (polynomialPure (K := K) x) =
      polynomialPure (K := K) (fun c ↦ PolynomialVector.mapLinear (f c) (x c)) := by
  rw [← ofLegs_eta f, ← ofLegs_eta x]
  convert polynomialPure_mapLinear_ofLegs (K := K) (V := V)
    (f .X) (f .Y) (f .Z) (x .X) (x .Y) (x .Z) using 1
  congr 1
  funext c
  cases c <;> rfl

/-- Explicit three-leg form of cyclic naturality for polynomial pure tensors: permuting the legs
of the source path `polynomialPure (ofLegs xX xY xZ)` by the cycle `X ↦ Y ↦ Z ↦ X` gives the
polynomial pure path of the rotated triple `(xZ, xX, xY)`. -/
private theorem polynomialPure_permute_cycle_ofLegs
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) cycle).toLinearMap
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      polynomialPure (K := K) (V := fun i ↦ V (cycle.symm i)) (ofLegs xZ xX xY) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero =>
      simp only [polynomialPure_zero_X, map_zero]
      exact (polynomialPure_zero_Y (K := K) (V := fun i ↦ V (cycle.symm i)) xZ xY).symm
  | add a b ha hb =>
      simp only [polynomialPure_add_X, map_add, ha, hb]
      exact (polynomialPure_add_Y (K := K) (V := fun i ↦ V (cycle.symm i)) xZ a b xY).symm
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero =>
          simp only [polynomialPure_zero_Y, map_zero]
          exact (polynomialPure_zero_Z (K := K) (V := fun i ↦ V (cycle.symm i)) xZ
            (PolynomialVector.monomial dx vx)).symm
      | add a b ha hb =>
          simp only [polynomialPure_add_Y, map_add, ha, hb]
          exact (polynomialPure_add_Z (K := K) (V := fun i ↦ V (cycle.symm i)) xZ
            (PolynomialVector.monomial dx vx) a b).symm
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero =>
              simp only [polynomialPure_zero_Z, map_zero]
              exact (polynomialPure_zero_X (K := K) (V := fun i ↦ V (cycle.symm i))
                (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)).symm
          | add a b ha hb =>
              simp only [polynomialPure_add_Z, map_add, ha, hb]
              exact (polynomialPure_add_X (K := K) (V := fun i ↦ V (cycle.symm i)) a b
                (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)).symm
          | single dz vz =>
              have hfam :
                  (fun i ↦ ofLegs vx vy vz (cycle.symm i)) =
                    ofLegs (V := fun i ↦ V (cycle.symm i)) vz vx vy := by
                funext c
                cases c <;> rfl
              change PolynomialVector.mapLinear
                    (Tensor.permute (K := K) (V := V) cycle).toLinearMap
                    (polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx)
                      (PolynomialVector.monomial dy vy)
                      (PolynomialVector.monomial dz vz))) =
                  polynomialPure (K := K) (V := fun i ↦ V (cycle.symm i)) (ofLegs
                    (PolynomialVector.monomial dz vz)
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy))
              rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial,
                polynomialPure_monomial (K := K) (V := fun i ↦ V (cycle.symm i))
                  dz dx dy vz vx vy,
                show dz + dx + dy = dx + dy + dz from by ring,
                LinearEquiv.coe_coe, Tensor.permute_pure, hfam]

/-- Cyclic leg permutation commutes with polynomial pure tensors, coefficient by coefficient:
permuting the legs of the polynomial pure path of `x` by the cycle `X ↦ Y ↦ Z ↦ X` gives the
polynomial pure path of the reindexed family `fun c ↦ x (cycle.symm c)`.

Proof sketch: both sides are additive in each of the three polynomial vectors, so a triple
`Finsupp.induction_linear` reduces to the case where every leg carries a single monomial.  There
the total degree `dx + dy + dz` is unchanged by rotation and `Tensor.permute_pure` rotates the
pure tensor of coefficients. -/
theorem polynomialPure_permute_cycle (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) cycle).toLinearMap
        (polynomialPure (K := K) x) =
      polynomialPure (K := K) (V := fun i ↦ V (cycle.symm i))
        (fun c ↦ x (cycle.symm c)) := by
  rw [← ofLegs_eta x]
  convert polynomialPure_permute_cycle_ofLegs (K := K) (V := V)
    (x .X) (x .Y) (x .Z) using 1
  congr 1
  funext c
  cases c <;> rfl

/-- Multiplying the `X` polynomial vector by `ε^n` shifts the total polynomial-pure path. -/
theorem polynomialPure_shift_X_ofLegs (n : ℕ)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs (PolynomialVector.shift n xX) xY xZ) =
      PolynomialVector.shift n (polynomialPure (K := K) (ofLegs xX xY xZ)) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [PolynomialVector.shift_add, polynomialPure_add_X, ha, hb]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [PolynomialVector.shift_add, polynomialPure_add_Y, ha, hb]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [PolynomialVector.shift_add, polynomialPure_add_Z, ha, hb]
          | single dz vz =>
              change polynomialPure (K := K) (ofLegs
                  (PolynomialVector.shift n (PolynomialVector.monomial dx vx))
                  (PolynomialVector.monomial dy vy)
                  (PolynomialVector.monomial dz vz)) =
                PolynomialVector.shift n
                  (polynomialPure (K := K) (ofLegs
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy)
                    (PolynomialVector.monomial dz vz)))
              simp only [PolynomialVector.shift_monomial, polynomialPure_monomial]
              rw [show n + dx + dy + dz = n + (dx + dy + dz) by omega]

/-- Coordinate-family form of `polynomialPure_shift_X_ofLegs`. -/
theorem polynomialPure_shift_X (n : ℕ) (x : ∀ c, PolynomialVector (V c)) :
    polynomialPure (K := K)
        (ofLegs (PolynomialVector.shift n (x .X)) (x .Y) (x .Z)) =
      PolynomialVector.shift n (polynomialPure (K := K) x) := by
  rw [← ofLegs_eta x]
  exact polynomialPure_shift_X_ofLegs n _ _ _

/-- `P` has first nonzero coefficient `T` in degree `d`.

No condition is imposed on coefficients above `d`; this is the exact algebraic version of
`P = ε^d T + O(ε^(d+1))`.
-/
def HasLeadingTerm {M : Type*} [Zero M]
    (P : PolynomialVector M) (d : ℕ) (x : M) : Prop :=
  P d = x ∧ ∀ e < d, P e = 0

namespace HasLeadingTerm

/-- The zero polynomial has zero as a leading coefficient in every prescribed degree. -/
@[simp] theorem zero {M : Type*} [Zero M] (d : ℕ) :
    HasLeadingTerm (0 : PolynomialVector M) d 0 := by
  constructor <;> simp

/-- The coefficient of `P` in its leading degree `d` is the leading coefficient `x`. -/
theorem coeff {M : Type*} [Zero M] {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) : P d = x := h.1

/-- Every coefficient of `P` in a degree strictly below the leading degree vanishes. -/
theorem lower_coeff {M : Type*} [Zero M] {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) {e : ℕ} (he : e < d) : P e = 0 := h.2 e he

/-- Leading terms in a common degree add: if `P` and `Q` both lead in degree `d` with
coefficients `x` and `y`, then `P + Q` leads in degree `d` with coefficient `x + y`. -/
theorem add {M : Type*} [AddZeroClass M]
    {P Q : PolynomialVector M} {d : ℕ} {x y : M}
    (hP : HasLeadingTerm P d x) (hQ : HasLeadingTerm Q d y) :
    HasLeadingTerm (P + Q) d (x + y) := by
  constructor
  · simp [hP.coeff, hQ.coeff]
  · intro e he
    simp [hP.lower_coeff he, hQ.lower_coeff he]

/-- Applying a linear map coefficientwise preserves a leading term and its degree. -/
theorem mapLinear
    {M N : Type*}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) (f : M →ₗ[K] N) :
    HasLeadingTerm (PolynomialVector.mapLinear f P) d (f x) := by
  constructor
  · simp [h.coeff]
  · intro e he
    simp [h.lower_coeff he]

/-- Multiplication by `ε^n` shifts a leading degree by `n`. -/
theorem shift {M : Type*} [AddCommMonoid M]
    {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) (n : ℕ) :
    HasLeadingTerm (PolynomialVector.shift n P) (n + d) x := by
  constructor
  · rw [PolynomialVector.shift_apply, if_pos (Nat.le_add_right n d),
      Nat.add_sub_cancel_left]
    exact h.coeff
  · intro k hk
    rw [PolynomialVector.shift_apply]
    by_cases hnk : n ≤ k
    · rw [if_pos hnk]
      exact h.lower_coeff (by omega)
    · rw [if_neg hnk]

/-- Every supported degree is at least the leading degree. -/
theorem degree_le_of_mem_support {M : Type*} [Zero M]
    {P : PolynomialVector M} {d : ℕ}
    {x : M} (h : HasLeadingTerm P d x) {e : ℕ}
    (he : e ∈ P.support) : d ≤ e := by
  by_contra hde
  have helow : e < d := Nat.lt_of_not_ge hde
  exact (Finsupp.mem_support_iff.mp he) (h.lower_coeff helow)

/-- The monomial `ε^d x` has leading coefficient `x` in degree `d`. -/
theorem monomial {M : Type*} [Zero M] (d : ℕ) (x : M) :
    HasLeadingTerm (PolynomialVector.monomial d x) d x := by
  refine ⟨by simp, ?_⟩
  intro e he
  simp [PolynomialVector.monomial, Nat.ne_of_lt he]

/-- Leading terms multiply under polynomial convolution through a bilinear map: if
`f = ε^d x + O(ε^(d+1))` and `g = ε^e y + O(ε^(e+1))`, then
`convolution B f g = ε^(d+e) (B x y) + O(ε^(d+e+1))`.

Proof sketch: by `convolution_coeff`, the coefficient of the convolution in degree `n` is the
sum of `B (f i) (g j)` over supported degrees `i` of `f` and `j` of `g` with `i + j = n`.
Every supported degree of `f` is at least `d` and every supported degree of `g` is at least
`e`, so for `n < d + e` no supported pair contributes at all, while for `n = d + e` the only
contributing pair is `i = d`, `j = e`, giving exactly `B x y`. -/
theorem convolution
    {M N P : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    {f : PolynomialVector M} {g : PolynomialVector N}
    {d e : ℕ} {x : M} {y : N}
    (hf : HasLeadingTerm f d x) (hg : HasLeadingTerm g e y)
    (B : M →ₗ[K] N →ₗ[K] P) :
    HasLeadingTerm (PolynomialVector.convolution B f g) (d + e) (B x y) := by
  classical
  constructor
  · rw [PolynomialVector.convolution_coeff]
    rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single e]
      · simp [hf.coeff, hg.coeff]
      · intro j hj hje
        by_cases hsum : d + j = d + e
        · exact (hje (Nat.add_left_cancel hsum)).elim
        · simp [hje]
      · intro heNotMem
        have hge : g e = 0 := by
          by_contra hne
          exact heNotMem (Finsupp.mem_support_iff.mpr hne)
        simp [hge]
    · intro i hi hid
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hsum : i + j = d + e
      · have hdi : d ≤ i := hf.degree_le_of_mem_support hi
        have hej : e ≤ j := hg.degree_le_of_mem_support hj
        have hie : i + e ≤ d + e := by
          calc
            i + e ≤ i + j := Nat.add_le_add_left hej i
            _ = d + e := hsum
        have hid' : i = d := Nat.le_antisymm (Nat.le_of_add_le_add_right hie) hdi
        exact (hid hid').elim
      · simp [hsum]
    · intro hdNotMem
      have hfd : f d = 0 := by
        by_contra hne
        exact hdNotMem (Finsupp.mem_support_iff.mpr hne)
      simp [hfd]
  · intro n hn
    rw [PolynomialVector.convolution_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hsum : i + j = n
    · have hdi : d ≤ i := hf.degree_le_of_mem_support hi
      have hej : e ≤ j := hg.degree_le_of_mem_support hj
      have hle : d + e ≤ n := by
        rw [← hsum]
        exact Nat.add_le_add hdi hej
      exact (Nat.not_le_of_lt hn hle).elim
    · simp [hsum]

/-- Leading terms are preserved when the parameter is replaced by `ε^N`. -/
theorem dilation {M : Type*} [AddCommMonoid M]
    {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) {N : ℕ} (hN : 0 < N) :
    HasLeadingTerm (PolynomialVector.dilation N P) (N * d) x := by
  constructor
  · exact PolynomialVector.dilation_coeff hN P d |>.trans h.coeff
  · intro n hn
    apply Finsupp.mapDomain_of_not_mem_image_support
    rintro ⟨i, hi, rfl⟩
    have hdi : d ≤ i := h.degree_le_of_mem_support hi
    exact (Nat.not_le_of_lt hn) (Nat.mul_le_mul_left N hdi)

/-- Parameter dilation creates a gap: below `N(d+1)`, only the new leading degree `Nd` can
survive. -/
theorem dilation_gap {M : Type*} [AddCommMonoid M]
    {P : PolynomialVector M} {d : ℕ} {x : M}
    (h : HasLeadingTerm P d x) {N n : ℕ}
    (hn : n < N * (d + 1)) (hne : n ≠ N * d) :
    PolynomialVector.dilation N P n = 0 := by
  apply Finsupp.mapDomain_of_not_mem_image_support
  rintro ⟨i, hi, rfl⟩
  have hdi : d ≤ i := h.degree_le_of_mem_support hi
  rcases hdi.eq_or_lt with rfl | hdi
  · exact hne rfl
  · have hsucc : d + 1 ≤ i := hdi
    exact (Nat.not_le_of_lt hn) (Nat.mul_le_mul_left N hsucc)

end HasLeadingTerm

/-- External products of polynomial tensor paths use Cauchy convolution of degrees. -/
noncomputable def polynomialExternal
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (P : PolynomialTensor K V) (Q : PolynomialTensor K W) :
    PolynomialTensor K (fun i ↦ TensorProduct K (V i) (W i)) :=
  PolynomialVector.convolution Tensor.external P Q

/-- The polynomial external product with the zero path on the left is zero. -/
@[simp] theorem polynomialExternal_zero_left
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (Q : PolynomialTensor K W) :
    polynomialExternal (0 : PolynomialTensor K V) Q = 0 := by
  exact PolynomialVector.convolution_zero_left _ _

/-- The polynomial external product with the zero path on the right is zero. -/
@[simp] theorem polynomialExternal_zero_right
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (P : PolynomialTensor K V) :
    polynomialExternal P (0 : PolynomialTensor K W) = 0 := by
  exact PolynomialVector.convolution_zero_right _ _

/-- The polynomial external product is additive in its left factor. -/
theorem polynomialExternal_add_left
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (P₁ P₂ : PolynomialTensor K V) (Q : PolynomialTensor K W) :
    polynomialExternal (P₁ + P₂) Q =
      polynomialExternal P₁ Q + polynomialExternal P₂ Q := by
  exact PolynomialVector.convolution_add_left _ _ _ _

/-- The polynomial external product is additive in its right factor. -/
theorem polynomialExternal_add_right
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (P : PolynomialTensor K V) (Q₁ Q₂ : PolynomialTensor K W) :
    polynomialExternal P (Q₁ + Q₂) =
      polynomialExternal P Q₁ + polynomialExternal P Q₂ := by
  exact PolynomialVector.convolution_add_right _ _ _ _

/-- The polynomial external product commutes with scalar multiplication of the left factor. -/
theorem polynomialExternal_smul_left
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (r : K) (P : PolynomialTensor K V) (Q : PolynomialTensor K W) :
    polynomialExternal (r • P) Q = r • polynomialExternal P Q := by
  exact PolynomialVector.convolution_smul_left _ _ _ _

/-- The polynomial external product commutes with scalar multiplication of the right factor. -/
theorem polynomialExternal_smul_right
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (r : K) (P : PolynomialTensor K V) (Q : PolynomialTensor K W) :
    polynomialExternal P (r • Q) = r • polynomialExternal P Q := by
  exact PolynomialVector.convolution_smul_right _ _ _ _

/-- The external product of two polynomial pure tensors is the polynomial pure tensor of the
legwise Cauchy products. -/
theorem polynomialExternal_polynomialPure_ofLegs
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) (yX : PolynomialVector (W .X))
    (yY : PolynomialVector (W .Y)) (yZ : PolynomialVector (W .Z)) :
    polynomialExternal
        (polynomialPure (K := K) (ofLegs xX xY xZ))
        (polynomialPure (K := K) (ofLegs yX yY yZ)) =
      polynomialPure (K := K) (ofLegs
        (PolynomialVector.convolution (TensorProduct.mk K (V .X) (W .X)) xX yX)
        (PolynomialVector.convolution (TensorProduct.mk K (V .Y) (W .Y)) xY yY)
        (PolynomialVector.convolution (TensorProduct.mk K (V .Z) (W .Z)) xZ yZ)) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [PolynomialVector.convolution_add_left, polynomialExternal_add_left,
        polynomialPure_add_X, ha, hb]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [PolynomialVector.convolution_add_left, polynomialExternal_add_left,
            polynomialPure_add_Y, ha, hb]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [PolynomialVector.convolution_add_left, polynomialExternal_add_left,
                polynomialPure_add_Z, ha, hb]
          | single dz vz =>
              induction yX using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb =>
                  simp [PolynomialVector.convolution_add_right, polynomialExternal_add_right,
                    polynomialPure_add_X, ha, hb]
              | single ex wx =>
                  induction yY using Finsupp.induction_linear with
                  | zero => simp
                  | add a b ha hb =>
                      simp [PolynomialVector.convolution_add_right,
                        polynomialExternal_add_right, polynomialPure_add_Y, ha, hb]
                  | single ey wy =>
                      induction yZ using Finsupp.induction_linear with
                      | zero => simp
                      | add a b ha hb =>
                          simp [PolynomialVector.convolution_add_right,
                            polynomialExternal_add_right, polynomialPure_add_Z, ha, hb]
                      | single ez wz =>
                          change polynomialExternal
                              (polynomialPure (K := K) (ofLegs
                                (PolynomialVector.monomial dx vx)
                                (PolynomialVector.monomial dy vy)
                                (PolynomialVector.monomial dz vz)))
                              (polynomialPure (K := K) (ofLegs
                                (PolynomialVector.monomial ex wx)
                                (PolynomialVector.monomial ey wy)
                                (PolynomialVector.monomial ez wz))) =
                            polynomialPure (K := K) (ofLegs
                              (PolynomialVector.convolution
                                (TensorProduct.mk K (V .X) (W .X))
                                (PolynomialVector.monomial dx vx)
                                (PolynomialVector.monomial ex wx))
                              (PolynomialVector.convolution
                                (TensorProduct.mk K (V .Y) (W .Y))
                                (PolynomialVector.monomial dy vy)
                                (PolynomialVector.monomial ey wy))
                              (PolynomialVector.convolution
                                (TensorProduct.mk K (V .Z) (W .Z))
                                (PolynomialVector.monomial dz vz)
                                (PolynomialVector.monomial ez wz)))
                          simp only [polynomialPure_monomial,
                            PolynomialVector.convolution_monomial, polynomialExternal]
                          rw [show dx + dy + dz + (ex + ey + ez) =
                              (dx + ex) + (dy + ey) + (dz + ez) by omega]
                          simp
                          congr 2
                          funext i
                          fin_cases i <;> rfl

/-- Coordinate-free form of `polynomialExternal_polynomialPure_ofLegs`. -/
theorem polynomialExternal_polynomialPure
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (x : ∀ c, PolynomialVector (V c))
    (y : ∀ c, PolynomialVector (W c)) :
    polynomialExternal (polynomialPure (K := K) x) (polynomialPure (K := K) y) =
      polynomialPure (K := K)
        (fun c ↦ PolynomialVector.convolution (TensorProduct.mk K (V c) (W c))
          (x c) (y c)) := by
  rw [← ofLegs_eta x, ← ofLegs_eta y]
  exact polynomialExternal_polynomialPure_ofLegs _ _ _ _ _ _

/-- Leading tensor terms multiply under the polynomial external product. -/
theorem HasLeadingTerm.external
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {P : PolynomialTensor K V} {Q : PolynomialTensor K W}
    {d e : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hP : HasLeadingTerm P d T) (hQ : HasLeadingTerm Q e S) :
    HasLeadingTerm (polynomialExternal P Q) (d + e) (Tensor.external T S) :=
  hP.convolution hQ Tensor.external

/-- A constructive border-rank upper bound.

The witness is a list of polynomial pure tensors whose sum has `T` as its leading coefficient.
This formulation is designed for exact, machine-checkable approximation algorithms.
-/
def BorderRankLE (r : ℕ) (T : Tensor3 K V) : Prop :=
  ∃ (d : ℕ) (terms : List (∀ c, PolynomialVector (V c))),
    terms.length ≤ r ∧
      HasLeadingTerm (terms.map (polynomialPure (K := K))).sum d T

/-- A constructive border-rank certificate with its leading degree retained in the type.

This refinement is useful for interpolation: tensor powers add the leading degrees, so coefficient
extraction incurs only polynomial—not exponential—overhead. -/
def BorderRankLEAt (r d : ℕ) (T : Tensor3 K V) : Prop :=
  ∃ terms : List (∀ c, PolynomialVector (V c)),
    terms.length ≤ r ∧
      HasLeadingTerm (terms.map (polynomialPure (K := K))).sum d T

namespace BorderRankLEAt

/-- Forgetting the leading degree turns a degree-aware certificate into a plain border-rank
bound: `BorderRankLEAt r d T` implies `BorderRankLE r T`. -/
theorem toBorderRankLE {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) : BorderRankLE r T := by
  rcases h with ⟨terms, hlen, hlead⟩
  exact ⟨d, terms, hlen, hlead⟩

/-- A degree-aware border-rank certificate for rank bound `r` also witnesses every larger bound
`s ≥ r`, with the same leading degree. -/
theorem mono {r s d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) (hrs : r ≤ s) : BorderRankLEAt s d T := by
  rcases h with ⟨terms, hlen, hlead⟩
  exact ⟨terms, hlen.trans hrs, hlead⟩

/-- A pure tensor is an exact degree-zero border-rank certificate. -/
theorem pure_tensor (x : ∀ c, V c) :
    BorderRankLEAt 1 0 (pure (K := K) x) := by
  refine ⟨[fun c ↦ PolynomialVector.constant (x c)], by simp, ?_⟩
  rw [← ofLegs_eta x]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show (fun c ↦ PolynomialVector.constant
      (ofLegs (x .X) (x .Y) (x .Z) c)) =
      ofLegs (PolynomialVector.constant (x .X))
        (PolynomialVector.constant (x .Y))
        (PolynomialVector.constant (x .Z)) by
    funext c
    cases c <;> rfl]
  rw [polynomialPure_constant]
  exact HasLeadingTerm.monomial 0
    (pure (K := K) (ofLegs (x .X) (x .Y) (x .Z)))

/-- Applying fixed linear maps preserves the certificate size and leading degree. -/
theorem map
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {r d : ℕ} {T : Tensor3 K V}
    (h : BorderRankLEAt r d T) (f : ∀ c, V c →ₗ[K] W c) :
    BorderRankLEAt r d (Tensor.map f T) := by
  rcases h with ⟨terms, hlen, hlead⟩
  let mapped : List (∀ c, PolynomialVector (W c)) :=
    terms.map fun x c ↦ PolynomialVector.mapLinear (f c) (x c)
  refine ⟨mapped, by simpa [mapped] using hlen, ?_⟩
  have hmapped := hlead.mapLinear (Tensor.map f)
  have hpath :
      PolynomialVector.mapLinear (Tensor.map f)
          (terms.map (polynomialPure (K := K))).sum =
        (mapped.map (polynomialPure (K := K))).sum := by
    rw [map_list_sum]
    simp [Function.comp_def, mapped, polynomialPure_mapLinear]
  rw [← hpath]
  exact hmapped

end BorderRankLEAt

namespace BorderRankLE

/-- Every constructive border-rank certificate has a definite leading degree. -/
theorem exists_at {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    ∃ d, BorderRankLEAt r d T := by
  rcases h with ⟨d, terms, hlen, hlead⟩
  exact ⟨d, terms, hlen, hlead⟩

/-- The zero tensor has border rank at most `0`, witnessed by the empty list of terms. -/
theorem zero : BorderRankLE 0 (0 : Tensor3 K V) := by
  refine ⟨0, [], by simp, ?_⟩
  exact ⟨rfl, fun e he ↦ (Nat.not_lt_zero e he).elim⟩

/-- Conversely, a tensor with border rank at most `0` is the zero tensor. -/
theorem eq_zero {T : Tensor3 K V} (h : BorderRankLE 0 T) : T = 0 := by
  rcases h with ⟨d, terms, hlen, hlead⟩
  cases terms with
  | nil =>
      have hcoeff := hlead.coeff
      simp at hcoeff
      exact hcoeff.symm
  | cons x terms => simp at hlen

/-- Package a verified polynomial list decomposition as a border-rank certificate. -/
theorem of_list_decomposition {T : Tensor3 K V} (d : ℕ)
    (terms : List (∀ c, PolynomialVector (V c)))
    (h : HasLeadingTerm (terms.map (polynomialPure (K := K))).sum d T) :
    BorderRankLE terms.length T := by
  exact ⟨d, terms, le_rfl, h⟩

/-- A constructive border-rank bound is monotone: border rank at most `r` implies border rank
at most every `s ≥ r`. -/
theorem mono {r s : ℕ} {T : Tensor3 K V}
    (h : BorderRankLE r T) (hrs : r ≤ s) : BorderRankLE s T := by
  rcases h with ⟨d, terms, hlen, hlead⟩
  exact ⟨d, terms, hlen.trans hrs, hlead⟩

/-- Shifting the `X`-leg polynomial of every term in a list shifts the sum of the polynomial
pure paths by the same amount. -/
private theorem sum_polynomialPure_shift_X
    (n : ℕ) (terms : List (∀ c, PolynomialVector (V c))) :
    ((terms.map fun x ↦
        ofLegs (PolynomialVector.shift n (x .X)) (x .Y) (x .Z)).map
          (polynomialPure (K := K))).sum =
      PolynomialVector.shift n (terms.map (polynomialPure (K := K))).sum := by
  induction terms with
  | nil => simp
  | cons x terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [polynomialPure_shift_X, ih, PolynomialVector.shift_add]

/-- Constructive border rank is subadditive: if `T` has border rank at most `r` and `S` has
border rank at most `s`, then the sum `T + S` has border rank at most `r + s`.

Proof sketch: the two certificates may lead in different degrees `d` and `e`.  Multiplying the
`X`-leg polynomial of every term of the first certificate by `ε^e`, and of the second by `ε^d`,
shifts each whole polynomial pure path by that amount, so both certificate sums acquire the
common leading degree `d + e` while keeping leading coefficients `T` and `S`.  Concatenating
the two shifted term lists gives at most `r + s` terms whose sum has leading coefficient
`T + S` in degree `d + e`. -/
theorem add {r s : ℕ} {T S : Tensor3 K V}
    (hT : BorderRankLE r T) (hS : BorderRankLE s S) :
    BorderRankLE (r + s) (T + S) := by
  rcases hT with ⟨d, left, hleft, hleadLeft⟩
  rcases hS with ⟨e, right, hright, hleadRight⟩
  let leftShifted : List (∀ c, PolynomialVector (V c)) := left.map fun x ↦
    ofLegs (PolynomialVector.shift e (x .X)) (x .Y) (x .Z)
  let rightShifted : List (∀ c, PolynomialVector (V c)) := right.map fun x ↦
    ofLegs (PolynomialVector.shift d (x .X)) (x .Y) (x .Z)
  let terms := leftShifted ++ rightShifted
  refine ⟨d + e, terms, ?_, ?_⟩
  · simpa [terms, leftShifted, rightShifted] using Nat.add_le_add hleft hright
  · have hLeft := hleadLeft.shift e
    rw [Nat.add_comm e d] at hLeft
    have hRight := hleadRight.shift d
    have hleading := hLeft.add hRight
    have hpath :
        (terms.map (polynomialPure (K := K))).sum =
          PolynomialVector.shift e (left.map (polynomialPure (K := K))).sum +
            PolynomialVector.shift d (right.map (polynomialPure (K := K))).sum := by
      simp only [terms, List.map_append, List.sum_append]
      rw [show leftShifted.map (polynomialPure (K := K)) =
          (left.map fun x ↦
            ofLegs (PolynomialVector.shift e (x .X)) (x .Y) (x .Z)).map
              (polynomialPure (K := K)) by rfl,
        show rightShifted.map (polynomialPure (K := K)) =
          (right.map fun x ↦
            ofLegs (PolynomialVector.shift d (x .X)) (x .Y) (x .Z)).map
              (polynomialPure (K := K)) by rfl,
        sum_polynomialPure_shift_X, sum_polynomialPure_shift_X]
    rw [hpath]
    exact hleading

/-- The external product of one polynomial pure path with a sum of pure paths distributes into
the sum of the legwise-convolved pure paths. -/
private theorem polynomialExternal_pure_sum
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (x : ∀ c, PolynomialVector (V c))
    (terms : List (∀ c, PolynomialVector (W c))) :
    polynomialExternal (polynomialPure (K := K) x)
        (terms.map (polynomialPure (K := K))).sum =
      (terms.map fun y ↦ polynomialPure (K := K) (fun c ↦
        PolynomialVector.convolution (TensorProduct.mk K (V c) (W c))
          (x c) (y c))).sum := by
  induction terms with
  | nil => simp
  | cons y terms ih =>
      simp only [List.map_cons, List.sum_cons, polynomialExternal_add_right,
        polynomialExternal_polynomialPure, ih]

/-- The external product of two sums of polynomial pure paths is the sum, over all pairs of
terms, of the legwise-convolved pure paths. -/
private theorem polynomialExternal_sums
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (left : List (∀ c, PolynomialVector (V c)))
    (right : List (∀ c, PolynomialVector (W c))) :
    polynomialExternal
        (left.map (polynomialPure (K := K))).sum
        (right.map (polynomialPure (K := K))).sum =
      ((left.flatMap fun x ↦ right.map fun y c ↦
        PolynomialVector.convolution (TensorProduct.mk K (V c) (W c))
          (x c) (y c)).map (polynomialPure (K := K))).sum := by
  induction left with
  | nil => simp
  | cons x left ih =>
      rw [List.map_cons, List.sum_cons, polynomialExternal_add_left,
        polynomialExternal_pure_sum, ih]
      simp [Function.comp_def]

end BorderRankLE

namespace BorderRankLEAt

/-- Degree-aware border-rank certificates multiply under external tensor products: from a
size-`r`, degree-`d` certificate for `T` and a size-`s`, degree-`e` certificate for `S`, the
external product `Tensor.external T S` gets a size-`r * s` certificate with leading degree
`d + e`.

Proof sketch: take all pairwise legwise Cauchy convolutions of a term of the first certificate
with a term of the second, giving at most `r * s` terms.  By bilinearity and the product law
for polynomial pure tensors, the sum of these paths equals the polynomial external product of
the two certificate sums; since leading terms multiply under convolution
(`HasLeadingTerm.external`), that product leads in degree `d + e` with coefficient
`Tensor.external T S`. -/
theorem external
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {r s d e : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : BorderRankLEAt r d T) (hS : BorderRankLEAt s e S) :
    BorderRankLEAt (r * s) (d + e) (Tensor.external T S) := by
  rcases hT with ⟨left, hleft, hleadLeft⟩
  rcases hS with ⟨right, hright, hleadRight⟩
  let pairs : List (∀ c, PolynomialVector (TensorProduct K (V c) (W c))) :=
    left.flatMap fun x ↦ right.map fun y c ↦
      PolynomialVector.convolution (TensorProduct.mk K (V c) (W c))
        (x c) (y c)
  refine ⟨pairs, ?_, ?_⟩
  · change pairs.length ≤ r * s
    calc
      pairs.length = left.length * right.length := by simp [pairs]
      _ ≤ r * s := Nat.mul_le_mul hleft hright
  · have hleading := hleadLeft.external hleadRight
    rw [BorderRankLE.polynomialExternal_sums] at hleading
    exact hleading

end BorderRankLEAt

namespace BorderRankLE

/-- Constructive border rank is submultiplicative under external tensor products: border rank
at most `r` for `T` and at most `s` for `S` give border rank at most `r * s` for
`Tensor.external T S`.

Proof sketch: as in `BorderRankLEAt.external`, all pairwise legwise convolutions of the terms
of the two certificates sum to the polynomial external product of the two certificate paths,
whose leading coefficient in degree `d + e` is `Tensor.external T S` because leading terms
multiply under convolution. -/
theorem external
    {W : Leg → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {r s : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : BorderRankLE r T) (hS : BorderRankLE s S) :
    BorderRankLE (r * s) (Tensor.external T S) := by
  rcases hT with ⟨d, left, hleft, hleadLeft⟩
  rcases hS with ⟨e, right, hright, hleadRight⟩
  let pairs : List (∀ c, PolynomialVector (TensorProduct K (V c) (W c))) :=
    left.flatMap fun x ↦ right.map fun y c ↦
      PolynomialVector.convolution (TensorProduct.mk K (V c) (W c))
        (x c) (y c)
  refine ⟨d + e, pairs, ?_, ?_⟩
  · change pairs.length ≤ r * s
    calc
      pairs.length = left.length * right.length := by simp [pairs]
      _ ≤ r * s := Nat.mul_le_mul hleft hright
  · have hleading := hleadLeft.external hleadRight
    rw [polynomialExternal_sums] at hleading
    exact hleading

end BorderRankLE

end AlgebraicComplexity.Tensor
