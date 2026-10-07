/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Polynomial scalars acting on polynomial vectors

A border-rank certificate is a sum of *polynomial* pure tensors
`polynomialPure (a(ε), b(ε), c(ε))`.  Linear algebra on such a certificate — expanding a leg in a
basis, moving a coefficient from one leg to another, cancelling a kernel relation — is linear
algebra over the polynomial ring `K[X]`, not over `K`.  This file supplies exactly that much of
it: the action of `K[X]` on `PolynomialVector M`, and the statement that `polynomialPure` is
`K[X]`-trilinear.

The action is not rebuilt by hand.  `PolynomialVector M` is `ℕ →₀ M`, the coefficient
representation of Mathlib's `PolynomialModule K M`, so `polySMul` is transported from the
`K[X]`-module structure there and every module axiom is inherited.

## Main definitions and results

* `PolynomialVector.polySMul p x`: the polynomial `p` acting on the polynomial vector `x`, with
  its module laws (`polySMul_add`, `add_polySMul`, `mul_polySMul`, `one_polySMul`, and the finite
  sum forms);
* `PolynomialVector.polySMul_monomial`: `(c ε^i) • (ε^j x) = ε^(i+j) (c • x)`;
* `PolynomialVector.mapLinear_polySMul`: coefficientwise linear maps are `K[X]`-linear;
* `polynomialPure_polySMul_X`, `_Y`, `_Z`: a polynomial scalar on any one leg of a polynomial pure
  tensor pulls out, so it can be moved between legs;
* `polynomialPure_sum_polySMul_XY`: the bilinear expansion
  `(∑ᵢ pᵢ xᵢ) ⊗ (∑ₖ rₖ yₖ) ⊗ z = ∑ᵢ ∑ₖ (pᵢ rₖ) (xᵢ ⊗ yₖ ⊗ z)`;
* `PolynomialVector.toPolynomial` and `PolynomialVector.sum_polySMul_basis`: a polynomial vector
  is the `K[X]`-combination of the constant basis vectors with its coordinate polynomials as
  coefficients;
* `hasLeadingTerm_polySMul_constant`: `q • (constant x)` leads with `x` in degree `d` as soon as
  `q = ε^d + O(ε^(d+1))`.

## Scope

Only what the border-rank one-slice speedup (`Tensor/OneSliceBorderSpeedup.lean`) consumes is
developed.  In particular no tensor product over `K[X]` is introduced: `polynomialPure` remains
the library's convolution, and the lemmas here say that it behaves `K[X]`-trilinearly.
-/

namespace AlgebraicComplexity.Tensor

open scoped Polynomial

open Module

universe u v w

namespace PolynomialVector

variable {K : Type u} [CommRing K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable {N : Type w} [AddCommGroup N] [Module K N]

/-- The polynomial `p ∈ K[X]` acting on a polynomial vector: Cauchy multiplication of the
coefficient sequences.  Transported from the `K[X]`-module structure of `PolynomialModule K M`,
whose coefficient representation `ℕ →₀ M` is `PolynomialVector M`. -/
noncomputable def polySMul (p : K[X]) (x : PolynomialVector M) : PolynomialVector M :=
  (p • PolynomialModule.ofCoeff K x).coeff

/-- A polynomial scalar annihilates the zero polynomial vector. -/
@[simp] theorem polySMul_zero (p : K[X]) : polySMul p (0 : PolynomialVector M) = 0 := by
  simp [polySMul]

/-- The zero polynomial annihilates every polynomial vector. -/
@[simp] theorem zero_polySMul (x : PolynomialVector M) : polySMul (0 : K[X]) x = 0 := by
  simp [polySMul]

/-- The polynomial action is additive in the vector. -/
theorem polySMul_add (p : K[X]) (x y : PolynomialVector M) :
    polySMul p (x + y) = polySMul p x + polySMul p y := by
  simp [polySMul, smul_add]

/-- The polynomial action is additive in the scalar. -/
theorem add_polySMul (p q : K[X]) (x : PolynomialVector M) :
    polySMul (p + q) x = polySMul p x + polySMul q x := by
  simp [polySMul, add_smul]

/-- The polynomial action is compatible with multiplication of polynomials. -/
theorem mul_polySMul (p q : K[X]) (x : PolynomialVector M) :
    polySMul (p * q) x = polySMul p (polySMul q x) := by
  simp only [polySMul, PolynomialModule.ofCoeff_coeff, mul_smul]

/-- The constant polynomial `1` acts as the identity. -/
@[simp] theorem one_polySMul (x : PolynomialVector M) : polySMul (1 : K[X]) x = x := by
  simp [polySMul]

/-- The polynomial action commutes with finite sums of vectors. -/
theorem polySMul_finset_sum {ι : Type*} (p : K[X]) (s : Finset ι)
    (x : ι → PolynomialVector M) :
    polySMul p (∑ i ∈ s, x i) = ∑ i ∈ s, polySMul p (x i) :=
  map_sum (AddMonoidHom.mk' (polySMul p) (polySMul_add p)) x s

/-- The polynomial action commutes with finite sums of scalars. -/
theorem finset_sum_polySMul {ι : Type*} (s : Finset ι) (p : ι → K[X])
    (x : PolynomialVector M) :
    polySMul (∑ i ∈ s, p i) x = ∑ i ∈ s, polySMul (p i) x :=
  map_sum (AddMonoidHom.mk' (fun q : K[X] ↦ polySMul q x) fun q q' ↦ add_polySMul q q' x) p s

/-- On monomials the action is the expected one: `(c ε^i) • (ε^j x) = ε^(i+j) (c • x)`. -/
theorem polySMul_monomial (i : ℕ) (c : K) (j : ℕ) (x : M) :
    polySMul (Polynomial.monomial i c) (PolynomialVector.monomial j x) =
      PolynomialVector.monomial (i + j) (c • x) := by
  simp only [polySMul, PolynomialVector.monomial, PolynomialModule.ofCoeff_single,
    PolynomialModule.monomial_smul_single, PolynomialModule.coeff_single]

/-- Coefficients of a polynomial multiple of a constant vector: the degree-`e` coefficient of
`q • (constant x)` is `q.coeff e • x`. -/
theorem polySMul_constant_apply (q : K[X]) (x : M) (e : ℕ) :
    polySMul q (constant x) e = q.coeff e • x := by
  simp [polySMul, constant, PolynomialVector.monomial]

/-- Applying a linear map coefficientwise sends a constant vector to a constant vector. -/
@[simp] theorem mapLinear_constant (f : M →ₗ[K] N) (x : M) :
    mapLinear (K := K) f (constant x) = constant (f x) := by
  simp [constant]

/-- A constant polynomial vector is additive over finite sums of its coefficient. -/
theorem constant_finset_sum {ι : Type*} (s : Finset ι) (x : ι → M) :
    constant (∑ i ∈ s, x i) = ∑ i ∈ s, constant (x i) := by
  simp only [constant, PolynomialVector.monomial]
  exact Finsupp.single_finsetSum s x 0

/-- Coefficientwise linear maps are linear over polynomial scalars. -/
theorem mapLinear_polySMul (f : M →ₗ[K] N) (p : K[X]) (x : PolynomialVector M) :
    mapLinear (K := K) f (polySMul p x) = polySMul p (mapLinear (K := K) f x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_polySMul, add_polySMul, map_add, hp, hq]
  | monomial i c =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => rw [polySMul_add, map_add, map_add, polySMul_add, ha, hb]
      | single j x =>
          change mapLinear (K := K) f
              (polySMul (Polynomial.monomial i c) (PolynomialVector.monomial j x)) =
            polySMul (Polynomial.monomial i c)
              (mapLinear (K := K) f (PolynomialVector.monomial j x))
          rw [polySMul_monomial, mapLinear_monomial, mapLinear_monomial, polySMul_monomial,
            map_smul]

/-- The polynomial with the given coefficient sequence. -/
noncomputable def toPolynomial (s : PolynomialVector K) : K[X] :=
  s.sum fun e c ↦ Polynomial.monomial e c

/-- The zero coefficient sequence gives the zero polynomial. -/
@[simp] theorem toPolynomial_zero : toPolynomial (0 : PolynomialVector K) = 0 := by
  simp [toPolynomial]

/-- `toPolynomial` is additive. -/
theorem toPolynomial_add (s t : PolynomialVector K) :
    toPolynomial (s + t) = toPolynomial s + toPolynomial t := by
  simp [toPolynomial, Finsupp.sum_add_index']

/-- `toPolynomial` sends a monomial coefficient sequence to the corresponding monomial. -/
@[simp] theorem toPolynomial_monomial (e : ℕ) (c : K) :
    toPolynomial (PolynomialVector.monomial e c) = Polynomial.monomial e c := by
  simp [toPolynomial, PolynomialVector.monomial]

/-- **Basis expansion over `K[X]`.**  A polynomial vector is the combination of the constant
basis vectors whose coefficients are its coordinate polynomials. -/
theorem sum_polySMul_basis {ι : Type*} [Fintype ι] (b : Basis ι K M)
    (x : PolynomialVector M) :
    ∑ j, polySMul (toPolynomial (mapLinear (K := K) (b.coord j) x)) (constant (b j)) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, toPolynomial_add, add_polySMul, Finset.sum_add_distrib, hx, hy]
  | single d m =>
      change ∑ j, polySMul (toPolynomial
          (mapLinear (K := K) (b.coord j) (PolynomialVector.monomial d m))) (constant (b j)) =
        PolynomialVector.monomial d m
      simp only [mapLinear_monomial, toPolynomial_monomial, constant, polySMul_monomial,
        add_zero, Basis.coord_apply]
      simp only [PolynomialVector.monomial]
      rw [← Finsupp.single_finsetSum, b.sum_repr]

/-- The basis expansion of `sum_polySMul_basis`, pushed through a linear map: the image of a
polynomial vector is the same `K[X]`-combination of the images of the basis vectors. -/
theorem sum_polySMul_basis_mapLinear {ι : Type*} [Fintype ι] (b : Basis ι K M)
    (f : M →ₗ[K] N) (x : PolynomialVector M) :
    ∑ j, polySMul (toPolynomial (mapLinear (K := K) (b.coord j) x)) (constant (f (b j))) =
      mapLinear (K := K) f x := by
  have h := congrArg (mapLinear (K := K) f) (sum_polySMul_basis b x)
  rw [map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mapLinear_polySMul, mapLinear_constant]

end PolynomialVector

open PolynomialVector

section LeadingTerm

variable {K : Type u} [CommRing K] {M : Type v} [AddCommGroup M] [Module K M]

/-- If `q = ε^d + O(ε^(d+1))`, then `q • (constant x)` has leading coefficient `x` in degree
`d`. -/
theorem hasLeadingTerm_polySMul_constant {q : K[X]} {d : ℕ} (hq : q.coeff d = 1)
    (hlow : ∀ e < d, q.coeff e = 0) (x : M) :
    HasLeadingTerm (polySMul q (constant x)) d x := by
  refine ⟨?_, fun e he ↦ ?_⟩
  · rw [polySMul_constant_apply, hq, one_smul]
  · rw [polySMul_constant_apply, hlow e he, zero_smul]

/-- Leading terms in a common degree add over a finite sum. -/
theorem HasLeadingTerm.finset_sum {ι : Type*} {A : Type*} [AddCommMonoid A] (s : Finset ι)
    {P : ι → PolynomialVector A} {d : ℕ} {x : ι → A}
    (h : ∀ i ∈ s, HasLeadingTerm (P i) d (x i)) :
    HasLeadingTerm (∑ i ∈ s, P i) d (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end LeadingTerm

section PolynomialPure

variable {K : Type u} [CommRing K]
variable {V : Leg → Type v} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]

/-- The convolutional pure tensor commutes with finite sums in its `X` polynomial vector. -/
theorem polynomialPure_finset_sum_X {ι : Type*} (s : Finset ι)
    (x : ι → PolynomialVector (V .X)) (y : PolynomialVector (V .Y))
    (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs (∑ i ∈ s, x i) y z) =
      ∑ i ∈ s, polynomialPure (K := K) (ofLegs (x i) y z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polynomialPure_add_X, ih]

/-- The convolutional pure tensor commutes with finite sums in its `Y` polynomial vector. -/
theorem polynomialPure_finset_sum_Y {ι : Type*} (s : Finset ι)
    (x : PolynomialVector (V .X)) (y : ι → PolynomialVector (V .Y))
    (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x (∑ i ∈ s, y i) z) =
      ∑ i ∈ s, polynomialPure (K := K) (ofLegs x (y i) z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polynomialPure_add_Y, ih]

/-- A polynomial scalar on the `X` leg of a polynomial pure tensor pulls out. -/
theorem polynomialPure_polySMul_X (p : K[X]) (x : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs (polySMul p x) y z) =
      polySMul p (polynomialPure (K := K) (ofLegs x y z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_polySMul, polynomialPure_add_X, hp, hq, add_polySMul]
  | monomial i c =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          rw [polySMul_add, polynomialPure_add_X, ha, hb, polynomialPure_add_X, polySMul_add]
      | single dx vx =>
          induction y using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              rw [polynomialPure_add_Y, ha, hb, polynomialPure_add_Y, polySMul_add]
          | single dy vy =>
              induction z using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb =>
                  rw [polynomialPure_add_Z, ha, hb, polynomialPure_add_Z, polySMul_add]
              | single dz vz =>
                  change polynomialPure (K := K) (ofLegs
                      (polySMul (Polynomial.monomial i c) (PolynomialVector.monomial dx vx))
                      (PolynomialVector.monomial dy vy) (PolynomialVector.monomial dz vz)) =
                    polySMul (Polynomial.monomial i c) (polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)
                      (PolynomialVector.monomial dz vz)))
                  rw [polySMul_monomial, polynomialPure_monomial, polynomialPure_monomial,
                    polySMul_monomial, pure_ofLegs_smul_X]
                  congr 1
                  omega

/-- A polynomial scalar on the `Y` leg of a polynomial pure tensor pulls out. -/
theorem polynomialPure_polySMul_Y (p : K[X]) (x : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x (polySMul p y) z) =
      polySMul p (polynomialPure (K := K) (ofLegs x y z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_polySMul, polynomialPure_add_Y, hp, hq, add_polySMul]
  | monomial i c =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          rw [polynomialPure_add_X, ha, hb, polynomialPure_add_X, polySMul_add]
      | single dx vx =>
          induction y using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              rw [polySMul_add, polynomialPure_add_Y, ha, hb, polynomialPure_add_Y,
                polySMul_add]
          | single dy vy =>
              induction z using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb =>
                  rw [polynomialPure_add_Z, ha, hb, polynomialPure_add_Z, polySMul_add]
              | single dz vz =>
                  change polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx)
                      (polySMul (Polynomial.monomial i c) (PolynomialVector.monomial dy vy))
                      (PolynomialVector.monomial dz vz)) =
                    polySMul (Polynomial.monomial i c) (polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)
                      (PolynomialVector.monomial dz vz)))
                  rw [polySMul_monomial, polynomialPure_monomial, polynomialPure_monomial,
                    polySMul_monomial, pure_ofLegs_smul_Y]
                  congr 1
                  omega

/-- A polynomial scalar on the `Z` leg of a polynomial pure tensor pulls out. -/
theorem polynomialPure_polySMul_Z (p : K[X]) (x : PolynomialVector (V .X))
    (y : PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K) (ofLegs x y (polySMul p z)) =
      polySMul p (polynomialPure (K := K) (ofLegs x y z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_polySMul, polynomialPure_add_Z, hp, hq, add_polySMul]
  | monomial i c =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          rw [polynomialPure_add_X, ha, hb, polynomialPure_add_X, polySMul_add]
      | single dx vx =>
          induction y using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              rw [polynomialPure_add_Y, ha, hb, polynomialPure_add_Y, polySMul_add]
          | single dy vy =>
              induction z using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb =>
                  rw [polySMul_add, polynomialPure_add_Z, ha, hb, polynomialPure_add_Z,
                    polySMul_add]
              | single dz vz =>
                  change polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)
                      (polySMul (Polynomial.monomial i c) (PolynomialVector.monomial dz vz))) =
                    polySMul (Polynomial.monomial i c) (polynomialPure (K := K) (ofLegs
                      (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)
                      (PolynomialVector.monomial dz vz)))
                  rw [polySMul_monomial, polynomialPure_monomial, polynomialPure_monomial,
                    polySMul_monomial, pure_ofLegs_smul_Z]
                  congr 1
                  omega

/-- **Bilinear expansion over `K[X]`.**  Polynomial combinations on the `X` and `Y` legs of a
polynomial pure tensor expand into the double sum whose coefficients are the products. -/
theorem polynomialPure_sum_polySMul_XY {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → K[X]) (x : ι → PolynomialVector (V .X))
    (r : κ → K[X]) (y : κ → PolynomialVector (V .Y)) (z : PolynomialVector (V .Z)) :
    polynomialPure (K := K)
        (ofLegs (∑ i ∈ s, polySMul (p i) (x i)) (∑ k ∈ t, polySMul (r k) (y k)) z) =
      ∑ i ∈ s, ∑ k ∈ t,
        polySMul (p i * r k) (polynomialPure (K := K) (ofLegs (x i) (y k) z)) := by
  rw [polynomialPure_finset_sum_X]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [polynomialPure_finset_sum_Y]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [polynomialPure_polySMul_X, polynomialPure_polySMul_Y, mul_polySMul]

end PolynomialPure

end AlgebraicComplexity.Tensor
