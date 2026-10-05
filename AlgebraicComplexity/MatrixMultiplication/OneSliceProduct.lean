/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.ProductCore

/-!
# Lightweight external products of one-slice matrix tensors

The general rectangular external-product equivalence uses the full finite-coordinate basis
layer.  Zero/easy CW constituents need only the special case
`⟨1,d,1⟩ ⊠ ⟨1,e,1⟩ → ⟨1,de,1⟩`.  This module constructs that map directly from the universal
property of `TensorProduct`, proves it on pure matrix terms, and avoids importing the general
coordinate-equivalence development.

The map is intentionally exposed.  On the `Z` leg it is independent of `d` and `e`, which is the
coherence needed to assemble a whole shared-leg C-tensor fiber.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

namespace OneSliceProduct

/-- Pair two matrix-leg coordinates and encode the paired finite indices. -/
def indexProductEquiv (d e : ℕ) : ∀ c,
    MMIndex 1 d 1 c × MMIndex 1 e 1 c ≃ MMIndex 1 (d * e) 1 c
  | .X => (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  | .Y => (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  | .Z => (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)

/-- Pointwise multiplication as a bilinear map on two finite coordinate spaces. -/
private def coordinateMulBilinear {I J L : Type*} (equiv : I × J ≃ L) :
    (I → K) →ₗ[K] (J → K) →ₗ[K] (L → K) where
  toFun f :=
    { toFun := fun g k ↦ f (equiv.symm k).1 * g (equiv.symm k).2
      map_add' := by
        intro g h
        ext k
        simp [mul_add]
      map_smul' := by
        intro a g
        ext k
        simp [smul_eq_mul, mul_left_comm] }
  map_add' := by
    intro f g
    ext h k
    simp [add_mul]
  map_smul' := by
    intro a f
    ext g k
    simp [smul_eq_mul, mul_left_comm, mul_comm]

/-- Multiply two coordinate vectors after pairing their coordinate indices. -/
def coordinateProductMap {I J L : Type*} (equiv : I × J ≃ L) :
    TensorProduct K (I → K) (J → K) →ₗ[K] (L → K) :=
  TensorProduct.lift (coordinateMulBilinear (K := K) equiv)

@[simp] theorem coordinateProductMap_tmul_apply
    {I J L : Type*} (equiv : I × J ≃ L)
    (f : I → K) (g : J → K) (k : L) :
    coordinateProductMap (K := K) equiv (f ⊗ₜ[K] g) k =
      f (equiv.symm k).1 * g (equiv.symm k).2 := by
  rfl

/-- Pair coordinates after first applying two arbitrary source-leg maps.  Defining this directly
through `TensorProduct.lift` avoids importing the general binary tensor-product map calculus. -/
def coordinateProductMapAfter
    {I J L : Type*} {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (equiv : I × J ≃ L) (left : M →ₗ[K] (I → K)) (right : N →ₗ[K] (J → K)) :
    TensorProduct K M N →ₗ[K] (L → K) :=
  TensorProduct.lift
    { toFun := fun x ↦ (coordinateMulBilinear (K := K) equiv (left x)).comp right
      map_add' := by
        intro x y
        ext z k
        simp
      map_smul' := by
        intro a x
        ext z k
        simp [smul_eq_mul] }

@[simp] theorem coordinateProductMapAfter_tmul_apply
    {I J L : Type*} {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (equiv : I × J ≃ L) (left : M →ₗ[K] (I → K)) (right : N →ₗ[K] (J → K))
    (x : M) (y : N) (k : L) :
    coordinateProductMapAfter equiv left right (x ⊗ₜ[K] y) k =
      left x (equiv.symm k).1 * right y (equiv.symm k).2 := by
  rfl

/-- Paired standard basis vectors map to the corresponding paired standard basis vector. -/
@[simp] theorem coordinateProductMap_single
    {I J L : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (equiv : I × J ≃ L) (i : I) (j : J) :
    coordinateProductMap (K := K) equiv
        (Pi.single i 1 ⊗ₜ[K] Pi.single j 1) =
      Pi.single (equiv (i, j)) 1 := by
  ext k
  by_cases h : equiv.symm k = (i, j)
  · have hk : k = equiv (i, j) := by
      simpa using congrArg equiv h
    subst k
    simp
  · have hk : k ≠ equiv (i, j) := by
      intro hk
      apply h
      simp [hk]
    by_cases hi : (equiv.symm k).1 = i
    · have hj : (equiv.symm k).2 ≠ j := by
        intro hj
        exact h (Prod.ext hi hj)
      simp [hi, hj, hk]
    · simp [Pi.single_apply, hi, hk]

/-- The explicit leg map for the product of two one-slice matrix tensors. -/
def legMap (d e : ℕ) : ∀ c,
    TensorProduct K (MMSpace K 1 d 1 c) (MMSpace K 1 e 1 c) →ₗ[K]
      MMSpace K 1 (d * e) 1 c :=
  fun c ↦ coordinateProductMap (K := K) (indexProductEquiv d e c)

/-- Explicit one-slice product maps after arbitrary maps into the two input matrix spaces. -/
def legMapAfter
    {V : Leg → Type v} {W : Leg → Type w}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (d e : ℕ)
    (left : ∀ c, V c →ₗ[K] MMSpace K 1 d 1 c)
    (right : ∀ c, W c →ₗ[K] MMSpace K 1 e 1 c) : ∀ c,
    TensorProduct K (V c) (W c) →ₗ[K] MMSpace K 1 (d * e) 1 c :=
  fun c ↦ coordinateProductMapAfter (indexProductEquiv d e c) (left c) (right c)

/-- Mapping an external product with `legMapAfter` is the same as first mapping both factors and
then applying the canonical one-slice product map. -/
theorem map_external_after
    {V : Leg → Type v} {W : Leg → Type w}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (d e : ℕ)
    (left : ∀ c, V c →ₗ[K] MMSpace K 1 d 1 c)
    (right : ∀ c, W c →ₗ[K] MMSpace K 1 e 1 c)
    (T : Tensor3 K V) (S : Tensor3 K W) :
    Tensor.map (legMapAfter d e left right) (Tensor.external T S) =
      Tensor.map (legMap (K := K) d e)
        (Tensor.external (Tensor.map left T) (Tensor.map right S)) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      simp [legMapAfter, legMap, coordinateProductMapAfter,
        coordinateProductMap, coordinateMulBilinear]
    · intro S₁ S₂ h₁ h₂
      simp only [LinearMap.map_add, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]

/-- The `Z`-leg product map is definitionally independent of both middle dimensions. -/
theorem legMap_Z_eq (d e : ℕ) : legMap (K := K) d e .Z = legMap (K := K) 1 1 .Z :=
  rfl

/-- The explicit product map sends a pair of defining one-slice terms to the defining term with
paired middle index. -/
@[simp] theorem map_external_mmTerm
    (d e : ℕ) (j : Fin d) (j' : Fin e) :
    Tensor.map (legMap (K := K) d e)
        (Tensor.external
          (pure (K := K) (mmTerm (K := K) 1 d 1 0 j 0))
          (pure (K := K) (mmTerm (K := K) 1 e 1 0 j' 0))) =
      pure (K := K)
        (mmTerm (K := K) 1 (d * e) 1 0 (finProdFinEquiv (j, j')) 0) := by
  rw [external_pure, Tensor.map_pure]
  congr 1
  funext c
  have hzero : finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)) = 0 := rfl
  cases c <;>
    simp [legMap, indexProductEquiv, mmTerm, hzero]

/-- One-slice form of the defining matrix-multiplication sum. -/
theorem matrixMultiplication_eq_sum (d : ℕ) :
    matrixMultiplication (K := K) 1 d 1 =
      ∑ j : Fin d, pure (K := K) (mmTerm (K := K) 1 d 1 0 j 0) := by
  unfold matrixMultiplication
  simp [Fintype.sum_prod_type]

/-- Exact lightweight product law for one-slice matrix-multiplication tensors. -/
theorem map_external_matrixMultiplication (d e : ℕ) :
    Tensor.map (legMap (K := K) d e)
        (Tensor.external
          (matrixMultiplication (K := K) 1 d 1)
          (matrixMultiplication (K := K) 1 e 1)) =
      matrixMultiplication (K := K) 1 (d * e) 1 := by
  rw [matrixMultiplication_eq_sum, matrixMultiplication_eq_sum,
    matrixMultiplication_eq_sum, external_sum_sum]
  simp_rw [map_sum, map_external_mmTerm]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp finProdFinEquiv
    (fun j : Fin (d * e) ↦
      pure (K := K) (mmTerm (K := K) 1 (d * e) 1 0 j 0))

end OneSliceProduct

end AlgebraicComplexity
