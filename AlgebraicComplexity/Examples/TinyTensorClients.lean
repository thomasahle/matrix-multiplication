/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.SliceRank
import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.MatrixMultiplication

/-!
# Tiny regression clients for the core tensor API

This file contains deliberately small clients of the public core API, as required by the trust
policy in `DESIGN.md`: every major semantic operation should have a tiny test whose answer can be
checked by hand.  Each example states in its doc comment which kind of API misuse it would catch.

The objects are one- and two-dimensional: the scalar tensor `1 ⊗ 1 ⊗ 1`, the two-term diagonal
tensor `e₀⊗e₀⊗e₀ + e₁⊗e₁⊗e₁` in `K × K` legs, the three-term `W` tensor, and the
matrix-multiplication tensor `⟨1,1,1⟩`.  The results proved here are:

- zeroing one term of the two-term diagonal tensor by an exact restriction (`Restricts`,
  source first, result second);
- external products of rank-one tensors are rank-one (`RankLE 1`), including a left-associated
  triple product;
- the indexed direct sum of `n` scalar tensors has rank at most `n` and folds, by an exact
  restriction, onto the `n`-fold scalar sum;
- an explicit degree-one polynomial degeneration certificate
  (`PolynomialDegeneratesAt 1`) from the diagonal tensor to the `W` tensor, with the border-rank
  consequence `BorderRankLE 2 W`;
- invariance of the `W` tensor under the cyclic leg rotation (`permute cycle`);
- `⟨1,1,1⟩` is a single pure tensor, has `RankLE 1`, and is `Isomorphic` to the scalar tensor;
- the two-term diagonal tensor on `K × K` legs is `Isomorphic` to the library's
  `Tensor.diagonalTensor K (Fin 2)` on `Fin 2 → K` legs, which upgrades its rank certificate to the
  exact value `rank (diagonalTwo F) = 2` over a field.  The two leg models are kept distinct on
  purpose: the isomorphism is the test, and collapsing them would remove it.

This is a layer-4 regression client: it imports only the reusable tensor layer and the base
matrix-multiplication module, and it must never be imported by them.
-/

namespace AlgebraicComplexity.Examples.TinyTensor

open AlgebraicComplexity Tensor
open Tensor.PolynomialVector

universe u

/-- The one-dimensional ambient space `K` on every tensor leg. -/
abbrev ScalarSpace (K : Type u) (_ : Leg) : Type u := K

/-- The two-dimensional ambient space `K × K` on every tensor leg. -/
abbrev PairSpace (K : Type u) (_ : Leg) : Type u := K × K

section Semiring

variable (K : Type u) [CommSemiring K]

/-- The scalar tensor `1 ⊗ 1 ⊗ 1` in one-dimensional legs. -/
noncomputable def scalarOne : Tensor3 K (ScalarSpace K) :=
  pure (K := K) (ofLegs (1 : K) 1 1)

/-- First standard vector `e₀ = (1, 0)` of `K × K`. -/
def e0 : K × K := (1, 0)

/-- Second standard vector `e₁ = (0, 1)` of `K × K`. -/
def e1 : K × K := (0, 1)

/-- The two-term diagonal tensor `e₀⊗e₀⊗e₀ + e₁⊗e₁⊗e₁` in two-dimensional legs. -/
noncomputable def diagonalTwo : Tensor3 K (PairSpace K) :=
  pure (K := K) (ofLegs (e0 K) (e0 K) (e0 K)) +
    pure (K := K) (ofLegs (e1 K) (e1 K) (e1 K))

/-- Projection of `K × K` onto its first coordinate, on every leg. -/
def firstCoordinateMap : ∀ c, PairSpace K c →ₗ[K] ScalarSpace K c :=
  ofLegs (V := fun c ↦ PairSpace K c →ₗ[K] ScalarSpace K c)
    (LinearMap.fst K K K) (LinearMap.fst K K K) (LinearMap.fst K K K)

/-- Zeroing one term of a two-term tensor: projecting every leg of
`e₀⊗e₀⊗e₀ + e₁⊗e₁⊗e₁` onto its first coordinate kills the second summand and carries the
first onto the scalar tensor `1 ⊗ 1 ⊗ 1`.

This is the smallest test of the `Restricts` relation.  It would catch a reversed relation
direction (`Restricts T S` means the maps carry the *source* `T` to the *result* `S`) and a
leg map that fails to annihilate a pure tensor with one zero leg. -/
theorem diagonalTwo_restricts_scalarOne :
    Restricts (diagonalTwo K) (scalarOne K) := by
  refine ⟨firstCoordinateMap K, ?_⟩
  unfold diagonalTwo scalarOne
  rw [LinearMap.map_add, Tensor.map_pure, Tensor.map_pure]
  have h0 : (fun i ↦ firstCoordinateMap K i
        (ofLegs (V := PairSpace K) (e0 K) (e0 K) (e0 K) i)) =
      ofLegs (V := ScalarSpace K) (1 : K) 1 1 := by
    funext c
    cases c <;> simp [firstCoordinateMap, e0]
  have h1 : (fun i ↦ firstCoordinateMap K i
        (ofLegs (V := PairSpace K) (e1 K) (e1 K) (e1 K) i)) =
      ofLegs (V := ScalarSpace K) (0 : K) 0 0 := by
    funext c
    cases c <;> simp [firstCoordinateMap, e1]
  rw [h0, h1]
  simp

/-- The scalar tensor is pure, hence has rank at most one. -/
theorem scalarOne_rankLE : RankLE 1 (scalarOne K) := by
  unfold scalarOne
  exact RankLE.pure_tensor _

/-- The two-term diagonal tensor has rank at most two.  A one-line test of additivity of
constructive rank certificates. -/
theorem diagonalTwo_rankLE_two : RankLE 2 (diagonalTwo K) := by
  unfold diagonalTwo
  simpa using (RankLE.pure_tensor _).add (RankLE.pure_tensor _)

/-- Identification of the hand-written leg model `K × K` with the coordinate space `Fin 2 → K` used
by the library's `Tensor.diagonalTensor`. -/
noncomputable def pairLegEquiv : ∀ c, PairSpace K c ≃ₗ[K] (Fin 2 → K) :=
  fun _ ↦ (LinearEquiv.piFinTwo K fun _ : Fin 2 ↦ K).symm

/-- **The hand-written `⟨2⟩` is the library's `⟨2⟩`.**  `diagonalTwo` is deliberately built on a
different leg model (`K × K` rather than `Fin 2 → K`) so that it tests the API without reusing its
definitions; this isomorphism ties it back to `Tensor.diagonalTensor`, turning the file's local
computations into a regression test *of* the library rather than a parallel development.

Proof sketch: `pairLegEquiv` sends `(1, 0)` and `(0, 1)` to the two standard basis vectors, so it
matches the two defining pure terms one by one. -/
theorem diagonalTwo_isomorphic_diagonalTensor :
    Isomorphic (diagonalTwo K) (diagonalTensor K (Fin 2)) := by
  classical
  refine ⟨pairLegEquiv K, ?_⟩
  unfold diagonalTwo diagonalTensor
  rw [map_add, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod, Fin.sum_univ_two]
  have h0 : (fun i ↦ pairLegEquiv K i (ofLegs (V := PairSpace K) (e0 K) (e0 K) (e0 K) i)) =
      (fun _ : Leg ↦ (Pi.single (0 : Fin 2) (1 : K))) := by
    funext c
    cases c <;> · ext j; fin_cases j <;> simp [pairLegEquiv, e0]
  have h1 : (fun i ↦ pairLegEquiv K i (ofLegs (V := PairSpace K) (e1 K) (e1 K) (e1 K) i)) =
      (fun _ : Leg ↦ (Pi.single (1 : Fin 2) (1 : K))) := by
    funext c
    cases c <;> · ext j; fin_cases j <;> simp [pairLegEquiv, e1]
  rw [h0, h1]

section RankOne

variable {V W : Leg → Type*}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- A product of two rank-one tensors is rank-one: if `RankLE 1 T` and `RankLE 1 S` then
`RankLE 1 (T ⊗ S)` under the factorwise external product.

This exercises submultiplicativity of the rank calculus at its smallest instance `1 * 1 = 1`
and would catch a wrong certificate-size formula in `RankLE.external`. -/
theorem rankLE_one_external {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE 1 T) (hS : RankLE 1 S) :
    RankLE 1 (Tensor.external T S) := by
  simpa using hT.external hS

end RankOne

/-- The left-associated triple external product of scalar tensors is rank-one.

Iterated external products change the ambient leg spaces through tensor-product associators;
this tiny instance would catch a rank calculus that fails on nested products. -/
theorem external3_scalarOne_rankLE_one :
    RankLE 1 (Tensor.external (Tensor.external (scalarOne K) (scalarOne K)) (scalarOne K)) :=
  rankLE_one_external K
    (rankLE_one_external K (scalarOne_rankLE K) (scalarOne_rankLE K))
    (scalarOne_rankLE K)

/-- Summing one-dimensional tensors, rank form: the indexed direct sum of `n` copies of the
scalar tensor has rank at most `n = ∑ 1`.

This checks that rank certificates add over `indexedDirectSum` and would catch a size formula
that multiplied instead of added. -/
theorem indexedDirectSum_scalarOne_rankLE (n : ℕ) :
    RankLE n (Tensor.indexedDirectSum (fun _ : Fin n ↦ scalarOne K)) := by
  simpa using
    RankLE.indexedDirectSum (r := fun _ : Fin n ↦ 1) (fun _ ↦ scalarOne_rankLE K)

/-- Summing one-dimensional tensors, restriction form: folding the indexed direct sum of `n`
copies of the scalar tensor into the common one-dimensional space gives its `n`-fold sum,
i.e. `(n : K) • (1 ⊗ 1 ⊗ 1)`.

The direction matters: the direct sum is the source and the folded sum is the result.  This
would catch a reversed fold or an inclusion/projection mix-up in the indexed direct-sum API. -/
theorem indexedDirectSum_scalarOne_restricts_sum (n : ℕ) :
    Restricts (Tensor.indexedDirectSum (fun _ : Fin n ↦ scalarOne K))
      ((n : K) • scalarOne K) := by
  simpa [Nat.cast_smul_eq_nsmul] using
    Restricts.indexedDirectSum_to_sum
      (T := fun _ : Fin n ↦ scalarOne K) (S := fun _ ↦ scalarOne K)
      (fun _ ↦ Restricts.refl _)

/-- `⟨1,1,1⟩` is the single pure tensor `x₀₀ ⊗ y₀₀ ⊗ z₀₀`. -/
theorem matrixMultiplication_one_eq_pure :
    matrixMultiplication (K := K) 1 1 1 =
      pure (K := K) (mmTermOfTriple (K := K) 1 1 1 (0, 0, 0)) := by
  unfold matrixMultiplication
  simp [Fintype.sum_prod_type]

/-- `⟨1,1,1⟩` has rank at most one: multiplying two `1 × 1` matrices is one scalar product.

The smallest matrix-multiplication regression; it would catch an index-convention error making
the defining triple sum range over more than one term. -/
theorem matrixMultiplication_one_rankLE_one :
    RankLE 1 (matrixMultiplication (K := K) 1 1 1) := by
  rw [matrixMultiplication_one_eq_pure]
  exact RankLE.pure_tensor _

/-- The `1 × 1` matrix index set has exactly one element.  Mathlib has no `Unique` instance for
binary products, so this tiny client provides the closed instance it needs; `Unique` is a
subsingleton class, so no diamond can arise.

It is deliberately `local`: this is a regression client, and a `Unique (Fin 1 × Fin 1)`
instance for one specific product of `Fin`s has no business entering the global instance set of
every downstream module.  Only `mmOneLegEquiv` and the isomorphism below need it. -/
local instance instUniqueFinOneProd : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, by decide⟩

/-- Legwise linear equivalences collapsing the `1 × 1` coordinate spaces of `⟨1,1,1⟩` to `K`. -/
def mmOneLegEquiv : ∀ c, MMSpace K 1 1 1 c ≃ₗ[K] ScalarSpace K c
  | .X => LinearEquiv.funUnique (Fin 1 × Fin 1) K K
  | .Y => LinearEquiv.funUnique (Fin 1 × Fin 1) K K
  | .Z => LinearEquiv.funUnique (Fin 1 × Fin 1) K K

/-- `⟨1,1,1⟩` is isomorphic (by invertible maps on all three legs) to the scalar tensor
`1 ⊗ 1 ⊗ 1`.

This exercises the strongest relation in the hierarchy, `Isomorphic`, on the smallest matrix
multiplication tensor and would catch a mismatch between the coordinate representation of
`⟨1,1,1⟩` and its abstract one-dimensional content. -/
theorem matrixMultiplication_one_isomorphic_scalarOne :
    Isomorphic (matrixMultiplication (K := K) 1 1 1) (scalarOne K) := by
  refine ⟨mmOneLegEquiv K, ?_⟩
  rw [matrixMultiplication_one_eq_pure, PiTensorProduct.congr_tprod]
  unfold scalarOne
  have hdefault : (default : Fin 1 × Fin 1) = (0, 0) := rfl
  congr 1
  funext c
  cases c <;> simp [mmOneLegEquiv, mmTerm, hdefault]

end Semiring

section Field

variable (F : Type u) [Field F]

/-- **The rank of the two-term diagonal tensor is exactly two.**  The upper bound is the
constructive certificate `diagonalTwo_rankLE_two`; the matching lower bound is Tao's slice-rank
argument, transported along `diagonalTwo_isomorphic_diagonalTensor`.  This is the sharpest form of
the file's smallest regression test: it would catch a rank API that silently under-counts. -/
theorem rank_diagonalTwo : rank (diagonalTwo F) = 2 := by
  rw [rank_isomorphic (diagonalTwo_isomorphic_diagonalTensor F), rank_diagonalTensor]
  simp

end Field

section Ring

variable (K : Type u) [CommRing K]

/-- The three-term `W` tensor `e₁⊗e₀⊗e₀ + e₀⊗e₁⊗e₀ + e₀⊗e₀⊗e₁`. -/
noncomputable def wTensor : Tensor3 K (PairSpace K) :=
  pure (K := K) (ofLegs (e1 K) (e0 K) (e0 K)) +
    pure (K := K) (ofLegs (e0 K) (e1 K) (e0 K)) +
    pure (K := K) (ofLegs (e0 K) (e0 K) (e1 K))

/-- The `W` tensor is invariant under the cyclic rotation of its three legs.

`permute` reindexes through `e.symm`; this tiny check would catch using `e` in place of
`e.symm` (which would rotate the legs the opposite way and still typecheck on a symmetric
ambient family, but move each pure term to the wrong slot). -/
theorem permute_cycle_wTensor :
    Tensor.permute cycle (wTensor K) = wTensor K := by
  unfold wTensor
  rw [map_add, map_add, permute_pure, permute_pure, permute_pure]
  have h1 : (fun i ↦ ofLegs (V := PairSpace K) (e1 K) (e0 K) (e0 K) (cycle.symm i)) =
      ofLegs (V := PairSpace K) (e0 K) (e1 K) (e0 K) := by
    funext c; cases c <;> rfl
  have h2 : (fun i ↦ ofLegs (V := PairSpace K) (e0 K) (e1 K) (e0 K) (cycle.symm i)) =
      ofLegs (V := PairSpace K) (e0 K) (e0 K) (e1 K) := by
    funext c; cases c <;> rfl
  have h3 : (fun i ↦ ofLegs (V := PairSpace K) (e0 K) (e0 K) (e1 K) (cycle.symm i)) =
      ofLegs (V := PairSpace K) (e1 K) (e0 K) (e0 K) := by
    funext c; cases c <;> rfl
  rw [h1, h2, h3]
  abel

/-- Degree-zero `X`-leg coefficient of the `W` degeneration: `e₀ ↦ e₀`, `e₁ ↦ -e₀`. -/
def wMapX0 : (K × K) →ₗ[K] K × K :=
  LinearMap.inl K K K ∘ₗ (LinearMap.fst K K K - LinearMap.snd K K K)

/-- Degree-zero `Y`/`Z`-leg coefficient of the `W` degeneration: `e₀ ↦ e₀`, `e₁ ↦ e₀`. -/
def wMapYZ0 : (K × K) →ₗ[K] K × K :=
  LinearMap.inl K K K ∘ₗ (LinearMap.fst K K K + LinearMap.snd K K K)

/-- Degree-one coefficient of the `W` degeneration on every leg: `e₀ ↦ e₁`, `e₁ ↦ 0`. -/
def wMap1 : (K × K) →ₗ[K] K × K :=
  LinearMap.inr K K K ∘ₗ LinearMap.fst K K K

/-- The polynomial map families of the classical `W` degeneration.  On the `X` leg the family is
`ε ↦ wMapX0 + ε wMap1`, sending `e₀ ↦ e₀ + ε e₁` and `e₁ ↦ -e₀`; on the `Y` and `Z` legs it is
`ε ↦ wMapYZ0 + ε wMap1`, sending `e₀ ↦ e₀ + ε e₁` and `e₁ ↦ e₀`. -/
noncomputable def wCurve : ∀ c, PolynomialLinearMap K (PairSpace K c) (PairSpace K c) :=
  ofLegs (V := fun c ↦ PolynomialLinearMap K (PairSpace K c) (PairSpace K c))
    (constant (wMapX0 K) + monomial 1 (wMap1 K))
    (constant (wMapYZ0 K) + monomial 1 (wMap1 K))
    (constant (wMapYZ0 K) + monomial 1 (wMap1 K))

/-- Applying the `W` curve maps to the diagonal tensor gives the explicit polynomial path
`(e₀ + εe₁)⊗(e₀ + εe₁)⊗(e₀ + εe₁) + (-e₀)⊗e₀⊗e₀`. -/
theorem wCurve_transform_eq :
    polynomialTransform (wCurve K) (diagonalTwo K) =
      polynomialPure (K := K) (ofLegs
        (constant (e0 K) + monomial 1 (e1 K))
        (constant (e0 K) + monomial 1 (e1 K))
        (constant (e0 K) + monomial 1 (e1 K))) +
      polynomialPure (K := K) (ofLegs
        (constant (-e0 K)) (constant (e0 K)) (constant (e0 K))) := by
  unfold diagonalTwo
  rw [polynomialTransform_add, polynomialTransform_pure, polynomialTransform_pure]
  congr 1
  · congr 1
    funext c
    cases c <;>
      simp [wCurve, wMapX0, wMapYZ0, wMap1, e0, e1, constant,
        PolynomialLinearMap.applyVector_add]
  · congr 1
    funext c
    cases c <;>
      simp [wCurve, wMapX0, wMapYZ0, wMap1, e0, e1, constant,
        PolynomialLinearMap.applyVector_add, Prod.mk_zero_zero]

/-- The `W` path has zero constant coefficient: the two `e₀⊗e₀⊗e₀` contributions cancel. -/
theorem wCurve_transform_coeff_zero :
    polynomialTransform (wCurve K) (diagonalTwo K) 0 = 0 := by
  rw [wCurve_transform_eq]
  simp [constant]

/-- The degree-one coefficient of the `W` path is exactly the `W` tensor. -/
theorem wCurve_transform_coeff_one :
    polynomialTransform (wCurve K) (diagonalTwo K) 1 = wTensor K := by
  rw [wCurve_transform_eq]
  simp [wTensor, constant]

/-- Degree-one polynomial degeneration certificate: the rank-two diagonal tensor degenerates to
the `W` tensor with leading degree exactly one,
`(e₀+εe₁)^{⊗3} - e₀^{⊗3} = ε · W + O(ε²)`.

This is the smallest genuinely approximate degeneration.  It would catch a wrong leading-degree
convention in `HasLeadingTerm` (the certificate is *not* exact in degree zero — the degree-zero
coefficients must cancel), a sign error in the polynomial calculus, and a reversed
`PolynomialDegeneratesAt` direction (the diagonal tensor is the source, `W` the result). -/
theorem diagonalTwo_polynomialDegeneratesAt_one_wTensor :
    PolynomialDegeneratesAt 1 (diagonalTwo K) (wTensor K) := by
  refine ⟨wCurve K, ?_, ?_⟩
  · exact wCurve_transform_coeff_one K
  · intro e he
    obtain rfl : e = 0 := Nat.lt_one_iff.mp he
    exact wCurve_transform_coeff_zero K

/-- Border-rank consequence of the tiny degeneration: `W` has border rank at most two, although
its exact rank is classically three.  This composes a rank certificate with a degree-aware
degeneration through the public API. -/
theorem wTensor_borderRankLE_two : BorderRankLE 2 (wTensor K) :=
  ((diagonalTwo_rankLE_two K).borderAt_of_polynomialDegeneratesAt
    (diagonalTwo_polynomialDegeneratesAt_one_wTensor K)).toBorderRankLE

end Ring

end AlgebraicComplexity.Examples.TinyTensor
