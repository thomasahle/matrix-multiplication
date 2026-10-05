/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum

/-!
# Polynomial degenerations of indexed direct sums

This file proves that finitely many independent polynomial tensor degenerations can be assembled
into one degeneration of their indexed direct sums.  The degree-aware theorem assumes a common
leading degree.  A second theorem synchronizes arbitrary positive component degrees by replacing
the parameter in component `i` by `ε^(D / dᵢ)`, where `D` is their finite product.

The construction is reusable in laser-method arguments where several independently supported
tensor groups must all survive one global degeneration.  It is deliberately independent of
Coppersmith--Winograd tensors and of any particular grouping convention.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Leg → Type v} {W : ι → Leg → Type x}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]
variable [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]

namespace PolynomialLinearMap

/-- Lift one polynomial map family between indexed summands to the ambient indexed direct-sum
spaces, killing every other source summand. -/
noncomputable def indexedComponent
    (i : ι) (c : Leg) (A : PolynomialLinearMap K (V i c) (W i c)) :
    PolynomialLinearMap K (IndexedDirectSumSpace K V c) (IndexedDirectSumSpace K W c) :=
  Finsupp.mapRange
    (fun f ↦ indexedInclude (K := K) (V := W) i c ∘ₗ f ∘ₗ
      DirectSum.component K ι (fun j ↦ V j c) i)
    (by simp) A

/-- Assemble polynomial map families independently on every indexed summand. -/
noncomputable def indexedMap
    (A : ∀ i c, PolynomialLinearMap K (V i c) (W i c)) : ∀ c,
    PolynomialLinearMap K (IndexedDirectSumSpace K V c) (IndexedDirectSumSpace K W c) :=
  fun c ↦ ∑ i, indexedComponent (K := K) i c (A i c)

/-- The assembled coefficient map acts on an included vector through exactly the corresponding
component coefficient map.

Proof sketch: expand the finite sum defining `indexedMap`.  Direct-sum projection after inclusion
is the identity at the selected index and zero at every other index. -/
theorem indexedMap_coeff_comp_indexedInclude
    (A : ∀ i c, PolynomialLinearMap K (V i c) (W i c))
    (i : ι) (c : Leg) (d : ℕ) :
    indexedMap (K := K) A c d ∘ₗ indexedInclude (K := K) (V := V) i c =
      indexedInclude (K := K) (V := W) i c ∘ₗ A i c d := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  unfold indexedMap
  rw [show (∑ j, indexedComponent (K := K) j c (A j c)) d =
      ∑ j, (indexedComponent (K := K) j c (A j c)) d by
        change Finsupp.applyAddHom d
          (∑ j, indexedComponent (K := K) j c (A j c)) = _
        rw [map_sum]
        rfl]
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [indexedComponent, indexedInclude]
  · intro j _ hji
    simp [indexedComponent, indexedInclude, DirectSum.component.of, Ne.symm hji]
  · simp

/-- Applying an assembled polynomial family to a vector included in summand `i` is the
coefficientwise inclusion of the componentwise polynomial result. -/
theorem applyVector_indexedMap_indexedInclude
    (A : ∀ i c, PolynomialLinearMap K (V i c) (W i c))
    (i : ι) (c : Leg) (x : V i c) :
    applyVector (indexedMap (K := K) A c)
        (indexedInclude (K := K) (V := V) i c x) =
      PolynomialVector.mapLinear (indexedInclude (K := K) (V := W) i c)
        (applyVector (A i c) x) := by
  apply Finsupp.ext
  intro d
  simp only [applyVector_coeff, PolynomialVector.mapLinear_apply]
  have h := LinearMap.congr_fun
    (indexedMap_coeff_comp_indexedInclude (K := K) A i c d) x
  exact h

end PolynomialLinearMap

/-- Polynomial transformation by assembled indexed maps commutes with embedding one tensor
summand.

Proof sketch: induct on the tensor-product universal property.  For a pure tensor, use the
componentwise `applyVector` identity on all three legs and functoriality of `polynomialPure`.
Additivity handles the induction step. -/
theorem polynomialTransform_indexedMap_indexedInclude
    (A : ∀ i c, PolynomialLinearMap K (V i c) (W i c))
    (i : ι) (T : Tensor3 K (V i)) :
    polynomialTransform (PolynomialLinearMap.indexedMap (K := K) A)
        (map (indexedInclude (K := K) (V := V) i) T) =
      PolynomialVector.mapLinear
        (map (indexedInclude (K := K) (V := W) i))
        (polynomialTransform (A i) T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    rw [map_smul, polynomialTransform_smul, polynomialTransform_smul,
      map_smul]
    congr 1
    rw [Tensor.map_pure, polynomialTransform_pure, polynomialTransform_pure,
      polynomialPure_mapLinear]
    congr 1
    funext c
    exact PolynomialLinearMap.applyVector_indexedMap_indexedInclude A i c (x c)
  · intro T₁ T₂ h₁ h₂
    rw [map_add, polynomialTransform_add, polynomialTransform_add,
      map_add, h₁, h₂]

/-- Transforming a finite indexed tensor direct sum by assembled polynomial maps is the sum of
the independently transformed and re-included component paths. -/
theorem polynomialTransform_indexedMap_indexedDirectSum
    (A : ∀ i c, PolynomialLinearMap K (V i c) (W i c))
    (T : ∀ i, Tensor3 K (V i)) :
    polynomialTransform (PolynomialLinearMap.indexedMap (K := K) A)
        (indexedDirectSum T) =
      ∑ i, PolynomialVector.mapLinear
        (map (indexedInclude (K := K) (V := W) i))
        (polynomialTransform (A i) (T i)) := by
  classical
  unfold indexedDirectSum
  rw [polynomialTransform_fintype_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact polynomialTransform_indexedMap_indexedInclude A i (T i)

namespace HasLeadingTerm

/-- A finite sum of polynomial paths with the same leading degree has as leading coefficient the
sum of their leading coefficients. -/
theorem fintype_sum
    {U : Type*} [AddCommMonoid U]
    {d : ℕ} {P : ι → PolynomialVector U} {x : ι → U}
    (h : ∀ i, HasLeadingTerm (P i) d (x i)) :
    HasLeadingTerm (∑ i, P i) d (∑ i, x i) := by
  classical
  constructor
  · change Finsupp.applyAddHom d (∑ i, P i) = ∑ i, x i
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _hi ↦ (h i).coeff
  · intro e he
    change Finsupp.applyAddHom e (∑ i, P i) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _hi ↦ (h i).lower_coeff he

end HasLeadingTerm

namespace PolynomialDegeneratesAt

/-- Component degenerations with one common displayed degree assemble into a degeneration of
their indexed direct sums at that same degree. -/
theorem indexedDirectSum
    {d : ℕ} {T : ∀ i, Tensor3 K (V i)} {S : ∀ i, Tensor3 K (W i)}
    (h : ∀ i, PolynomialDegeneratesAt d (T i) (S i)) :
    PolynomialDegeneratesAt d (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  choose A hA using h
  refine ⟨PolynomialLinearMap.indexedMap (K := K) A, ?_⟩
  rw [polynomialTransform_indexedMap_indexedDirectSum]
  have hsum := HasLeadingTerm.fintype_sum fun i ↦
    (hA i).mapLinear (map (indexedInclude (K := K) (V := W) i))
  change HasLeadingTerm _ d
    (∑ i, map (indexedInclude (K := K) (V := W) i) (S i))
  exact hsum

omit [Fintype ι] in
/-- Replacing the degeneration parameter by `ε^N` multiplies the displayed leading degree by
`N`, provided `N` is positive. -/
theorem dilate
    {d : ℕ} {T : Tensor3 K (V i)} {S : Tensor3 K (W i)}
    (h : PolynomialDegeneratesAt d T S) {N : ℕ} (hN : 0 < N) :
    PolynomialDegeneratesAt (N * d) T S := by
  rcases h with ⟨A, hA⟩
  refine ⟨fun c ↦ PolynomialLinearMap.dilate N (A c), ?_⟩
  rw [polynomialTransform_dilate]
  exact hA.dilation hN

end PolynomialDegeneratesAt

namespace PolynomialDegenerates

/-- Finitely many component degenerations with positive, possibly different displayed degrees
assemble into one degeneration of their indexed direct sums.

Proof sketch: let `D` be the product of all component degrees.  Every positive `dᵢ` divides
`D`, so dilating component `i` by the positive quotient `D / dᵢ` moves its leading coefficient
to degree `D`.  Apply the common-degree indexed-direct-sum theorem and then forget `D`. -/
theorem indexedDirectSum_of_pos_degrees
    {T : ∀ i, Tensor3 K (V i)} {S : ∀ i, Tensor3 K (W i)}
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (h : ∀ i, PolynomialDegeneratesAt (d i) (T i) (S i)) :
    PolynomialDegenerates (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  let D := ∏ i, d i
  have hD : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun i _hi ↦ hd i
  have hdiv : ∀ i, d i ∣ D := by
    intro i
    dsimp [D]
    simpa using Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  choose N hN using hdiv
  have hNpos : ∀ i, 0 < N i := by
    intro i
    by_contra hnot
    have hzero : N i = 0 := Nat.eq_zero_of_not_pos hnot
    have : D = 0 := by simpa [hzero] using hN i
    omega
  apply (PolynomialDegeneratesAt.indexedDirectSum (d := D) fun i ↦ ?_).toPolynomialDegenerates
  have hi := (h i).dilate (hNpos i)
  convert hi using 1
  rw [Nat.mul_comm]
  exact hN i

/-- Arbitrary finitely many component degenerations assemble into a degeneration of their
indexed direct sums.

The component certificates need not expose a common leading degree.  This theorem first replaces
each certificate by the positive-degree form supplied by `PolynomialDegenerates.exists_at_pos`,
then invokes `indexedDirectSum_of_pos_degrees` to synchronize those degrees.

Proof sketch: choose a positive displayed degree for every component degeneration and apply the
positive-degree assembly theorem. -/
theorem indexedDirectSum
    {T : ∀ i, Tensor3 K (V i)} {S : ∀ i, Tensor3 K (W i)}
    (h : ∀ i, PolynomialDegenerates (T i) (S i)) :
    PolynomialDegenerates (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  choose d hd hdeg using fun i ↦ (h i).exists_at_pos
  exact indexedDirectSum_of_pos_degrees d hd hdeg

end PolynomialDegenerates

end AlgebraicComplexity.Tensor
