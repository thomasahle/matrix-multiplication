/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.SliceRank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Subspace form of slice rank, and monotonicity under polynomial degeneration

This file proves thesis Proposition 5.1, quoting [TaoSawin2016, Corollary 2]: over a field, slice
rank is monotone under one-parameter polynomial degeneration.  The certificate-level half of the
argument lives in `Tensor/SliceRankDegeneration.lean`; what is added here is the valuative
("saturation") step that it was missing.

## The subspace layer

The subspace layer this file consumes is **not** defined here: it is part of the general slice-rank
API of `Tensor/SliceRank.lean`.  Recalled for orientation:

* `sliceSubmodule c D`: the span of the pure tensors whose leg-`c` component lies in `D`, that is
  `D ⊗ Y ⊗ Z` and its rotations.
* `SliceSumWith c e T`: `T` splits into one slice term per member of a finite family `e` of
  prescribed leg-`c` vectors, whence `sliceRankAlongLE_of_mem_sliceSubmodule`.
* `sliceRankLE_iff_exists_sliceSubmodules`: `S (T) ≤ r` if and only if `T` lies in
  `A ⊗ Y ⊗ Z + X ⊗ B ⊗ Z + X ⊗ Y ⊗ C` for leg subspaces of total dimension at most `r`.

Only `sliceRankAlongLE_of_mem_sliceSubmodule_list`, the list form used by the saturation argument,
is still stated here.

## The saturation layer

Working over a field `K`, a polynomial vector is an element of the `K[λ]`-module `M[λ]`, encoded
here as `PolynomialVector M = ℕ →₀ M`.  The `K[λ]`-module structure is not installed as an
instance; the two pieces of it that the argument needs are provided directly:

* `PolynomialVector.scalarSmul g v`, the cyclic action `g · v` of a scalar polynomial, together
  with `PolynomialVector.convolution_scalarSmul` (scalar polynomials multiply);
* `PolynomialLinearMap.applyPolynomial`, already in `Tensor/Degeneration.lean`, which is the action
  of a polynomial matrix, with `applyPolynomial_comp` and `applyPolynomial_constant_id` making
  `PolynomialLinearMap K M M` act as `K[λ]`-endomorphisms.

`exists_polynomialLinearMap_fixing_one` is the valuative heart in its cyclic case: for every
polynomial vector `w` there is a polynomial family `s` fixing `w` whose degree-zero coefficient has
rank at most one.  This is exactly saturation of the `K[λ]`-line `K[λ] w`: factoring `w = f · z`
where `f` generates the ideal spanned by the coordinates of `w`, Bézout in the principal ideal ring
`K[λ]` provides a `K[λ]`-linear functional `φ` with `φ z = 1`, and `s = z ∘ φ` projects onto the
saturated line `K[λ] z`.  Iterating over a list
(`exists_polynomialLinearMap_fixing_list`) saturates a finitely generated `K[λ]`-submodule: the
degree-zero coefficient of the resulting family has rank at most the number of generators, which is
the statement that reduction modulo `λ` of a saturated submodule preserves its rank.

## Proposition 5.1

`sliceRank_le_of_hasLeadingTerm_polynomialTransform` assembles the two layers.  A slice
decomposition of `T` transports to a decomposition of the path `polynomialTransform A T` into
polynomial slice terms whose leg-`c` polynomial slice vectors form a finite list `us c` with
`∑ c, |us c| ≤ S (T)` (`exists_polySlice_lists`).  Saturating each list gives families `q c` fixing
every `us c` and of small degree-zero rank; the complementary families `p c = 1 - q c` annihilate
every transported slice term, hence the whole path.  Taking degree-`d` coefficients, where `d` is
the leading degree, turns a legwise polynomial family into its degree-zero coefficient acting on
the leading tensor `S` (`polynomialTransformPath_coeff_of_vanishing`); expanding `1 = q + p` legwise
and telescoping then writes `S` as a sum of three tensors, the `c`-th of which lies in
`sliceSubmodule c (range (q c 0))`.  The subspace layer converts this into a slice certificate of
length at most `S (T)`.

The hypotheses that are genuinely forced: `K` must be a field (Bézout, existence of a complement
for a finite-dimensional subspace, and finite bases), and the *target* leg spaces must be additive
groups because the argument subtracts.  Neither the source nor the target leg spaces need to be
finite-dimensional: the finite-dimensional subspaces that appear are always spans of the finitely
many coefficients actually present in the given certificate.

## References

* J. Alman, *Limits on the Universal Method for Matrix Multiplication*, Ph.D. thesis, MIT, 2019,
  Proposition 5.1.
* T. Tao and W. Sawin, *Notes on the "slice rank" of tensors*, blog post, 2016, Corollary 2.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-! ## Scalar polynomials acting on polynomial vectors -/

section ScalarSmul

open PolynomialVector

variable {K : Type u} [CommSemiring K]

/-- The polynomial vector `g · v`, for a scalar polynomial `g : K[X]` and a fixed vector `v`.

This is the image of `v` under the `K[X]`-module structure of `PolynomialVector M`; the whole
saturation argument below only ever needs this cyclic part of that structure, so it is introduced
directly rather than through a module instance. -/
noncomputable def PolynomialVector.scalarSmul {M : Type*} [AddCommMonoid M] [Module K M]
    (g : Polynomial K) (v : M) : PolynomialVector M :=
  Finsupp.onFinset g.support (fun n ↦ g.coeff n • v) fun n hn ↦ by
    rw [Polynomial.mem_support_iff]
    intro h
    exact hn (by rw [h, zero_smul])

variable {M N P : Type*} [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
  [AddCommMonoid P] [Module K P]

/-- The coefficients of `g · v` are the coefficients of `g` scaling `v`. -/
@[simp] theorem PolynomialVector.scalarSmul_coeff (g : Polynomial K) (v : M) (n : ℕ) :
    scalarSmul g v n = g.coeff n • v := rfl

/-- The zero scalar polynomial acts as zero. -/
@[simp] theorem PolynomialVector.scalarSmul_zero_left (v : M) :
    scalarSmul (0 : Polynomial K) v = 0 := by
  ext n; simp

/-- Every scalar polynomial sends the zero vector to the zero polynomial vector. -/
@[simp] theorem PolynomialVector.scalarSmul_zero_right (g : Polynomial K) :
    scalarSmul g (0 : M) = 0 := by
  ext n; simp

/-- The action is additive in the scalar polynomial. -/
theorem PolynomialVector.scalarSmul_add_left (g h : Polynomial K) (v : M) :
    scalarSmul (g + h) v = scalarSmul g v + scalarSmul h v := by
  ext n; simp [add_smul]

/-- The action of a scalar monomial is a vector monomial. -/
theorem PolynomialVector.scalarSmul_monomial (i : ℕ) (a : K) (v : M) :
    scalarSmul (Polynomial.monomial i a) v = PolynomialVector.monomial i (a • v) := by
  ext n
  rw [scalarSmul_coeff, Polynomial.coeff_monomial, PolynomialVector.monomial,
    Finsupp.single_apply]
  by_cases h : i = n <;> simp [h]

/-- **Scalar polynomials multiply under convolution.**  Convolving `g · x` with `h · y` through a
bilinear map `B` produces `(g * h) · B x y`: this is the statement that the convolution product of
polynomial vectors is `K[X]`-bilinear, in the only form needed below.

Proof sketch: both sides are additive in `g` and in `h`, so `Polynomial.induction_on'` twice
reduces to scalar monomials, where both sides are the vector monomial in the added degree with
coefficient the product of the two scalars acting on `B x y`. -/
theorem PolynomialVector.convolution_scalarSmul (B : M →ₗ[K] N →ₗ[K] P)
    (g h : Polynomial K) (x : M) (y : N) :
    convolution B (scalarSmul g x) (scalarSmul h y) = scalarSmul (g * h) (B x y) := by
  induction g using Polynomial.induction_on' with
  | add g₁ g₂ hg₁ hg₂ =>
      rw [scalarSmul_add_left, convolution_add_left, hg₁, hg₂, add_mul, scalarSmul_add_left]
  | monomial i a =>
      induction h using Polynomial.induction_on' with
      | add h₁ h₂ hh₁ hh₂ =>
          rw [scalarSmul_add_left, convolution_add_right, hh₁, hh₂, mul_add,
            scalarSmul_add_left]
      | monomial j b =>
          rw [scalarSmul_monomial, scalarSmul_monomial, convolution_monomial,
            Polynomial.monomial_mul_monomial, scalarSmul_monomial]
          congr 1
          simp only [map_smul, LinearMap.smul_apply, smul_smul]
          rw [mul_comm]

end ScalarSmul

/-! ## Coefficients of convolutions in degree zero -/

section CoeffZero

open PolynomialVector

variable {K : Type u} [CommSemiring K]

/-- The degree-zero coefficient of a convolution is the bilinear map applied to the two
degree-zero coefficients: the only splitting `0 = i + j` is `i = j = 0`. -/
theorem PolynomialVector.convolution_coeff_zero
    {M N P : Type*} [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [AddCommMonoid P] [Module K P] (B : M →ₗ[K] N →ₗ[K] P)
    (f : PolynomialVector M) (g : PolynomialVector N) :
    convolution B f g 0 = B (f 0) (g 0) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [convolution_add_left, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply, map_add,
        LinearMap.add_apply]
  | single i x =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ =>
          rw [convolution_add_right, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply, map_add]
      | single j y =>
          show convolution B (PolynomialVector.monomial i x)
              (PolynomialVector.monomial j y) 0 = _
          rw [convolution_monomial]
          by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
            simp [PolynomialVector.monomial, hi, hj]

end CoeffZero

/-! ## Calculus of polynomial families of linear maps -/

section PolynomialFamily

open PolynomialVector PolynomialLinearMap

variable {K : Type u} [CommSemiring K]
variable {M N P : Type*} [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
  [AddCommMonoid P] [Module K P]

/-- Convolution distributes over finite sums in its left argument. -/
theorem PolynomialVector.convolution_finset_sum_left {ι : Type*} (B : M →ₗ[K] N →ₗ[K] P)
    (s : Finset ι) (f : ι → PolynomialVector M) (g : PolynomialVector N) :
    convolution B (∑ i ∈ s, f i) g = ∑ i ∈ s, convolution B (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, convolution_add_left, ih, Finset.sum_insert hi]

/-- Convolution distributes over finite sums in its right argument. -/
theorem PolynomialVector.convolution_finset_sum_right {ι : Type*} (B : M →ₗ[K] N →ₗ[K] P)
    (f : PolynomialVector M) (s : Finset ι) (g : ι → PolynomialVector N) :
    convolution B f (∑ i ∈ s, g i) = ∑ i ∈ s, convolution B f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, convolution_add_right, ih, Finset.sum_insert hi]

/-- The action of a scalar polynomial on a vector is additive over finite sums of scalars. -/
theorem PolynomialVector.scalarSmul_finset_sum_left {ι : Type*} (s : Finset ι)
    (g : ι → Polynomial K) (v : M) :
    scalarSmul (∑ i ∈ s, g i) v = ∑ i ∈ s, scalarSmul (g i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, scalarSmul_add_left, ih, Finset.sum_insert hi]

/-- The degree-zero coefficient of a Cauchy composition is the composition of the degree-zero
coefficients. -/
theorem PolynomialLinearMap.comp_coeff_zero (B : PolynomialLinearMap K N P)
    (A : PolynomialLinearMap K M N) : comp B A 0 = (B 0).comp (A 0) :=
  PolynomialVector.convolution_coeff_zero _ B A

/-- Polynomial application distributes over finite sums of map families. -/
theorem PolynomialLinearMap.applyPolynomial_finset_sum_left {ι : Type*} (s : Finset ι)
    (A : ι → PolynomialLinearMap K M N) (Q : PolynomialVector M) :
    applyPolynomial (∑ i ∈ s, A i) Q = ∑ i ∈ s, applyPolynomial (A i) Q :=
  PolynomialVector.convolution_finset_sum_left _ s A Q

/-- Polynomial application distributes over finite sums of polynomial vectors. -/
theorem PolynomialLinearMap.applyPolynomial_finset_sum_right (A : PolynomialLinearMap K M N)
    {ι : Type*} (s : Finset ι) (Q : ι → PolynomialVector M) :
    applyPolynomial A (∑ i ∈ s, Q i) = ∑ i ∈ s, applyPolynomial A (Q i) :=
  PolynomialVector.convolution_finset_sum_right _ A s Q

/-- Applying a scalar-polynomial multiple of a fixed linear map to a scalar-polynomial multiple of
a fixed vector multiplies the scalar polynomials. -/
theorem PolynomialLinearMap.applyPolynomial_scalarSmul (g h : Polynomial K) (F : M →ₗ[K] N)
    (v : M) :
    applyPolynomial (scalarSmul g F) (scalarSmul h v) = scalarSmul (g * h) (F v) := by
  rw [applyPolynomial, PolynomialVector.convolution_scalarSmul]
  rfl

/-- The constant identity family acts as the identity on polynomial vectors. -/
theorem PolynomialLinearMap.applyPolynomial_constant_id (Q : PolynomialVector M) :
    applyPolynomial (constant (LinearMap.id : M →ₗ[K] M)) Q = Q := by
  classical
  induction Q using Finsupp.induction_linear with
  | zero => simp
  | add Q₁ Q₂ h₁ h₂ => rw [applyPolynomial_add_right, h₁, h₂]
  | single k a =>
      show applyPolynomial (PolynomialVector.monomial 0 (LinearMap.id : M →ₗ[K] M))
        (PolynomialVector.monomial k a) = _
      rw [applyPolynomial_monomial]
      simp [PolynomialVector.monomial]

/-- **Cauchy composition computes successive polynomial application.**  This is the polynomial-path
version of `PolynomialLinearMap.applyVector_comp`. -/
theorem PolynomialLinearMap.applyPolynomial_comp (B : PolynomialLinearMap K N P)
    (A : PolynomialLinearMap K M N) (Q : PolynomialVector M) :
    applyPolynomial (comp B A) Q = applyPolynomial B (applyPolynomial A Q) := by
  classical
  induction B using Finsupp.induction_linear with
  | zero => simp
  | add B₁ B₂ h₁ h₂ =>
      simp only [comp_add_left, applyPolynomial_add_left, h₁, h₂]
  | single i f =>
      induction A using Finsupp.induction_linear with
      | zero => simp
      | add A₁ A₂ h₁ h₂ =>
          simp only [comp_add_right, applyPolynomial_add_left, applyPolynomial_add_right,
            h₁, h₂]
      | single j g =>
          induction Q using Finsupp.induction_linear with
          | zero => simp
          | add Q₁ Q₂ h₁ h₂ =>
              simp only [applyPolynomial_add_right, h₁, h₂]
          | single k a =>
              show applyPolynomial (comp (PolynomialVector.monomial i f)
                    (PolynomialVector.monomial j g)) (PolynomialVector.monomial k a) =
                  applyPolynomial (PolynomialVector.monomial i f)
                    (applyPolynomial (PolynomialVector.monomial j g)
                      (PolynomialVector.monomial k a))
              rw [comp, PolynomialVector.convolution_monomial, applyPolynomial_monomial,
                applyPolynomial_monomial, applyPolynomial_monomial, Nat.add_assoc]
              rfl

end PolynomialFamily

/-! ## Saturation of a finite family of polynomial vectors -/

section Saturation

open PolynomialVector PolynomialLinearMap

variable {K : Type u} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- A finite dual family adapted to a finite-dimensional subspace: vectors `ee i` and global
functionals `ψ i` that are dual to each other and reconstruct every vector of the subspace.

Proof sketch: take a finite basis `b` of `S`, extend the coordinate functionals to all of `M` by
composing with a left inverse of the inclusion (which exists over a field), and read off duality
and reconstruction from `Basis.repr_self` and `Basis.sum_repr`. -/
private theorem exists_dual_family_of_finite (S : Submodule K M) [FiniteDimensional K S] :
    ∃ (m : ℕ) (ee : Fin m → M) (ψ : Fin m → (M →ₗ[K] K)),
      (∀ i j, ψ i (ee j) = if i = j then 1 else 0) ∧
      (∀ v ∈ S, ∑ i, ψ i v • ee i = v) := by
  classical
  obtain ⟨pr, hpr⟩ := S.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype S)
  have hprS : ∀ x : S, pr (x : M) = x := by
    intro x
    have := congrArg (fun g : S →ₗ[K] S ↦ g x) hpr
    simpa using this
  set b := Module.finBasis K S with hbdef
  refine ⟨Module.finrank K S, fun i ↦ (b i : M), fun i ↦ (b.coord i).comp pr, ?_, ?_⟩
  · intro i j
    have hij : ((b.coord i).comp pr) ((b j : M)) = b.repr (b j) i := by
      rw [LinearMap.comp_apply, hprS (b j)]
      rfl
    rw [hij, b.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro v hv
    have hbv : pr v = (⟨v, hv⟩ : S) := hprS ⟨v, hv⟩
    have hstep : ∀ i, ((b.coord i).comp pr) v • ((b i : M)) =
        S.subtype (b.repr (⟨v, hv⟩ : S) i • b i) := by
      intro i
      rw [Submodule.subtype_apply, Submodule.coe_smul]
      congr 1
      rw [LinearMap.comp_apply, hbv]
      rfl
    calc ∑ i, ((b.coord i).comp pr) v • ((b i : M))
        = ∑ i, S.subtype (b.repr (⟨v, hv⟩ : S) i • b i) :=
          Finset.sum_congr rfl fun i _ ↦ hstep i
      _ = S.subtype (∑ i, b.repr (⟨v, hv⟩ : S) i • b i) := (map_sum _ _ _).symm
      _ = v := by rw [b.sum_repr]; rfl

/-- **Rank-one saturation step.**  For every polynomial vector `w` there is a polynomial family of
linear maps `s` fixing `w` whose degree-zero coefficient has rank at most one.

This is the valuative content of [TaoSawin2016, Corollary 2] in its cyclic case: the `K[λ]`-line
spanned by `w` is replaced by its saturation `K[λ] z`, where `w = f · z` and `f` generates the ideal
of coordinates of `w`.  Bézout in the principal ideal ring `K[λ]` produces a `K[λ]`-linear
functional `φ` with `φ z = 1`, and `s := z ∘ φ` is the associated projection onto that saturated
line; its degree-zero coefficient factors through the line spanned by the single vector `s 0 1`.

Proof sketch: let `S` be the (finite-dimensional) span of the coefficients of `w`, with dual family
`ee`, `ψ`.  The coordinates `wc i` of `w` are scalar polynomials, and `w = ∑ i, wc i · ee i`.  Let
`f` generate the ideal they span, `wc i = f * zc i`, and write `f = ∑ i, cc i * wc i`; cancelling
`f` gives `∑ i, cc i * zc i = 1`.  Then `φ := ∑ i, cc i · ψ i` sends `w` to `f`, and
`z := ∑ i, zc i · (1 ↦ ee i)` sends `f` back to `w`. -/
theorem exists_polynomialLinearMap_fixing_one (w : PolynomialVector M) :
    ∃ (s : PolynomialLinearMap K M M) (z : M),
      applyPolynomial s w = w ∧ LinearMap.range (s 0) ≤ Submodule.span K {z} := by
  classical
  by_cases hw : w = 0
  · exact ⟨0, 0, by simp [hw], by simp⟩
  -- The coefficients of `w` span a finite-dimensional subspace.
  have hmem : ∀ n, w n ∈ Submodule.span K ((w.support.image w : Finset M) : Set M) := by
    intro n
    by_cases hn : n ∈ w.support
    · exact Submodule.subset_span (by simpa using ⟨n, Finsupp.mem_support_iff.mp hn, rfl⟩)
    · rw [Finsupp.notMem_support_iff.mp hn]
      exact Submodule.zero_mem _
  obtain ⟨m, ee, ψ, hdual, hrec⟩ :=
    exists_dual_family_of_finite (Submodule.span K ((w.support.image w : Finset M) : Set M))
  have hrecw : ∀ n, ∑ i, ψ i (w n) • ee i = w n := fun n ↦ hrec (w n) (hmem n)
  -- Coordinates of `w` as scalar polynomials.
  obtain ⟨wc, hwc⟩ : ∃ wc : Fin m → Polynomial K, ∀ i k, (wc i).coeff k = ψ i (w k) := by
    refine ⟨fun i ↦ ∑ n ∈ w.support, Polynomial.monomial n (ψ i (w n)), fun i k ↦ ?_⟩
    rw [Polynomial.finsetSum_coeff]
    by_cases hk : k ∈ w.support
    · rw [Finset.sum_eq_single k]
      · rw [Polynomial.coeff_monomial, if_pos rfl]
      · intro n _ hn
        rw [Polynomial.coeff_monomial, if_neg hn]
      · intro h
        exact absurd hk h
    · rw [Finsupp.notMem_support_iff.mp hk, map_zero]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      rw [Polynomial.coeff_monomial, if_neg]
      rintro rfl
      exact hk hn
  have hwsplit : w = ∑ i, scalarSmul (wc i) (ee i) := by
    ext k
    rw [Finsupp.finsetSum_apply]
    simp only [scalarSmul_coeff, hwc]
    exact (hrecw k).symm
  -- The ideal generated by the coordinates is principal.
  obtain ⟨f, hf⟩ : ∃ f, (Ideal.span (Set.range wc) : Ideal (Polynomial K)) = Ideal.span {f} :=
    ⟨Submodule.IsPrincipal.generator _,
      (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
  have hmemI : ∀ i, wc i ∈ Ideal.span ({f} : Set (Polynomial K)) := by
    intro i
    rw [← hf]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hfne : f ≠ 0 := by
    intro hf0
    obtain ⟨n, hn⟩ : ∃ n, w n ≠ 0 := by
      by_contra h
      exact hw (Finsupp.ext fun n ↦ by simpa using not_not.mp (not_exists.mp h n))
    obtain ⟨i, hi⟩ : ∃ i, ψ i (w n) ≠ 0 := by
      by_contra h
      refine hn ?_
      rw [← hrecw n]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [not_not.mp (not_exists.mp h i), zero_smul]
    have hdvd0 : f ∣ wc i := Ideal.mem_span_singleton.mp (hmemI i)
    rw [hf0] at hdvd0
    exact hi (by rw [← hwc i n, zero_dvd_iff.mp hdvd0, Polynomial.coeff_zero])
  -- Divide the coordinates by the generator.
  have hdvd : ∀ i, ∃ q, wc i = f * q := fun i ↦ Ideal.mem_span_singleton.mp (hmemI i)
  choose zc hzc using hdvd
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (Polynomial K)).mp
    (show f ∈ Ideal.span (Set.range wc) by
      rw [hf]; exact Ideal.mem_span_singleton_self f)
  have hone : ∑ i, cc i * zc i = 1 := by
    refine mul_left_cancel₀ hfne ?_
    rw [mul_one, Finset.mul_sum]
    calc ∑ i, f * (cc i * zc i) = ∑ i, cc i • wc i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_eq_mul, hzc i]
          ring
      _ = f := hcc
  -- The two halves of the rank-one projection.
  refine ⟨comp (∑ i, scalarSmul (zc i) (LinearMap.toSpanSingleton K M (ee i)))
      (∑ i, scalarSmul (cc i) (ψ i)),
    (∑ i, scalarSmul (zc i) (LinearMap.toSpanSingleton K M (ee i))) 0 1, ?_, ?_⟩
  · rw [applyPolynomial_comp]
    have hφ : applyPolynomial (∑ i, scalarSmul (cc i) (ψ i)) w = scalarSmul f (1 : K) := by
      conv_lhs => rw [hwsplit]
      rw [applyPolynomial_finset_sum_left]
      have hinner : ∀ i : Fin m,
          applyPolynomial (scalarSmul (cc i) (ψ i)) (∑ j, scalarSmul (wc j) (ee j)) =
            scalarSmul (cc i * wc i) (1 : K) := by
        intro i
        rw [applyPolynomial_finset_sum_right, Finset.sum_eq_single i]
        · rw [applyPolynomial_scalarSmul, hdual i i, if_pos rfl]
        · intro j _ hj
          rw [applyPolynomial_scalarSmul, hdual i j, if_neg (Ne.symm hj),
            scalarSmul_zero_right]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [Finset.sum_congr rfl fun i _ ↦ hinner i, ← scalarSmul_finset_sum_left]
      congr 1
    rw [hφ, applyPolynomial_finset_sum_left]
    conv_rhs => rw [hwsplit]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [applyPolynomial_scalarSmul, LinearMap.toSpanSingleton_apply, one_smul, hzc i,
      mul_comm]
  · rintro y ⟨v, rfl⟩
    rw [comp_coeff_zero, LinearMap.comp_apply]
    have hlin : (∑ i, scalarSmul (zc i) (LinearMap.toSpanSingleton K M (ee i))) 0
        ((∑ i, scalarSmul (cc i) (ψ i)) 0 v) =
      ((∑ i, scalarSmul (cc i) (ψ i)) 0 v) •
        (∑ i, scalarSmul (zc i) (LinearMap.toSpanSingleton K M (ee i))) 0 1 := by
      rw [← map_smul]
      congr 1
      rw [smul_eq_mul, mul_one]
    rw [hlin]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Polynomial application is additive under differences of map families. -/
theorem PolynomialLinearMap.applyPolynomial_sub_left (A B : PolynomialLinearMap K M M)
    (Q : PolynomialVector M) :
    applyPolynomial (A - B) Q = applyPolynomial A Q - applyPolynomial B Q := by
  refine eq_sub_of_add_eq ?_
  rw [← applyPolynomial_add_left, sub_add_cancel]

/-- **Saturation of a finite family of polynomial vectors.**  For every finite list of polynomial
vectors there is a polynomial family of linear maps fixing each of them whose degree-zero
coefficient has rank at most the length of the list.

This is the finite form of the valuative criterion behind [TaoSawin2016, Corollary 2]: the
`K[λ]`-submodule generated by the family is replaced by a saturated one, whose reduction modulo `λ`
still has dimension at most the number of generators.

Proof sketch: induction on the list.  Given a family `q` fixing the tail, the head `u` is fixed
after adding the rank-one correction `s` of `exists_polynomialLinearMap_fixing_one` for the residue
`u - q u`, precomposed with `1 - q` so that the tail stays fixed.  The degree-zero coefficient of
the corrected family lands in the span of the previous list together with the one new vector. -/
theorem exists_polynomialLinearMap_fixing_list (us : List (PolynomialVector M)) :
    ∃ (q : PolynomialLinearMap K M M) (zs : List M),
      (∀ u ∈ us, applyPolynomial q u = u) ∧ zs.length ≤ us.length ∧
        LinearMap.range (q 0) ≤ Submodule.span K {v | v ∈ zs} := by
  induction us with
  | nil => exact ⟨0, [], by simp, by simp, by simp⟩
  | cons u rest ih =>
      obtain ⟨q', zs', hfix, hlen, hrange⟩ := ih
      obtain ⟨s, z, hs, hsrange⟩ :=
        exists_polynomialLinearMap_fixing_one (K := K) (u - applyPolynomial q' u)
      have hp : ∀ x : PolynomialVector M,
          applyPolynomial (PolynomialLinearMap.constant (LinearMap.id : M →ₗ[K] M) - q') x =
            x - applyPolynomial q' x := by
        intro x
        rw [applyPolynomial_sub_left, applyPolynomial_constant_id]
      refine ⟨q' + comp s (PolynomialLinearMap.constant (LinearMap.id : M →ₗ[K] M) - q'),
        z :: zs', ?_, ?_, ?_⟩
      · intro x hx
        rw [applyPolynomial_add_left, applyPolynomial_comp, hp]
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hs]
          abel
        · rw [hfix x hx, sub_self, applyPolynomial_zero_right, add_zero]
      · simpa using hlen
      · intro y hy
        obtain ⟨v, rfl⟩ := hy
        rw [Finsupp.add_apply, LinearMap.add_apply, comp_coeff_zero, LinearMap.comp_apply]
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.span_mono (fun x hx ↦ List.mem_cons_of_mem _ hx)
            (hrange ⟨v, rfl⟩)
        · refine Submodule.span_mono ?_ (hsrange ⟨_, rfl⟩)
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact List.mem_cons_self ..

end Saturation

/-! ## Monotonicity of slice rank under polynomial degeneration -/

section Degeneration

open PolynomialVector PolynomialLinearMap

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {W : Leg → Type w} [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- Transforming by monomial families of linear maps produces a monomial path. -/
private theorem polynomialTransform_monomial_maps (i j k : ℕ)
    (f : V .X →ₗ[K] W .X) (g : V .Y →ₗ[K] W .Y) (h : V .Z →ₗ[K] W .Z) (T : Tensor3 K V) :
    polynomialTransform (ofLegs (PolynomialVector.monomial i f) (PolynomialVector.monomial j g)
        (PolynomialVector.monomial k h)) T =
      PolynomialVector.monomial (i + j + k) (Tensor.map (ofLegs f g h) T) := by
  classical
  simp [polynomialTransform, PolynomialVector.monomial, ofLegs]

/-- Three-leg form of the degree-zero coefficient of a polynomial transform. -/
private theorem polynomialTransform_coeff_zero_ofLegs
    (AX : PolynomialLinearMap K (V .X) (W .X)) (AY : PolynomialLinearMap K (V .Y) (W .Y))
    (AZ : PolynomialLinearMap K (V .Z) (W .Z)) (T : Tensor3 K V) :
    polynomialTransform (ofLegs AX AY AZ) T 0 =
      Tensor.map (ofLegs (AX 0) (AY 0) (AZ 0)) T := by
  classical
  induction AX using Finsupp.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ =>
      rw [polynomialTransform_add_maps_X, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply,
        map_ofLegs_add_X]
  | single i f =>
      induction AY using Finsupp.induction_linear with
      | zero => simp
      | add A₁ A₂ h₁ h₂ =>
          rw [polynomialTransform_add_maps_Y, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply,
            map_ofLegs_add_Y]
      | single j g =>
          induction AZ using Finsupp.induction_linear with
          | zero => simp
          | add A₁ A₂ h₁ h₂ =>
              rw [polynomialTransform_add_maps_Z, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply,
                map_ofLegs_add_Z]
          | single k h =>
              show polynomialTransform (ofLegs (PolynomialVector.monomial i f)
                  (PolynomialVector.monomial j g) (PolynomialVector.monomial k h)) T 0 =
                Tensor.map (ofLegs (PolynomialVector.monomial i f 0)
                  (PolynomialVector.monomial j g 0) (PolynomialVector.monomial k h 0)) T
              rw [polynomialTransform_monomial_maps]
              by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hk : k = 0 <;>
                simp [PolynomialVector.monomial, hi, hj, hk]

/-- **The degree-zero coefficient of a polynomial transform** is the legwise image under the
degree-zero coefficient maps: only the choice `(0, 0, 0)` of the three coefficient degrees
contributes to total degree `0`. -/
theorem polynomialTransform_coeff_zero (A : ∀ c, PolynomialLinearMap K (V c) (W c))
    (T : Tensor3 K V) :
    polynomialTransform A T 0 = Tensor.map (fun c ↦ A c 0) T := by
  have h := polynomialTransform_coeff_zero_ofLegs (A .X) (A .Y) (A .Z) T
  rw [show ofLegs (A .X) (A .Y) (A .Z) = A from ofLegs_eta A] at h
  rw [show (fun c ↦ A c 0) = ofLegs (A .X 0) (A .Y 0) (A .Z 0) from by
    funext c; cases c <;> rfl]
  exact h

/-- **Leading coefficient of a transformed path.**  If a polynomial tensor path vanishes below
degree `d`, then transforming it by a polynomial family of legwise maps leaves the degree-`d`
coefficient equal to the legwise image of the original one under the degree-zero coefficient maps:
a shift of the input by `e ≥ d` and a transform degree `n > 0` cannot both stay in degree `d`. -/
theorem polynomialTransformPath_coeff_of_vanishing
    {U : Leg → Type*} [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (B : ∀ c, PolynomialLinearMap K (W c) (U c)) {P : PolynomialTensor K W} {d : ℕ}
    (h : ∀ n < d, P n = 0) :
    polynomialTransformPath B P d = Tensor.map (fun c ↦ B c 0) (P d) := by
  classical
  rw [polynomialTransformPath, Finsupp.sum, Finsupp.finsetSum_apply]
  by_cases hd : d ∈ P.support
  · rw [Finset.sum_eq_single d]
    · rw [PolynomialVector.shift_apply, if_pos le_rfl, Nat.sub_self,
        polynomialTransform_coeff_zero]
    · intro e he hed
      rw [PolynomialVector.shift_apply, if_neg]
      rcases Nat.lt_or_ge e d with hlt | hge
      · exact absurd (h e hlt) (Finsupp.mem_support_iff.mp he)
      · omega
    · intro hnot
      exact absurd hd hnot
  · have hP : P d = 0 := by
      by_contra hne
      exact hd (Finsupp.mem_support_iff.mpr hne)
    rw [hP, map_zero]
    refine Finset.sum_eq_zero fun e he ↦ ?_
    rw [PolynomialVector.shift_apply, if_neg]
    rcases Nat.lt_or_ge e d with hlt | hge
    · exact absurd (h e hlt) (Finsupp.mem_support_iff.mp he)
    · rcases eq_or_lt_of_le hge with rfl | hgt
      · exact absurd he hd
      · omega

/-- `PolySliceTermWith c u Q` is the polynomial-path analogue of `SliceTermWith`: the path `Q` is a
finite sum of polynomial pure tensors, all carrying the same leg-`c` polynomial vector `u`.  This is
what transporting one slice term along a polynomial family of legwise maps produces. -/
def PolySliceTermWith (c : Leg) (u : PolynomialVector (W c)) (Q : PolynomialTensor K W) : Prop :=
  ∃ factors : List (∀ i, PolynomialVector (W i)),
    (∀ y ∈ factors, y c = u) ∧ Q = (factors.map (polynomialPure (K := K))).sum

/-- Helper: a polynomial pure tensor with a vanishing leg vanishes. -/
private theorem polynomialPure_eq_zero_of_leg {c : Leg} (y : ∀ i, PolynomialVector (W i))
    (hy : y c = 0) : polynomialPure (K := K) y = 0 := by
  cases c with
  | X => rw [← ofLegs_eta y, hy]; exact polynomialPure_zero_X _ _
  | Y => rw [← ofLegs_eta y, hy]; exact polynomialPure_zero_Y _ _
  | Z => rw [← ofLegs_eta y, hy]; exact polynomialPure_zero_Z _ _

/-- A polynomial slice term is annihilated by any legwise family whose leg-`c` member kills the
slice vector. -/
theorem PolySliceTermWith.polynomialTransformPath_eq_zero {c : Leg}
    {u : PolynomialVector (W c)} {Q : PolynomialTensor K W} (h : PolySliceTermWith c u Q)
    (p : ∀ i, PolynomialLinearMap K (W i) (W i)) (hp : applyPolynomial (p c) u = 0) :
    polynomialTransformPath p Q = 0 := by
  obtain ⟨factors, hcomm, rfl⟩ := h
  induction factors with
  | nil => simp
  | cons y factors ih =>
      rw [List.map_cons, List.sum_cons, polynomialTransformPath_add,
        polynomialTransformPath_polynomialPure]
      rw [polynomialPure_eq_zero_of_leg _ (by rw [hcomm y (List.mem_cons_self ..), hp]),
        zero_add]
      exact ih fun y' hy' ↦ hcomm y' (List.mem_cons_of_mem _ hy')

/-- Transporting a slice term along a polynomial family of legwise maps produces a polynomial
slice term, whose polynomial slice vector is the transformed slice vector. -/
theorem SliceTermAlong.polySliceTermWith {c : Leg} {T : Tensor3 K V} (h : SliceTermAlong c T)
    (A : ∀ i, PolynomialLinearMap K (V i) (W i)) :
    ∃ u : PolynomialVector (W c), PolySliceTermWith c u (polynomialTransform A T) := by
  obtain ⟨v, factors, hcomm, rfl⟩ := h
  refine ⟨applyVector (A c) v,
    factors.map fun t i ↦ applyVector (A i) (t i), ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    show applyVector (A c) (t c) = applyVector (A c) v
    rw [hcomm t ht]
  · rw [polynomialTransform_list_sum, List.map_map, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t _ ↦ polynomialTransform_pure A t)

/-- **Transported slice vectors of a slice certificate.**  A list of slice terms transforms into a
path that is annihilated by every legwise family killing a finite per-leg list of polynomial
vectors, of total length at most the length of the certificate. -/
theorem exists_polySlice_lists (terms : List (Leg × Tensor3 K V))
    (hslice : ∀ p ∈ terms, SliceTermAlong p.1 p.2)
    (A : ∀ i, PolynomialLinearMap K (V i) (W i)) :
    ∃ us : ∀ i, List (PolynomialVector (W i)),
      (∑ i, (us i).length) ≤ terms.length ∧
      ∀ p : ∀ i, PolynomialLinearMap K (W i) (W i),
        (∀ i, ∀ u ∈ us i, applyPolynomial (p i) u = 0) →
        polynomialTransformPath p (polynomialTransform A (terms.map Prod.snd).sum) = 0 := by
  classical
  induction terms with
  | nil =>
      refine ⟨fun _ ↦ [], by simp, ?_⟩
      intro p _
      simp
  | cons pr rest ih =>
      obtain ⟨c, S⟩ := pr
      obtain ⟨us', hlen', hkey'⟩ := ih fun q hq ↦ hslice q (List.mem_cons_of_mem _ hq)
      obtain ⟨u, hu⟩ := (hslice (c, S) (List.mem_cons_self ..)).polySliceTermWith A
      refine ⟨Function.update us' c (u :: us' c), ?_, ?_⟩
      · rw [sum_leg]
        rw [sum_leg] at hlen'
        cases c with
        | X =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.Y ≠ Leg.X),
              Function.update_of_ne (by decide : Leg.Z ≠ Leg.X)]
            simp only [List.length_cons]
            omega
        | Y =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.X ≠ Leg.Y),
              Function.update_of_ne (by decide : Leg.Z ≠ Leg.Y)]
            simp only [List.length_cons]
            omega
        | Z =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.X ≠ Leg.Z),
              Function.update_of_ne (by decide : Leg.Y ≠ Leg.Z)]
            simp only [List.length_cons]
            omega
      · intro p hp
        have hpr : applyPolynomial (p c) u = 0 := by
          refine hp c u ?_
          rw [Function.update_self]
          exact List.mem_cons_self ..
        have hrest : ∀ i, ∀ u' ∈ us' i, applyPolynomial (p i) u' = 0 := by
          intro i u' hu'
          refine hp i u' ?_
          by_cases hi : i = c
          · subst hi
            rw [Function.update_self]
            exact List.mem_cons_of_mem _ hu'
          · rwa [Function.update_of_ne hi]
        rw [List.map_cons, List.sum_cons, polynomialTransform_add,
          polynomialTransformPath_add, hu.polynomialTransformPath_eq_zero p hpr,
          hkey' p hrest, add_zero]

end Degeneration

/-! ## Thesis Proposition 5.1 -/

section Main

open PolynomialVector PolynomialLinearMap

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {W : Leg → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- List form of `sliceRankAlongLE_of_mem_sliceSubmodule`. -/
theorem sliceRankAlongLE_of_mem_sliceSubmodule_list (c : Leg) (zs : List (W c))
    {T : Tensor3 K W} (hT : T ∈ sliceSubmodule c (Submodule.span K {v | v ∈ zs})) :
    SliceRankAlongLE c zs.length T := by
  have hsub : Submodule.span K {v | v ∈ zs} ≤
      Submodule.span K (Set.range fun k : Fin zs.length ↦ zs.get k) :=
    Submodule.span_mono fun v hv ↦ List.mem_iff_get.mp hv
  simpa using
    sliceRankAlongLE_of_mem_sliceSubmodule c (fun k : Fin zs.length ↦ zs.get k)
      (sliceSubmodule_mono hsub hT)

/-- **Thesis Proposition 5.1** ([TaoSawin2016, Corollary 2]) in certificate form: the leading
coefficient of a polynomial transform of `T` has slice rank at most that of `T`.

Proof sketch.  Take a slice decomposition of `T` into `r = sliceRank T` slice terms.  Transporting
it along the polynomial family `A` presents `P := polynomialTransform A T` as a sum of polynomial
slice terms, whose leg-`c` polynomial slice vectors form a finite list `us c`, with
`∑ c, |us c| ≤ r` (`exists_polySlice_lists`).  Saturating each list
(`exists_polynomialLinearMap_fixing_list`) yields polynomial families `q c` fixing every `us c` with
`rank (q c 0) ≤ |us c|`, spanned by a list `zs c`.  Setting `p c := 1 - q c`, the family `p`
annihilates every transported slice term, hence the whole path: `polynomialTransformPath p P = 0`.

Because `P` vanishes below its leading degree `d`, taking degree-`d` coefficients turns any legwise
polynomial family into its degree-zero coefficient acting on the leading tensor `S`
(`polynomialTransformPath_coeff_of_vanishing`); in particular `map (p · 0) S = 0`.  Expanding
`1 = q + p` legwise and telescoping,
`S = map (q_X, 1, 1) S + map (p_X, q_Y, 1) S + map (p_X, p_Y, q_Z) S + map (p_X, p_Y, p_Z) S`,
whose last summand vanishes.  Each remaining summand lies in the slice subspace of the range of one
`q c 0`, hence has leg-`c` slice rank at most `|zs c| ≤ |us c|`, and the three add up to at
most `r`. -/
theorem sliceRank_le_of_hasLeadingTerm_polynomialTransform {T : Tensor3 K V} {S : Tensor3 K W}
    {d : ℕ} {A : ∀ i, PolynomialLinearMap K (V i) (W i)}
    (hlead : HasLeadingTerm (polynomialTransform A T) d S) :
    sliceRank S ≤ sliceRank T := by
  classical
  obtain ⟨terms, hlen, hslice, hT⟩ := sliceRank_spec T
  obtain ⟨us, hlensum, hkey⟩ := exists_polySlice_lists terms hslice A
  choose q zs hfix hzlen hqrange using
    fun i ↦ exists_polynomialLinearMap_fixing_list (K := K) (us i)
  obtain ⟨p, hpdef⟩ : ∃ p : ∀ i, PolynomialLinearMap K (W i) (W i),
      ∀ i, p i = PolynomialLinearMap.constant LinearMap.id - q i := ⟨_, fun _ ↦ rfl⟩
  -- The complementary family annihilates every transported slice vector, hence the whole path.
  have hp0 : ∀ i, ∀ u ∈ us i, applyPolynomial (p i) u = 0 := by
    intro i u hu
    rw [hpdef i, applyPolynomial_sub_left, applyPolynomial_constant_id, hfix i u hu, sub_self]
  have hzero := hkey p hp0
  rw [← hT] at hzero
  -- Consequently the complementary family kills the leading coefficient.
  have hvanish : ∀ n < d, polynomialTransform A T n = 0 := fun n hn ↦ hlead.lower_coeff hn
  have hpzero : Tensor.map (fun i ↦ p i 0) S = 0 := by
    have h1 := polynomialTransformPath_coeff_of_vanishing p hvanish
    rw [hzero, hlead.coeff] at h1
    simpa using h1.symm
  have hid : ∀ i, q i 0 + p i 0 = LinearMap.id := by
    intro i
    rw [hpdef i, Finsupp.sub_apply]
    show q i 0 + (PolynomialVector.monomial 0 (LinearMap.id : W i →ₗ[K] W i) 0 - q i 0) = _
    rw [PolynomialVector.monomial_coeff_same]
    abel
  -- Telescope the legwise identity `1 = q + p`.
  have hidfam : ofLegs (LinearMap.id : W .X →ₗ[K] W .X) (LinearMap.id : W .Y →ₗ[K] W .Y)
      (LinearMap.id : W .Z →ₗ[K] W .Z) = fun i ↦ (LinearMap.id : W i →ₗ[K] W i) := by
    funext i
    cases i <;> rfl
  have hpfam : ofLegs (p .X 0) (p .Y 0) (p .Z 0) = fun i ↦ p i 0 := by
    funext i
    cases i <;> rfl
  have hZstep : Tensor.map (ofLegs (p .X 0) (p .Y 0) LinearMap.id) S =
      Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S := by
    rw [← hid .Z, map_ofLegs_add_Z, hpfam, hpzero, add_zero]
  have hYstep : Tensor.map (ofLegs (p .X 0) LinearMap.id LinearMap.id) S =
      Tensor.map (ofLegs (p .X 0) (q .Y 0) LinearMap.id) S +
        Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S := by
    rw [← hid .Y, map_ofLegs_add_Y, hZstep]
  have hSid : Tensor.map (ofLegs (LinearMap.id : W .X →ₗ[K] W .X)
      (LinearMap.id : W .Y →ₗ[K] W .Y) (LinearMap.id : W .Z →ₗ[K] W .Z)) S = S := by
    rw [hidfam, map_id]
    rfl
  have hdecomp : S = Tensor.map (ofLegs (q .X 0) LinearMap.id LinearMap.id) S +
      (Tensor.map (ofLegs (p .X 0) (q .Y 0) LinearMap.id) S +
        Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S) :=
    calc S = Tensor.map (ofLegs (LinearMap.id : W .X →ₗ[K] W .X)
            (LinearMap.id : W .Y →ₗ[K] W .Y) (LinearMap.id : W .Z →ₗ[K] W .Z)) S := hSid.symm
      _ = Tensor.map (ofLegs (q .X 0 + p .X 0) LinearMap.id LinearMap.id) S := by rw [hid .X]
      _ = Tensor.map (ofLegs (q .X 0) LinearMap.id LinearMap.id) S +
            Tensor.map (ofLegs (p .X 0) LinearMap.id LinearMap.id) S :=
          map_ofLegs_add_X _ _ _ _ S
      _ = Tensor.map (ofLegs (q .X 0) LinearMap.id LinearMap.id) S +
            (Tensor.map (ofLegs (p .X 0) (q .Y 0) LinearMap.id) S +
              Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S) := by rw [hYstep]
  -- Each surviving summand has small slice rank along its own leg.
  have hXmem : Tensor.map (ofLegs (q .X 0) (LinearMap.id : W .Y →ₗ[K] W .Y)
      (LinearMap.id : W .Z →ₗ[K] W .Z)) S ∈
      sliceSubmodule Leg.X (LinearMap.range (q Leg.X 0)) := by
    have h := map_mem_sliceSubmodule (K := K) (V := W) (W := W) Leg.X
      (ofLegs (q .X 0) (LinearMap.id : W .Y →ₗ[K] W .Y)
        (LinearMap.id : W .Z →ₗ[K] W .Z)) S
    simp only [ofLegs_X] at h
    exact h
  have hYmem : Tensor.map (ofLegs (p .X 0) (q .Y 0) (LinearMap.id : W .Z →ₗ[K] W .Z)) S ∈
      sliceSubmodule Leg.Y (LinearMap.range (q Leg.Y 0)) := by
    have h := map_mem_sliceSubmodule (K := K) (V := W) (W := W) Leg.Y
      (ofLegs (p .X 0) (q .Y 0) (LinearMap.id : W .Z →ₗ[K] W .Z)) S
    simp only [ofLegs_Y] at h
    exact h
  have hZmem : Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S ∈
      sliceSubmodule Leg.Z (LinearMap.range (q Leg.Z 0)) := by
    have h := map_mem_sliceSubmodule (K := K) (V := W) (W := W) Leg.Z
      (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S
    simp only [ofLegs_Z] at h
    exact h
  have hXrank : SliceRankAlongLE Leg.X (zs .X).length
      (Tensor.map (ofLegs (q .X 0) LinearMap.id LinearMap.id) S) :=
    sliceRankAlongLE_of_mem_sliceSubmodule_list Leg.X (zs .X)
      (sliceSubmodule_mono (hqrange .X) hXmem)
  have hYrank : SliceRankAlongLE Leg.Y (zs .Y).length
      (Tensor.map (ofLegs (p .X 0) (q .Y 0) LinearMap.id) S) :=
    sliceRankAlongLE_of_mem_sliceSubmodule_list Leg.Y (zs .Y)
      (sliceSubmodule_mono (hqrange .Y) hYmem)
  have hZrank : SliceRankAlongLE Leg.Z (zs .Z).length
      (Tensor.map (ofLegs (p .X 0) (p .Y 0) (q .Z 0)) S) :=
    sliceRankAlongLE_of_mem_sliceSubmodule_list Leg.Z (zs .Z)
      (sliceSubmodule_mono (hqrange .Z) hZmem)
  refine sliceRank_le_iff.mpr ?_
  rw [hdecomp]
  refine (hXrank.sliceRankLE.add (hYrank.sliceRankLE.add hZrank.sliceRankLE)).mono ?_
  rw [sum_leg] at hlensum
  have hX := hzlen Leg.X
  have hY := hzlen Leg.Y
  have hZ := hzlen Leg.Z
  omega

/-- **Thesis Proposition 5.1**: polynomial degeneration does not increase slice rank. -/
theorem sliceRank_le_of_polynomialDegenerates {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) : sliceRank S ≤ sliceRank T := by
  obtain ⟨A, d, hlead⟩ := h
  exact sliceRank_le_of_hasLeadingTerm_polynomialTransform hlead

end Main

end AlgebraicComplexity.Tensor
