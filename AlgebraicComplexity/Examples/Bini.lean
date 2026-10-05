/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoordinateCertificate
import AlgebraicComplexity.Tensor.Monomial
import AlgebraicComplexity.MatrixMultiplication.PartialAsymptoticSum

/-!
# Bini's five-term approximate algorithm for partial `2 × 2` multiplication

This file is a regression client for the border-rank API.  It formalizes the historically first
approximate (APA) matrix-multiplication algorithm, due to Bini, Capovani, Romani, and Lotti
(*O(n^2.7799) complexity for n × n approximate matrix multiplication*, Information Processing
Letters 8(5), 1979, pp. 234–235).

## Objects

* `biniPartial K` is the *partial* `2 × 2` matrix-multiplication tensor: the tensor of
  `matrixMultiplication K 2 2 2` with the two summands reading the deleted input entry `x₂₂`
  removed.  In coordinates its support consists of the six compatible index triples whose
  `X` index differs from `(1, 1)`.
* `biniCurve₁` … `biniCurve₅` are five explicit polynomial pure tensors (rank-one curves in the
  degeneration parameter `ε`), and `biniBorderPath` is their sum.

## Results

* `standardCoordinateEquiv_biniPartial`: the coordinate support formula for the partial tensor.
* `biniPartial_rankLE`: the trivial expansion gives exact rank at most `6`.
* `biniBorderPath_leading`: the certificate path equals `ε · biniPartial + O(ε²)`; that is, it
  has leading coefficient `biniPartial K` in degree `1`.
* `biniPartial_borderRankLEAt` / `biniPartial_borderRankLE`: the classical border-rank bound
  `R̲(biniPartial) ≤ 5`, with explicit leading degree `1`, over an arbitrary commutative ring.
* `matrixMultiplication_monomialDegenerates_biniPartial`: the full tensor `⟨2,2,2⟩` monomially
  degenerates to the partial tensor by weighting the deleted `x₂₂` coordinate.  The source of the
  degeneration is `⟨2,2,2⟩` and the result is `biniPartial K`.
* `biniPartial_eq_partialMatrixMultiplication`: `biniPartial K` is the partial
  matrix-multiplication tensor `partialMatrixMultiplication biniLeftPositions biniRightPositions`
  of the reusable theory, over every commutative semiring.
* `bini_omega_lt`: over every infinite field, `ω < 2.695`.

## Strategy

The tensor definition and both slices of the certificate are verified by coordinate expansion:
each identity between sums of pure tensors is transported through `standardCoordinateEquiv` to a
finite scalar table, the table is checked once over `ℤ` (or `ℕ`) with kernel-checked `decide`,
and a proved scalar-cast bridge transfers it to a general commutative (semi)ring.  This is the
same pattern as the Strassen regression client.

## Non-goals

The matching lower bounds (exact rank `6` is optimal, and rank `5` is impossible even though
border rank `5` holds) are not in scope.

The partial-to-total glue is no longer missing.  Schönhage's partial asymptotic sum inequality in
`AlgebraicComplexity/MatrixMultiplication/PartialAsymptoticSum.lean` consumes the border-rank-five
certificate directly, so `bini_omega_lt` derives `ω < 2.695` here rather than deferring to a later
client.  What remains out of scope is the historical elementary route: Bini's own `ω ≤ 2.7799…`
obtained by gluing two partial tensors into a total `⟨3, 3, 2⟩`-style tensor and applying
`omega_le_log_of_borderRankLEAt`.  That argument is strictly weaker than the bound proved here,
and is kept out of the file rather than duplicated.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open Tensor.PolynomialVector

universe u

section PartialTensor

variable (K : Type u) [CommSemiring K]

/-- The standard matrix unit `e_{ij}` in the coordinate space `Fin 2 × Fin 2 → K` shared by all
three legs of `⟨2,2,2⟩`. -/
def biniUnit (i j : Fin 2) : Fin 2 × Fin 2 → K :=
  Pi.single (i, j) 1

/-- The six summation triples `(i, j, k)` of the partial `2 × 2` product: all triples of
`⟨2,2,2⟩` except the two reading the deleted input entry `x₂₂`, i.e. except `(i, j) = (1, 1)`. -/
def biniPartialTriples : List (MMTriple 2 2 2) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1)]

/-- Bini's partial `2 × 2` matrix-multiplication tensor: the sum of the six standard summands
`x_{ij} ⊗ y_{jk} ⊗ z_{ki}` of `⟨2,2,2⟩` with `(i, j) ≠ (1, 1)`, so the input entry `x₂₂` is
never read. -/
noncomputable def biniPartial : Tensor3 K (MMSpace K 2 2 2) :=
  ((biniPartialTriples.map (mmTermOfTriple (K := K) 2 2 2)).map (pure (K := K))).sum

/-- Coordinate of the six-term expansion of `biniPartial` at a standard basis index. -/
def biniPartialCoefficient (R : Type*) [CommSemiring R] (a : ∀ c, MMIndex 2 2 2 c) : R :=
  MMCertificate.coefficient R (biniPartialTriples.map (mmTermOfTriple (K := R) 2 2 2)) a

/-- The finite natural-number coordinate table of the partial tensor: it is the indicator of the
compatible index triples avoiding the deleted `X` index `(1, 1)`. -/
theorem biniPartialCoefficient_nat (a : ∀ c, MMIndex 2 2 2 c) :
    biniPartialCoefficient ℕ a =
      if MMCompatible a ∧ a .X ≠ (1, 1) then 1 else 0 := by
  decide +revert

/-- The natural-number coordinate table of the partial tensor maps to the same table over every
commutative semiring. -/
theorem biniPartialCoefficient_cast (a : ∀ c, MMIndex 2 2 2 c) :
    biniPartialCoefficient K a = ((biniPartialCoefficient ℕ a : ℕ) : K) := by
  simp [biniPartialCoefficient, MMCertificate.coefficient, biniPartialTriples, mmTermOfTriple, mmTerm,
    prod_leg, Pi.single_apply]

/-- Coordinate support formula for the partial tensor: the coefficient at a standard basis index
is `1` exactly on compatible triples whose `X` index is not the deleted entry `(1, 1)`. -/
theorem standardCoordinateEquiv_biniPartial (a : ∀ c, MMIndex 2 2 2 c) :
    standardCoordinateEquiv (K := K) (κ := MMIndex 2 2 2) (biniPartial K) a =
      if MMCompatible a ∧ a .X ≠ (1, 1) then 1 else 0 := by
  unfold biniPartial
  rw [Tensor.standardCoordinateEquiv_list_sum_pure]
  change biniPartialCoefficient K a = _
  rw [biniPartialCoefficient_cast, biniPartialCoefficient_nat]
  split <;> simp

/-- The displayed six-term expansion is a constructive exact-rank certificate
`R(biniPartial) ≤ 6`. -/
theorem biniPartial_rankLE : RankLE 6 (biniPartial K) := by
  have h := RankLE.list_sum_pure (K := K)
    (biniPartialTriples.map (mmTermOfTriple (K := K) 2 2 2))
  have hlen : (biniPartialTriples.map (mmTermOfTriple (K := K) 2 2 2)).length = 6 := by
    simp [biniPartialTriples]
  rw [hlen] at h
  exact h

end PartialTensor

section Deletion

variable (K : Type u) [CommSemiring K]

/-- Monomial weight `1` on the deleted input coordinate `x₂₂` of the `X` leg and `0` on every
other coordinate of every leg. -/
def biniDeletionWeight : ∀ c, MMIndex 2 2 2 c → ℕ
  | .X => fun p ↦ if p = (1, 1) then 1 else 0
  | .Y => fun _ ↦ 0
  | .Z => fun _ ↦ 0

/-- Deleting the input entry `x₂₂` from the full tensor `⟨2,2,2⟩` yields the partial Bini
tensor: the source `matrixMultiplication K 2 2 2` monomially degenerates to the result
`biniPartial K` by weighting the deleted `X` coordinate.

Proof sketch: the weight assigns total degree `1` to the two summands reading `x₂₂` and total
degree `0` to the remaining six, so the degree-zero leading coefficient of the transformed path
is exactly the six-term partial tensor. -/
theorem matrixMultiplication_monomialDegenerates_biniPartial :
    MonomialDegenerates (matrixMultiplication (K := K) 2 2 2) (biniPartial K) := by
  refine ⟨biniDeletionWeight, 0, ?_, ?_⟩
  · unfold matrixMultiplication biniPartial
    rw [monomialTransform_fintype_sum]
    simp_rw [mmTermOfTriple_eq_single, monomialTransform_basis]
    rw [Finsupp.finsetSum_apply]
    simp +decide [mmTermOfTriple_eq_single, Fintype.sum_prod_type, Fin.sum_univ_two,
      monomialTotalWeight, biniDeletionWeight, mmPoint, biniPartialTriples,
      add_assoc]
  · intro e he
    exact absurd he (Nat.not_lt_zero e)

end Deletion

section Certificate

variable (K : Type u) [CommRing K]

/-- First rank-one curve of Bini's certificate:
`(x₁₂ + ε x₁₁) ⊗ (y₁₂ + ε y₂₂) ⊗ z₂₁`. -/
noncomputable def biniCurve₁ : ∀ c, PolynomialVector (MMSpace K 2 2 2 c) :=
  ofLegs (constant (biniUnit K 0 1) + monomial 1 (biniUnit K 0 0))
    (constant (biniUnit K 0 1) + monomial 1 (biniUnit K 1 1))
    (constant (biniUnit K 1 0))

/-- Second rank-one curve of Bini's certificate:
`(x₂₁ + ε x₁₁) ⊗ y₁₁ ⊗ (z₁₁ + ε z₁₂)`. -/
noncomputable def biniCurve₂ : ∀ c, PolynomialVector (MMSpace K 2 2 2 c) :=
  ofLegs (constant (biniUnit K 1 0) + monomial 1 (biniUnit K 0 0))
    (constant (biniUnit K 0 0))
    (constant (biniUnit K 0 0) + monomial 1 (biniUnit K 0 1))

/-- Third rank-one curve of Bini's certificate:
`(−x₁₂) ⊗ y₁₂ ⊗ (z₁₁ + z₂₁ + ε z₂₂)`. -/
noncomputable def biniCurve₃ : ∀ c, PolynomialVector (MMSpace K 2 2 2 c) :=
  ofLegs (constant (-(biniUnit K 0 1)))
    (constant (biniUnit K 0 1))
    (constant (biniUnit K 0 0 + biniUnit K 1 0) + monomial 1 (biniUnit K 1 1))

/-- Fourth rank-one curve of Bini's certificate:
`(−x₂₁) ⊗ (y₁₁ + y₁₂ + ε y₂₁) ⊗ z₁₁`. -/
noncomputable def biniCurve₄ : ∀ c, PolynomialVector (MMSpace K 2 2 2 c) :=
  ofLegs (constant (-(biniUnit K 1 0)))
    (constant (biniUnit K 0 0 + biniUnit K 0 1) + monomial 1 (biniUnit K 1 0))
    (constant (biniUnit K 0 0))

/-- Fifth rank-one curve of Bini's certificate:
`(x₁₂ + x₂₁) ⊗ (y₁₂ + ε y₂₁) ⊗ (z₁₁ + ε z₂₂)`. -/
noncomputable def biniCurve₅ : ∀ c, PolynomialVector (MMSpace K 2 2 2 c) :=
  ofLegs (constant (biniUnit K 0 1 + biniUnit K 1 0))
    (constant (biniUnit K 0 1) + monomial 1 (biniUnit K 1 0))
    (constant (biniUnit K 0 0) + monomial 1 (biniUnit K 1 1))

/-- The explicit list of the five polynomial pure tensors in Bini's approximation. -/
noncomputable def biniBorderTerms : List (∀ c, PolynomialVector (MMSpace K 2 2 2 c)) :=
  [biniCurve₁ K, biniCurve₂ K, biniCurve₃ K, biniCurve₄ K, biniCurve₅ K]

@[simp] theorem biniBorderTerms_length : (biniBorderTerms K).length = 5 := by
  simp [biniBorderTerms]

/-- The polynomial tensor path represented by Bini's explicit certificate. -/
noncomputable def biniBorderPath : PolynomialTensor K (MMSpace K 2 2 2) :=
  ((biniBorderTerms K).map (polynomialPure (K := K))).sum

/-- The certificate path is the sum of the five displayed polynomial pure tensors. -/
theorem biniBorderPath_eq :
    biniBorderPath K =
      polynomialPure (K := K) (biniCurve₁ K) +
        polynomialPure (K := K) (biniCurve₂ K) +
        polynomialPure (K := K) (biniCurve₃ K) +
        polynomialPure (K := K) (biniCurve₄ K) +
        polynomialPure (K := K) (biniCurve₅ K) := by
  simp [biniBorderPath, biniBorderTerms, add_assoc]

/-- Constant (`ε⁰`) coefficient of the first curve. -/
@[simp] theorem biniCurve₁_coeff_zero :
    polynomialPure (K := K) (biniCurve₁ K) 0 =
      pure (K := K) (ofLegs (biniUnit K 0 1) (biniUnit K 0 1) (biniUnit K 1 0)) := by
  simp [biniCurve₁, constant]

/-- Linear (`ε¹`) coefficient of the first curve. -/
@[simp] theorem biniCurve₁_coeff_one :
    polynomialPure (K := K) (biniCurve₁ K) 1 =
      pure (K := K) (ofLegs (biniUnit K 0 1) (biniUnit K 1 1) (biniUnit K 1 0)) +
        pure (K := K) (ofLegs (biniUnit K 0 0) (biniUnit K 0 1) (biniUnit K 1 0)) := by
  simp [biniCurve₁, constant]
  abel

/-- Constant (`ε⁰`) coefficient of the second curve. -/
@[simp] theorem biniCurve₂_coeff_zero :
    polynomialPure (K := K) (biniCurve₂ K) 0 =
      pure (K := K) (ofLegs (biniUnit K 1 0) (biniUnit K 0 0) (biniUnit K 0 0)) := by
  simp [biniCurve₂, constant]

/-- Linear (`ε¹`) coefficient of the second curve. -/
@[simp] theorem biniCurve₂_coeff_one :
    polynomialPure (K := K) (biniCurve₂ K) 1 =
      pure (K := K) (ofLegs (biniUnit K 1 0) (biniUnit K 0 0) (biniUnit K 0 1)) +
        pure (K := K) (ofLegs (biniUnit K 0 0) (biniUnit K 0 0) (biniUnit K 0 0)) := by
  simp [biniCurve₂, constant]
  abel

/-- Constant (`ε⁰`) coefficient of the third curve. -/
@[simp] theorem biniCurve₃_coeff_zero :
    polynomialPure (K := K) (biniCurve₃ K) 0 =
      pure (K := K) (ofLegs (-(biniUnit K 0 1)) (biniUnit K 0 1)
        (biniUnit K 0 0 + biniUnit K 1 0)) := by
  simp [biniCurve₃, constant]

/-- Linear (`ε¹`) coefficient of the third curve. -/
@[simp] theorem biniCurve₃_coeff_one :
    polynomialPure (K := K) (biniCurve₃ K) 1 =
      pure (K := K) (ofLegs (-(biniUnit K 0 1)) (biniUnit K 0 1) (biniUnit K 1 1)) := by
  simp [biniCurve₃, constant]

/-- Constant (`ε⁰`) coefficient of the fourth curve. -/
@[simp] theorem biniCurve₄_coeff_zero :
    polynomialPure (K := K) (biniCurve₄ K) 0 =
      pure (K := K) (ofLegs (-(biniUnit K 1 0)) (biniUnit K 0 0 + biniUnit K 0 1)
        (biniUnit K 0 0)) := by
  simp [biniCurve₄, constant]

/-- Linear (`ε¹`) coefficient of the fourth curve. -/
@[simp] theorem biniCurve₄_coeff_one :
    polynomialPure (K := K) (biniCurve₄ K) 1 =
      pure (K := K) (ofLegs (-(biniUnit K 1 0)) (biniUnit K 1 0) (biniUnit K 0 0)) := by
  simp [biniCurve₄, constant]

/-- Constant (`ε⁰`) coefficient of the fifth curve. -/
@[simp] theorem biniCurve₅_coeff_zero :
    polynomialPure (K := K) (biniCurve₅ K) 0 =
      pure (K := K) (ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 0 1)
        (biniUnit K 0 0)) := by
  simp [biniCurve₅, constant]

/-- Linear (`ε¹`) coefficient of the fifth curve. -/
@[simp] theorem biniCurve₅_coeff_one :
    polynomialPure (K := K) (biniCurve₅ K) 1 =
      pure (K := K) (ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 0 1)
          (biniUnit K 1 1)) +
        pure (K := K) (ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 1 0)
          (biniUnit K 0 0)) := by
  simp [biniCurve₅, constant]
  abel

/-- The five constant leg triples of the certificate, one per curve. -/
def biniZeroTerms : List (∀ c, MMSpace K 2 2 2 c) :=
  [ ofLegs (biniUnit K 0 1) (biniUnit K 0 1) (biniUnit K 1 0),
    ofLegs (biniUnit K 1 0) (biniUnit K 0 0) (biniUnit K 0 0),
    ofLegs (-(biniUnit K 0 1)) (biniUnit K 0 1) (biniUnit K 0 0 + biniUnit K 1 0),
    ofLegs (-(biniUnit K 1 0)) (biniUnit K 0 0 + biniUnit K 0 1) (biniUnit K 0 0),
    ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 0 1) (biniUnit K 0 0) ]

/-- The eight leg triples contributing to the linear (`ε¹`) coefficient of the certificate. -/
def biniOneTerms : List (∀ c, MMSpace K 2 2 2 c) :=
  [ ofLegs (biniUnit K 0 1) (biniUnit K 1 1) (biniUnit K 1 0),
    ofLegs (biniUnit K 0 0) (biniUnit K 0 1) (biniUnit K 1 0),
    ofLegs (biniUnit K 1 0) (biniUnit K 0 0) (biniUnit K 0 1),
    ofLegs (biniUnit K 0 0) (biniUnit K 0 0) (biniUnit K 0 0),
    ofLegs (-(biniUnit K 0 1)) (biniUnit K 0 1) (biniUnit K 1 1),
    ofLegs (-(biniUnit K 1 0)) (biniUnit K 1 0) (biniUnit K 0 0),
    ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 0 1) (biniUnit K 1 1),
    ofLegs (biniUnit K 0 1 + biniUnit K 1 0) (biniUnit K 1 0) (biniUnit K 0 0) ]

/-- Coordinate of the constant slice of the certificate at a standard basis index. -/
def biniZeroCoefficient (R : Type*) [CommRing R] (a : ∀ c, MMIndex 2 2 2 c) : R :=
  MMCertificate.coefficient R (biniZeroTerms R) a

/-- The integer coordinate table of the constant slice vanishes identically. -/
theorem biniZeroCoefficient_int (a : ∀ c, MMIndex 2 2 2 c) :
    biniZeroCoefficient ℤ a = 0 := by
  decide +revert

/-- The integer table of the constant slice maps to the same table over every commutative
ring. -/
theorem biniZeroCoefficient_cast (a : ∀ c, MMIndex 2 2 2 c) :
    biniZeroCoefficient K a = ((biniZeroCoefficient ℤ a : ℤ) : K) := by
  simp [biniZeroCoefficient, MMCertificate.coefficient, biniZeroTerms, biniUnit, ofLegs, prod_leg,
    Pi.single_apply]

/-- Coordinate of the linear slice of the certificate at a standard basis index. -/
def biniOneCoefficient (R : Type*) [CommRing R] (a : ∀ c, MMIndex 2 2 2 c) : R :=
  MMCertificate.coefficient R (biniOneTerms R) a

/-- The integer coordinate table of the linear slice is the support indicator of the partial
tensor. -/
theorem biniOneCoefficient_int (a : ∀ c, MMIndex 2 2 2 c) :
    biniOneCoefficient ℤ a =
      if MMCompatible a ∧ a .X ≠ (1, 1) then 1 else 0 := by
  decide +revert

/-- The integer table of the linear slice maps to the same table over every commutative ring. -/
theorem biniOneCoefficient_cast (a : ∀ c, MMIndex 2 2 2 c) :
    biniOneCoefficient K a = ((biniOneCoefficient ℤ a : ℤ) : K) := by
  simp [biniOneCoefficient, MMCertificate.coefficient, biniOneTerms, biniUnit, ofLegs, prod_leg,
    Pi.single_apply]

/-- The constant terms of the five curves cancel exactly: the `ε⁰` slice of Bini's certificate is
the zero tensor. -/
theorem biniZeroTerms_sum :
    ((biniZeroTerms K).map (pure (K := K))).sum =
      (0 : Tensor3 K (MMSpace K 2 2 2)) := by
  apply standardCoordinate_ext
  intro a
  rw [Tensor.standardCoordinateEquiv_list_sum_pure]
  change biniZeroCoefficient K a = _
  rw [biniZeroCoefficient_cast, biniZeroCoefficient_int]
  simp

/-- The linear terms of the five curves sum exactly to the partial tensor: the `ε¹` slice of
Bini's certificate is `biniPartial K`. -/
theorem biniOneTerms_sum :
    ((biniOneTerms K).map (pure (K := K))).sum = biniPartial K := by
  apply standardCoordinate_ext
  intro a
  rw [Tensor.standardCoordinateEquiv_list_sum_pure, standardCoordinateEquiv_biniPartial]
  change biniOneCoefficient K a = _
  rw [biniOneCoefficient_cast, biniOneCoefficient_int]
  split <;> simp

/-- The certificate path has vanishing constant coefficient. -/
theorem biniBorderPath_coeff_zero : biniBorderPath K 0 = 0 := by
  have h : biniBorderPath K 0 = ((biniZeroTerms K).map (pure (K := K))).sum := by
    rw [biniBorderPath_eq]
    simp [biniZeroTerms, add_assoc]
  rw [h, biniZeroTerms_sum]

/-- The linear coefficient of the certificate path is the partial tensor. -/
theorem biniBorderPath_coeff_one : biniBorderPath K 1 = biniPartial K := by
  have h : biniBorderPath K 1 = ((biniOneTerms K).map (pure (K := K))).sum := by
    rw [biniBorderPath_eq]
    simp [biniOneTerms, add_assoc]
  rw [h, biniOneTerms_sum]

/-- Bini's polynomial path equals `ε · biniPartial + O(ε²)`: it has the partial tensor as its
degree-one leading term. -/
theorem biniBorderPath_leading :
    HasLeadingTerm (biniBorderPath K) 1 (biniPartial K) := by
  constructor
  · exact biniBorderPath_coeff_one K
  · intro e he
    rw [Nat.lt_one_iff] at he
    subst he
    exact biniBorderPath_coeff_zero K

/-- Bini–Capovani–Romani–Lotti (1979): the partial `2 × 2` matrix-multiplication tensor with the
input entry `x₂₂` deleted has border rank at most `5`, witnessed by an explicit degree-one
polynomial certificate.

Proof sketch: the five rank-one curves `biniCurve₁ … biniCurve₅` are polynomial in the
degeneration parameter `ε` with degree at most one on each leg.  Their `ε⁰` slice cancels
(`biniZeroTerms_sum`) and their `ε¹` slice is exactly the partial tensor (`biniOneTerms_sum`);
both slice identities are checked as finite coordinate tables over `ℤ` and transported to `K`
through a proved scalar-cast bridge.  Hence the summed path is `ε · biniPartial + O(ε²)`, which
is precisely a degree-one border-rank certificate of size five. -/
theorem biniPartial_borderRankLEAt : BorderRankLEAt 5 1 (biniPartial K) :=
  ⟨biniBorderTerms K, by simp, biniBorderPath_leading K⟩

/-- Certificate-facing corollary: `R̲(biniPartial) ≤ 5` over every commutative ring. -/
theorem biniPartial_borderRankLE : BorderRankLE 5 (biniPartial K) :=
  (biniPartial_borderRankLEAt K).toBorderRankLE

end Certificate

section ExponentBound

/-- Bini's hand-built partial tensor **is** the partial matrix-multiplication tensor of the
reusable theory: `biniPartial K` equals `partialMatrixMultiplication biniLeftPositions
biniRightPositions` for the index types `κ = μ = ν = Fin 2`.

The two sides are the same object in different clothing.  `MMSpace K 2 2 2` and
`PMMSpace (Fin 2) (Fin 2) (Fin 2) K` are the same three coordinate spaces, `MMCompatible` and
`PMMCompatible` are the same three compatibility equations, and the two support predicates agree:
an `X` index lies in `biniLeftPositions` exactly when it is not the deleted entry `(1, 1)`, and
every `Y` index lies in `biniRightPositions`.  The identification therefore follows from the
coordinate support formula `standardCoordinateEquiv_biniPartial` through the criterion
`eq_partialMatrixMultiplication_of_coordinates`.

This is the client-side bridge that `AlgebraicComplexity/MatrixMultiplication/
PartialAsymptoticSum.lean` deliberately leaves to the example layer, since that module must not
import a named construction. -/
theorem biniPartial_eq_partialMatrixMultiplication (K : Type u) [CommSemiring K] :
    biniPartial K =
      partialMatrixMultiplication (K := K) biniLeftPositions biniRightPositions := by
  refine eq_partialMatrixMultiplication_of_coordinates fun a ↦ ?_
  refine (standardCoordinateEquiv_biniPartial K a).trans (if_congr ?_ rfl rfl)
  simp [biniLeftPositions, biniRightPositions]

/-- **Bini's exponent bound, unconditionally**: over every infinite field, `ω < 2.695`.

Schönhage (*Partial and total matrix multiplication*, SIAM J. Comput. 10(3), 1981, p. 435)
observes that his partial asymptotic sum inequality applied to the five-term approximate
algorithm of Bini, Capovani, Romani, and Lotti (*O(n^2.7799) complexity for n × n approximate
matrix multiplication*, Information Processing Letters 8(5), 1979, pp. 234–235) yields
`ω ≤ 3 ln 5 / ln 6 < 2.695`, well below the `2.7799…` that the same algorithm gives by the
elementary gluing argument.

The border-rank-five certificate is `biniPartial_borderRankLE`; the identification
`biniPartial_eq_partialMatrixMultiplication` turns it into the hypothesis of
`omega_lt_of_borderRankLE_biniPartial`, which supplies the partial asymptotic sum inequality and
the numerical estimate. -/
theorem bini_omega_lt (F : Type u) [Field F] [Infinite F] : omega F < 2.695 := by
  refine omega_lt_of_borderRankLE_biniPartial F ?_
  rw [← biniPartial_eq_partialMatrixMultiplication F]
  exact biniPartial_borderRankLE F

end ExponentBound

end AlgebraicComplexity.Examples
