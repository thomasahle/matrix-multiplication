import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRankProof

set_option linter.style.header false

/-!
# The `q + 2` border-rank theorem for the Coppersmith--Winograd tensor

The explicit polynomial family from `CoppersmithWinogradBorderRank` is verified here.  The proof is
coordinatewise and symbolic over an arbitrary commutative ring: coefficients below degree five
cancel and the degree-five coefficient is exactly `CW_q`.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable {K : Type u} [CommRing K]

private theorem curveMiddle_coeff_lt_five
    (q : ℕ) (i : Fin q) (a b c : CWIndex q) {degree : ℕ} (hdegree : degree < 5) :
    ((cwCurveMiddleTerm (K := K) q i).toTensor a b c).coeff degree =
      if degree = 1 then
        cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c
      else if degree = 3 then
        cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
            cwBasis (K := K) q (TriTensor.cwZero q) b *
            cwBasis (K := K) q (TriTensor.cwZero q) c +
          cwBasis (K := K) q (TriTensor.cwZero q) a *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
            cwBasis (K := K) q (TriTensor.cwZero q) c +
          cwBasis (K := K) q (TriTensor.cwZero q) a *
            cwBasis (K := K) q (TriTensor.cwZero q) b *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) c
      else 0 := by
  simpa [cwCurveMiddleTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor, mul_assoc] using
    middleFactor_coeff_lt_five
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) c) hdegree

private theorem curveMiddle_coeff_five
    (q : ℕ) (i : Fin q) (a b c : CWIndex q) :
    ((cwCurveMiddleTerm (K := K) q i).toTensor a b c).coeff 5 =
      cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
          cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c +
        cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwMiddle q i) c +
        cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
          cwBasis (K := K) q (TriTensor.cwMiddle q i) c := by
  simpa [cwCurveMiddleTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor, mul_assoc] using
    middleFactor_coeff_five
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (cwBasis (K := K) q (TriTensor.cwMiddle q i) c)

private theorem curveCancellation_coeff_lt_five
    (q : ℕ) (a b c : CWIndex q) {degree : ℕ} (hdegree : degree < 5) :
    ((cwCurveCancellationTerm (K := K) q).toTensor a b c).coeff degree =
      if degree = 0 then
        -(cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c)
      else if degree = 3 then
        -((∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) a) *
              cwBasis (K := K) q (TriTensor.cwZero q) b *
              cwBasis (K := K) q (TriTensor.cwZero q) c +
            cwBasis (K := K) q (TriTensor.cwZero q) a *
              (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) b) *
              cwBasis (K := K) q (TriTensor.cwZero q) c +
            cwBasis (K := K) q (TriTensor.cwZero q) a *
              cwBasis (K := K) q (TriTensor.cwZero q) b *
              (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) c))
      else 0 := by
  simpa [cwCurveCancellationTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor,
    cwPolynomialMiddleSum_eq_C, mul_assoc] using
    cancellationFactor_coeff_lt_five
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) c) hdegree

private theorem curveCancellation_coeff_five
    (q : ℕ) (a b c : CWIndex q) :
    ((cwCurveCancellationTerm (K := K) q).toTensor a b c).coeff 5 = 0 := by
  simpa [cwCurveCancellationTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor,
    cwPolynomialMiddleSum_eq_C, mul_assoc] using
    cancellationFactor_coeff_five
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) c)

private theorem curveCorner_coeff_lt_five
    (q : ℕ) (a b c : CWIndex q) {degree : ℕ} (hdegree : degree < 5) :
    ((cwCurveCornerTerm (K := K) q).toTensor a b c).coeff degree =
      if degree = 0 then
        cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c
      else if degree = 1 then
        -((q : K) * cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c)
      else 0 := by
  simpa [cwCurveCornerTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor, mul_assoc] using
    cornerFactor_coeff_lt_five q
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (cwBasis (K := K) q (TriTensor.cwLast q) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (cwBasis (K := K) q (TriTensor.cwLast q) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (cwBasis (K := K) q (TriTensor.cwLast q) c) hdegree

private theorem curveCorner_coeff_five
    (q : ℕ) (a b c : CWIndex q) :
    ((cwCurveCornerTerm (K := K) q).toTensor a b c).coeff 5 =
      cwBasis (K := K) q (TriTensor.cwLast q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c +
        cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwLast q) b *
          cwBasis (K := K) q (TriTensor.cwZero q) c +
        cwBasis (K := K) q (TriTensor.cwZero q) a *
          cwBasis (K := K) q (TriTensor.cwZero q) b *
          cwBasis (K := K) q (TriTensor.cwLast q) c := by
  simpa [cwCurveCornerTerm, cwPolynomialBasis, PolynomialPureTerm.toTensor, mul_assoc] using
    cornerFactor_coeff_five q
      (cwBasis (K := K) q (TriTensor.cwZero q) a)
      (cwBasis (K := K) q (TriTensor.cwLast q) a)
      (cwBasis (K := K) q (TriTensor.cwZero q) b)
      (cwBasis (K := K) q (TriTensor.cwLast q) b)
      (cwBasis (K := K) q (TriTensor.cwZero q) c)
      (cwBasis (K := K) q (TriTensor.cwLast q) c)

/-- Every coefficient below degree five of the `q+2` curve vanishes. -/
theorem cwPolynomialCurve_vanishesBelow_five (q : ℕ) :
    VanishesBelow 5 (cwPolynomialCurve (K := K) q) := by
  intro degree hdegree
  funext a b c
  rw [coeffTensor_apply, cwPolynomialCurve_apply]
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  simp_rw [curveMiddle_coeff_lt_five q _ a b c hdegree]
  rw [curveCancellation_coeff_lt_five q a b c hdegree,
    curveCorner_coeff_lt_five q a b c hdegree]
  interval_cases degree <;>
    simp [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, nsmul_eq_mul] <;> ring

/-- The degree-five coefficient of the curve is exactly the coordinate tensor `CW_q`. -/
theorem cwPolynomialCurve_coeff_five (q : ℕ) :
    coeffTensor 5 (cwPolynomialCurve (K := K) q) =
      coppersmithWinogradCoordinateTensor K q := by
  funext a b c
  rw [coeffTensor_apply, cwPolynomialCurve_apply]
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  simp_rw [curveMiddle_coeff_five q _ a b c]
  rw [curveCancellation_coeff_five q a b c, curveCorner_coeff_five q a b c]
  unfold coppersmithWinogradCoordinateTensor
  have hsum :
      (∑ i : Fin q,
        (cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
            cwBasis (K := K) q (TriTensor.cwZero q) c +
          cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
            cwBasis (K := K) q (TriTensor.cwZero q) b *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) c +
          cwBasis (K := K) q (TriTensor.cwZero q) a *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
            cwBasis (K := K) q (TriTensor.cwMiddle q i) c)) =
        ∑ i : Fin q,
          (cwBasis (K := K) q (TriTensor.cwZero q) a *
              cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
              cwBasis (K := K) q (TriTensor.cwMiddle q i) c +
            cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
              cwBasis (K := K) q (TriTensor.cwZero q) b *
              cwBasis (K := K) q (TriTensor.cwMiddle q i) c +
            cwBasis (K := K) q (TriTensor.cwMiddle q i) a *
              cwBasis (K := K) q (TriTensor.cwMiddle q i) b *
              cwBasis (K := K) q (TriTensor.cwZero q) c) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- The big Coppersmith--Winograd tensor has border rank at most `q+2`. -/
theorem coppersmithWinograd_borderRank_le (q : ℕ) :
    HasBorderRankAtMost (q + 2) (coppersmithWinogradCoordinateTensor K q) := by
  refine HasBorderRankAtMost.of_family (order := 5)
    (cwCurveTerms (K := K) q) (by rfl) ?_ ?_
  · exact cwPolynomialCurve_vanishesBelow_five (K := K) q
  · exact cwPolynomialCurve_coeff_five (K := K) q

#print axioms cwPolynomialCurve_vanishesBelow_five
#print axioms cwPolynomialCurve_coeff_five
#print axioms coppersmithWinograd_borderRank_le

end CoordinateTensor
end AlgebraicComplexity
