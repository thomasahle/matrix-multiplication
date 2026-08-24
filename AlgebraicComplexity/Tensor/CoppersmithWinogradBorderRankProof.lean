import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRank

set_option linter.style.header false

/-!
# Verification lemmas for the Coppersmith--Winograd border-rank curve

The cancellation is checked coefficient-by-coefficient through degree five.  These algebraic helper
lemmas are public because the final `q+2` theorem is assembled in
`CoppersmithWinogradBorderRankTheorem`.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable {K : Type u} [CommRing K]

@[simp]
theorem cwPolynomialMiddleSum_eq_C (q : ℕ) (a : CWIndex q) :
    cwPolynomialMiddleSum (K := K) q a =
      Polynomial.C (∑ i : Fin q, cwBasis (K := K) q (TriTensor.cwMiddle q i) a) := by
  simp [cwPolynomialMiddleSum, cwPolynomialBasis]

/-- Split the `Fin (q+2)` curve sum into its `q`, cancellation, and corner terms. -/
theorem cwPolynomialCurve_apply (q : ℕ) (a b c : CWIndex q) :
    cwPolynomialCurve (K := K) q a b c =
      (∑ i : Fin q, (cwCurveMiddleTerm (K := K) q i).toTensor a b c) +
      (cwCurveCancellationTerm (K := K) q).toTensor a b c +
      (cwCurveCornerTerm (K := K) q).toTensor a b c := by
  simp [cwPolynomialCurve, realizePolynomialFamily, cwCurveTerms]

theorem middleFactor_coeff_lt_five
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) {degree : ℕ} (hdegree : degree < 5) :
    (Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁)).coeff degree =
      if degree = 1 then x₀ * y₀ * z₀
      else if degree = 3 then
        x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁
      else 0 := by
  have hexpand :
      Polynomial.X *
          (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁) =
        Polynomial.C (x₀ * y₀ * z₀) * Polynomial.X +
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 3 +
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 5 +
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 7 := by
    ring
  rw [hexpand]
  interval_cases degree <;> simp

theorem middleFactor_coeff_five
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    (Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁)).coeff 5 =
      x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁ := by
  have hexpand :
      Polynomial.X *
          (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁) =
        Polynomial.C (x₀ * y₀ * z₀) * Polynomial.X +
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 3 +
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 5 +
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 7 := by
    ring
  rw [hexpand]
  simp

theorem cancellationFactor_coeff_lt_five
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) {degree : ℕ} (hdegree : degree < 5) :
    (-(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁)).coeff degree =
      if degree = 0 then -(x₀ * y₀ * z₀)
      else if degree = 3 then
        -(x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁)
      else 0 := by
  have hexpand :
      -(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁) =
        -Polynomial.C (x₀ * y₀ * z₀) -
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 3 -
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 6 -
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 9 := by
    ring
  rw [hexpand]
  interval_cases degree <;> simp

theorem cancellationFactor_coeff_five
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    (-(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁)).coeff 5 = 0 := by
  have hexpand :
      -(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁) =
        -Polynomial.C (x₀ * y₀ * z₀) -
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 3 -
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 6 -
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 9 := by
    ring
  rw [hexpand]
  simp

theorem cornerFactor_coeff_lt_five
    (q : ℕ) (x₀ x₁ y₀ y₁ z₀ z₁ : K) {degree : ℕ} (hdegree : degree < 5) :
    ((1 - Polynomial.C (q : K) * Polynomial.X) *
        (Polynomial.C x₀ + Polynomial.X ^ 5 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 5 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 5 * Polynomial.C z₁)).coeff degree =
      if degree = 0 then x₀ * y₀ * z₀
      else if degree = 1 then -((q : K) * x₀ * y₀ * z₀)
      else 0 := by
  have hexpand :
      (1 - Polynomial.C (q : K) * Polynomial.X) *
          (Polynomial.C x₀ + Polynomial.X ^ 5 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 5 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 5 * Polynomial.C z₁) =
        Polynomial.C (x₀ * y₀ * z₀) -
        Polynomial.C ((q : K) * x₀ * y₀ * z₀) * Polynomial.X +
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 5 -
        Polynomial.C ((q : K) *
          (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁)) * Polynomial.X ^ 6 +
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 10 -
        Polynomial.C ((q : K) *
          (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁)) * Polynomial.X ^ 11 +
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 15 -
        Polynomial.C ((q : K) * x₁ * y₁ * z₁) * Polynomial.X ^ 16 := by
    ring
  rw [hexpand]
  interval_cases degree <;> simp

theorem cornerFactor_coeff_five
    (q : ℕ) (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    ((1 - Polynomial.C (q : K) * Polynomial.X) *
        (Polynomial.C x₀ + Polynomial.X ^ 5 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 5 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 5 * Polynomial.C z₁)).coeff 5 =
      x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁ := by
  have hexpand :
      (1 - Polynomial.C (q : K) * Polynomial.X) *
          (Polynomial.C x₀ + Polynomial.X ^ 5 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 5 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 5 * Polynomial.C z₁) =
        Polynomial.C (x₀ * y₀ * z₀) -
        Polynomial.C ((q : K) * x₀ * y₀ * z₀) * Polynomial.X +
        Polynomial.C (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁) *
          Polynomial.X ^ 5 -
        Polynomial.C ((q : K) *
          (x₁ * y₀ * z₀ + x₀ * y₁ * z₀ + x₀ * y₀ * z₁)) * Polynomial.X ^ 6 +
        Polynomial.C (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁) *
          Polynomial.X ^ 10 -
        Polynomial.C ((q : K) *
          (x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁)) * Polynomial.X ^ 11 +
        Polynomial.C (x₁ * y₁ * z₁) * Polynomial.X ^ 15 -
        Polynomial.C ((q : K) * x₁ * y₁ * z₁) * Polynomial.X ^ 16 := by
    ring
  rw [hexpand]
  simp

end CoordinateTensor
end AlgebraicComplexity
