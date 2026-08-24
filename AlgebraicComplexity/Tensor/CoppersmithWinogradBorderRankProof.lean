import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRank

set_option linter.style.header false

/-!
# Verification lemmas for the Coppersmith--Winograd border-rank curve

The cancellation is checked coefficient-by-coefficient through degree five.  The helper lemmas below
keep constant-polynomial multiplication explicit, avoiding brittle normalization inside the
polynomial ring.
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

private theorem coeff_C3_mul_X_pow
    (a b c : K) (power degree : ℕ) :
    ((Polynomial.C a * Polynomial.C b * Polynomial.C c) * Polynomial.X ^ power).coeff degree =
      if degree = power then a * b * c else 0 := by
  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
  simpa [mul_assoc] using Polynomial.coeff_C_mul_X_pow (a * b * c) power degree

private theorem coeff_C4_mul_X_pow
    (a b c d : K) (power degree : ℕ) :
    ((Polynomial.C a * Polynomial.C b * Polynomial.C c * Polynomial.C d) *
        Polynomial.X ^ power).coeff degree =
      if degree = power then a * b * c * d else 0 := by
  rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_mul]
  simpa [mul_assoc] using Polynomial.coeff_C_mul_X_pow (a * b * c * d) power degree

/-- Split the `Fin (q+2)` curve sum into its `q`, cancellation, and corner terms. -/
theorem cwPolynomialCurve_apply (q : ℕ) (a b c : CWIndex q) :
    cwPolynomialCurve (K := K) q a b c =
      (∑ i : Fin q, (cwCurveMiddleTerm (K := K) q i).toTensor a b c) +
      (cwCurveCancellationTerm (K := K) q).toTensor a b c +
      (cwCurveCornerTerm (K := K) q).toTensor a b c := by
  unfold cwPolynomialCurve realizePolynomialFamily cwCurveTerms
  change
    (∑ x : Fin (q + 2),
      ((fun t : PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q)
          (L := CWIndex q) => t.toTensor a b c) ∘
        Fin.snoc
          (Fin.snoc (cwCurveMiddleTerm (K := K) q)
            (cwCurveCancellationTerm (K := K) q))
          (cwCurveCornerTerm (K := K) q)) x) = _
  rw [Fin.comp_snoc, Fin.sum_snoc]
  change
    (∑ x : Fin (q + 1),
      ((fun t : PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q)
          (L := CWIndex q) => t.toTensor a b c) ∘
        Fin.snoc (cwCurveMiddleTerm (K := K) q)
          (cwCurveCancellationTerm (K := K) q)) x) +
      (cwCurveCornerTerm (K := K) q).toTensor a b c = _
  rw [Fin.comp_snoc, Fin.sum_snoc]
  simpa only [Function.comp_apply]

/-- Coefficients below degree five of one middle curve term. -/
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
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 3 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 3 +
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 3 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 5 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 7 := by
    ring
  rw [hexpand]
  interval_cases degree <;>
    simp [Polynomial.coeff_add, coeff_C3_mul_X_pow] <;> ring

/-- Degree-five coefficient of one middle curve term. -/
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
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 3 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 3 +
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 3 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 5 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 7 := by
    ring
  rw [hexpand]
  simp [Polynomial.coeff_add, coeff_C3_mul_X_pow]

/-- Coefficients below degree five of the cancellation term. -/
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
        -((Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 0) -
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 3 -
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 3 -
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 3 -
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 6 -
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 6 -
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 6 -
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 9 := by
    ring
  rw [hexpand]
  interval_cases degree <;>
    simp [Polynomial.coeff_sub, Polynomial.coeff_neg, coeff_C3_mul_X_pow] <;> ring

/-- Degree-five coefficient of the cancellation term is zero. -/
theorem cancellationFactor_coeff_five
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    (-(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁)).coeff 5 = 0 := by
  have hexpand :
      -(Polynomial.C x₀ + Polynomial.X ^ 3 * Polynomial.C x₁) *
          (Polynomial.C y₀ + Polynomial.X ^ 3 * Polynomial.C y₁) *
          (Polynomial.C z₀ + Polynomial.X ^ 3 * Polynomial.C z₁) =
        -((Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 0) -
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 3 -
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 3 -
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 3 -
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 6 -
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 6 -
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 6 -
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 9 := by
    ring
  rw [hexpand]
  simp [Polynomial.coeff_sub, Polynomial.coeff_neg, coeff_C3_mul_X_pow]

/-- Coefficients below degree five of the corner term. -/
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
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 0 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) *
          Polynomial.X ^ 1 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 5 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) *
          Polynomial.X ^ 6 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) *
          Polynomial.X ^ 6 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) *
          Polynomial.X ^ 6 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 10 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 10 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 10 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) *
          Polynomial.X ^ 11 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) *
          Polynomial.X ^ 11 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) *
          Polynomial.X ^ 11 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 15 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) *
          Polynomial.X ^ 16 := by
    ring
  rw [hexpand]
  interval_cases degree <;>
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
      coeff_C3_mul_X_pow, coeff_C4_mul_X_pow] <;> ring

/-- Degree-five coefficient of the corner term. -/
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
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 0 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) *
          Polynomial.X ^ 1 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 5 +
        (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 5 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) *
          Polynomial.X ^ 6 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) *
          Polynomial.X ^ 6 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) *
          Polynomial.X ^ 6 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) * Polynomial.X ^ 10 +
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) * Polynomial.X ^ 10 +
        (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 10 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) *
          Polynomial.X ^ 11 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) *
          Polynomial.X ^ 11 -
        (Polynomial.C (q : K) * Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) *
          Polynomial.X ^ 11 +
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 15 -
        (Polynomial.C (q : K) * Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) *
          Polynomial.X ^ 16 := by
    ring
  rw [hexpand]
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
    coeff_C3_mul_X_pow, coeff_C4_mul_X_pow]

end CoordinateTensor
end AlgebraicComplexity
