import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRank

set_option linter.style.header false

namespace AlgebraicComplexity.CoordinateTensor

universe u
variable {K : Type u} [CommRing K]

private theorem coeff_three_constants_mul_X_pow
    (x y z : K) (n d : ℕ) :
    ((Polynomial.C x * Polynomial.C y * Polynomial.C z) * Polynomial.X ^ n).coeff d =
      if n = d then x * y * z else 0 := by
  rw [← map_mul, ← map_mul]
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : n = d <;> simp [h, h.symm, mul_assoc]

/-- Expansion of the middle rank-one polynomial factor used in the CW curve. -/
theorem cw_middle_polynomial_expansion (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁) =
      (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀) * Polynomial.X +
      ((Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀) +
       (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀) +
       (Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁)) * Polynomial.X ^ 3 +
      ((Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀) +
       (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁) +
       (Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁)) * Polynomial.X ^ 5 +
      (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁) * Polynomial.X ^ 7 := by
  ring

/-- The degree-five coefficient of a middle curve term. -/
theorem cw_middle_polynomial_coeff_five (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    (Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁)).coeff 5 =
      x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁ := by
  rw [cw_middle_polynomial_expansion]
  simp only [Polynomial.coeff_add]
  simp [coeff_three_constants_mul_X_pow]
  ring

end AlgebraicComplexity.CoordinateTensor
