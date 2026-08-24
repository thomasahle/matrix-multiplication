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
  simpa [mul_assoc] using Polynomial.coeff_C_mul_X_pow (R := K) (x * y * z) n d

example (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
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

example (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    (Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁)).coeff 5 =
      x₁ * y₁ * z₀ + x₁ * y₀ * z₁ + x₀ * y₁ * z₁ := by
  conv_lhs =>
    congr
    ring
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  simp [← map_mul, mul_assoc]

end AlgebraicComplexity.CoordinateTensor
