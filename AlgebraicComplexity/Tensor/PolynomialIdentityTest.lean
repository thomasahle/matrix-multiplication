import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRank

set_option linter.style.header false

namespace AlgebraicComplexity.CoordinateTensor

universe u
variable {K : Type u} [CommRing K]

example (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
    Polynomial.X *
        (Polynomial.C x₀ + Polynomial.X ^ 2 * Polynomial.C x₁) *
        (Polynomial.C y₀ + Polynomial.X ^ 2 * Polynomial.C y₁) *
        (Polynomial.C z₀ + Polynomial.X ^ 2 * Polynomial.C z₁) =
      Polynomial.X * Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₀ +
      Polynomial.X ^ 3 *
        (Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₀ +
         Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₀ +
         Polynomial.C x₀ * Polynomial.C y₀ * Polynomial.C z₁) +
      Polynomial.X ^ 5 *
        (Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₀ +
         Polynomial.C x₁ * Polynomial.C y₀ * Polynomial.C z₁ +
         Polynomial.C x₀ * Polynomial.C y₁ * Polynomial.C z₁) +
      Polynomial.X ^ 7 * Polynomial.C x₁ * Polynomial.C y₁ * Polynomial.C z₁ := by
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
  simp [Polynomial.coeff_add]

end AlgebraicComplexity.CoordinateTensor
