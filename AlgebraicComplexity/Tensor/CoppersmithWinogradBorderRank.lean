import AlgebraicComplexity.Tensor.CoppersmithWinograd
import AlgebraicComplexity.Tensor.PolynomialDegeneration
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The `q + 2` border-rank degeneration of the Coppersmith--Winograd tensor

This file formalizes the explicit polynomial curve behind the standard border-rank upper bound
`borderRank (CW_q) ≤ q + 2`. The curve is represented by `q + 2` polynomial rank-one terms.
Its coefficients below degree five cancel, while the coefficient of degree five is `CW_q`.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable {K : Type u} [CommRing K]

/-- Coordinate index set of the big Coppersmith--Winograd tensor. -/
abbrev CWIndex (q : ℕ) := Fin (q + 2)

/-- A coefficient of a standard Coppersmith--Winograd basis variable. -/
def cwBasis (q : ℕ) (i a : CWIndex q) : K :=
  TriTensor.cwVariable (K := K) q i a

/-- The coordinate presentation of the big Coppersmith--Winograd tensor. -/
def coppersmithWinogradCoordinateTensor (K : Type u) [CommRing K] (q : ℕ) :
    CoordinateTensor K (CWIndex q) (CWIndex q) (CWIndex q) :=
  fun a b c =>
    (∑ i : Fin q,
      (cwBasis (K := K) q (TriTensor.cwZero q) a) *
          (cwBasis (K := K) q (TriTensor.cwMiddle q i) b) *
          (cwBasis (K := K) q (TriTensor.cwMiddle q i) c) +
        (cwBasis (K := K) q (TriTensor.cwMiddle q i) a) *
          (cwBasis (K := K) q (TriTensor.cwZero q) b) *
          (cwBasis (K := K) q (TriTensor.cwMiddle q i) c) +
        (cwBasis (K := K) q (TriTensor.cwMiddle q i) a) *
          (cwBasis (K := K) q (TriTensor.cwMiddle q i) b) *
          (cwBasis (K := K) q (TriTensor.cwZero q) c)) +
      (cwBasis (K := K) q (TriTensor.cwZero q) a) *
        (cwBasis (K := K) q (TriTensor.cwZero q) b) *
        (cwBasis (K := K) q (TriTensor.cwLast q) c) +
      (cwBasis (K := K) q (TriTensor.cwZero q) a) *
        (cwBasis (K := K) q (TriTensor.cwLast q) b) *
        (cwBasis (K := K) q (TriTensor.cwZero q) c) +
      (cwBasis (K := K) q (TriTensor.cwLast q) a) *
        (cwBasis (K := K) q (TriTensor.cwZero q) b) *
        (cwBasis (K := K) q (TriTensor.cwZero q) c)

/-- Embed one scalar coordinate as a constant polynomial. -/
noncomputable def cwPolynomialBasis (q : ℕ) (i a : CWIndex q) : Polynomial K :=
  Polynomial.C (cwBasis (K := K) q i a)

/-- Sum of the `q` middle standard-basis variables. -/
noncomputable def cwPolynomialMiddleSum (q : ℕ) (a : CWIndex q) : Polynomial K :=
  ∑ i : Fin q, cwPolynomialBasis (K := K) q (TriTensor.cwMiddle q i) a

/-- One of the `q` rank-one terms in the explicit degeneration curve. -/
noncomputable def cwCurveMiddleTerm (q : ℕ) (i : Fin q) :
    PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q) (L := CWIndex q) where
  x a := Polynomial.X *
    (cwPolynomialBasis (K := K) q (TriTensor.cwZero q) a +
      Polynomial.X ^ 2 * cwPolynomialBasis (K := K) q (TriTensor.cwMiddle q i) a)
  y b := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) b +
    Polynomial.X ^ 2 * cwPolynomialBasis (K := K) q (TriTensor.cwMiddle q i) b
  z c := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) c +
    Polynomial.X ^ 2 * cwPolynomialBasis (K := K) q (TriTensor.cwMiddle q i) c

/-- The cancellation term of the explicit degeneration curve. -/
noncomputable def cwCurveCancellationTerm (q : ℕ) :
    PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q) (L := CWIndex q) where
  x a := -(
    cwPolynomialBasis (K := K) q (TriTensor.cwZero q) a +
      Polynomial.X ^ 3 * cwPolynomialMiddleSum (K := K) q a)
  y b := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) b +
    Polynomial.X ^ 3 * cwPolynomialMiddleSum (K := K) q b
  z c := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) c +
    Polynomial.X ^ 3 * cwPolynomialMiddleSum (K := K) q c

/-- The final corner-producing term of the explicit degeneration curve. -/
noncomputable def cwCurveCornerTerm (q : ℕ) :
    PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q) (L := CWIndex q) where
  x a := (1 - Polynomial.C (q : K) * Polynomial.X) *
    (cwPolynomialBasis (K := K) q (TriTensor.cwZero q) a +
      Polynomial.X ^ 5 * cwPolynomialBasis (K := K) q (TriTensor.cwLast q) a)
  y b := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) b +
    Polynomial.X ^ 5 * cwPolynomialBasis (K := K) q (TriTensor.cwLast q) b
  z c := cwPolynomialBasis (K := K) q (TriTensor.cwZero q) c +
    Polynomial.X ^ 5 * cwPolynomialBasis (K := K) q (TriTensor.cwLast q) c

/-- The complete `q + 2`-element polynomial rank-one family. -/
noncomputable def cwCurveTerms (q : ℕ) :
    Fin (q + 2) →
      PolynomialPureTerm (K := K) (I := CWIndex q) (J := CWIndex q) (L := CWIndex q) :=
  Fin.snoc
    (Fin.snoc (cwCurveMiddleTerm (K := K) q) (cwCurveCancellationTerm (K := K) q))
    (cwCurveCornerTerm (K := K) q)

/-- The polynomial tensor represented by the `q + 2` curve terms. -/
noncomputable def cwPolynomialCurve (q : ℕ) :
    CoordinateTensor (Polynomial K) (CWIndex q) (CWIndex q) (CWIndex q) :=
  realizePolynomialFamily (cwCurveTerms (K := K) q)

private theorem middleFactor_expansion
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
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

private theorem cancellationFactor_expansion
    (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
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

private theorem cornerFactor_expansion
    (q : ℕ) (x₀ x₁ y₀ y₁ z₀ z₁ : K) :
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

end CoordinateTensor
end AlgebraicComplexity
