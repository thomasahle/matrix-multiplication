import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRank
import Mathlib.Tactic

set_option linter.style.header false

/-!
# An executable border-rank certificate for `CW₆`

The original Coppersmith--Winograd exponent uses `q = 6`.  This file specializes the general
polynomial curve to rational coefficients and turns it into a closed finite computation.  Lean's
kernel checks all eight cubed coordinates and the coefficients through degree five.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

/-- The eight variables of `CW₆`. -/
abbrev CW6Index := Fin 8

/-- A computable rational standard-basis coefficient. -/
def cw6Basis (i a : CW6Index) : ℚ :=
  if a = i then 1 else 0

/-- Embed a rational basis coefficient as a constant polynomial. -/
def cw6PolynomialBasis (i a : CW6Index) : Polynomial ℚ :=
  Polynomial.C (cw6Basis i a)

/-- Sum of the six middle variables. -/
def cw6PolynomialMiddleSum (a : CW6Index) : Polynomial ℚ :=
  ∑ i : Fin 6, cw6PolynomialBasis (TriTensor.cwMiddle 6 i) a

/-- One of the six middle rank-one terms in the explicit curve. -/
def cw6CurveMiddleTerm (i : Fin 6) :
    PolynomialPureTerm (K := ℚ) (I := CW6Index) (J := CW6Index) (L := CW6Index) where
  x a := Polynomial.X *
    (cw6PolynomialBasis (TriTensor.cwZero 6) a +
      Polynomial.X ^ 2 * cw6PolynomialBasis (TriTensor.cwMiddle 6 i) a)
  y b := cw6PolynomialBasis (TriTensor.cwZero 6) b +
    Polynomial.X ^ 2 * cw6PolynomialBasis (TriTensor.cwMiddle 6 i) b
  z c := cw6PolynomialBasis (TriTensor.cwZero 6) c +
    Polynomial.X ^ 2 * cw6PolynomialBasis (TriTensor.cwMiddle 6 i) c

/-- The degree-three cancellation term. -/
def cw6CurveCancellationTerm :
    PolynomialPureTerm (K := ℚ) (I := CW6Index) (J := CW6Index) (L := CW6Index) where
  x a := -(
    cw6PolynomialBasis (TriTensor.cwZero 6) a +
      Polynomial.X ^ 3 * cw6PolynomialMiddleSum a)
  y b := cw6PolynomialBasis (TriTensor.cwZero 6) b +
    Polynomial.X ^ 3 * cw6PolynomialMiddleSum b
  z c := cw6PolynomialBasis (TriTensor.cwZero 6) c +
    Polynomial.X ^ 3 * cw6PolynomialMiddleSum c

/-- The corner-producing term. -/
def cw6CurveCornerTerm :
    PolynomialPureTerm (K := ℚ) (I := CW6Index) (J := CW6Index) (L := CW6Index) where
  x a := (1 - 6 * Polynomial.X) *
    (cw6PolynomialBasis (TriTensor.cwZero 6) a +
      Polynomial.X ^ 5 * cw6PolynomialBasis (TriTensor.cwLast 6) a)
  y b := cw6PolynomialBasis (TriTensor.cwZero 6) b +
    Polynomial.X ^ 5 * cw6PolynomialBasis (TriTensor.cwLast 6) b
  z c := cw6PolynomialBasis (TriTensor.cwZero 6) c +
    Polynomial.X ^ 5 * cw6PolynomialBasis (TriTensor.cwLast 6) c

/-- The closed family of eight rank-one polynomial tensors. -/
def cw6CurveTerms :
    Fin 8 → PolynomialPureTerm (K := ℚ) (I := CW6Index) (J := CW6Index) (L := CW6Index) :=
  Fin.snoc (Fin.snoc cw6CurveMiddleTerm cw6CurveCancellationTerm) cw6CurveCornerTerm

/-- A computable realization of the eight-term curve. -/
def cw6PolynomialCurve : CoordinateTensor (Polynomial ℚ) CW6Index CW6Index CW6Index :=
  fun a b c => ∑ i : Fin 8,
    (cw6CurveTerms i).x a * (cw6CurveTerms i).y b * (cw6CurveTerms i).z c

/-- The computable curve is definitionally the realization used by the border-rank API. -/
theorem cw6PolynomialCurve_eq_realize :
    cw6PolynomialCurve = realizePolynomialFamily cw6CurveTerms := by
  rfl

/-- The coordinate tensor `CW₆`, written with the computable basis coefficients. -/
def cw6CoordinateTensor : CoordinateTensor ℚ CW6Index CW6Index CW6Index :=
  fun a b c =>
    (∑ i : Fin 6, (
      cw6Basis (TriTensor.cwZero 6) a *
          cw6Basis (TriTensor.cwMiddle 6 i) b *
          cw6Basis (TriTensor.cwMiddle 6 i) c +
        cw6Basis (TriTensor.cwMiddle 6 i) a *
          cw6Basis (TriTensor.cwZero 6) b *
          cw6Basis (TriTensor.cwMiddle 6 i) c +
        cw6Basis (TriTensor.cwMiddle 6 i) a *
          cw6Basis (TriTensor.cwMiddle 6 i) b *
          cw6Basis (TriTensor.cwZero 6) c))) +
      cw6Basis (TriTensor.cwZero 6) a * cw6Basis (TriTensor.cwZero 6) b *
        cw6Basis (TriTensor.cwLast 6) c +
      cw6Basis (TriTensor.cwZero 6) a * cw6Basis (TriTensor.cwLast 6) b *
        cw6Basis (TriTensor.cwZero 6) c +
      cw6Basis (TriTensor.cwLast 6) a * cw6Basis (TriTensor.cwZero 6) b *
        cw6Basis (TriTensor.cwZero 6) c

/-- All coefficients below degree five of the explicit eight-term curve vanish. -/
theorem cw6PolynomialCurve_vanishesBelow : VanishesBelow 5 cw6PolynomialCurve := by
  intro degree hdegree
  interval_cases degree <;> native_decide

/-- The degree-five coefficient of the curve is exactly `CW₆`. -/
theorem cw6PolynomialCurve_coeff_five :
    coeffTensor 5 cw6PolynomialCurve = cw6CoordinateTensor := by
  native_decide

/-- The explicit eight-term curve proves border rank at most eight for `CW₆`. -/
theorem cw6_borderRank_le_eight : HasBorderRankAtMost 8 cw6CoordinateTensor := by
  refine HasBorderRankAtMost.of_family cw6CurveTerms (by rfl) ?_ ?_
  · rw [← cw6PolynomialCurve_eq_realize]
    exact cw6PolynomialCurve_vanishesBelow
  · rw [← cw6PolynomialCurve_eq_realize]
    exact cw6PolynomialCurve_coeff_five

#print axioms cw6PolynomialCurve_vanishesBelow
#print axioms cw6PolynomialCurve_coeff_five
#print axioms cw6_borderRank_le_eight

end CoordinateTensor
end AlgebraicComplexity
