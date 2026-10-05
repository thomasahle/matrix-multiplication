import MatrixMultiplication.FeasibilitySlack
import MatrixMultiplication.LogBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Final certificate arithmetic

This file kernel-checks the last implication in Section 6.4.  The retained-exponent and matrix-size
lower bounds are deliberately truncated to six decimal places, well below both the archived and
freshly reproduced outputs.  The logarithmic rank budget is not assumed: it is proved in
`LogBounds.lean`.

The final theorem exposes the two genuine external obligations:

1. the reconstructed certificate quantities really satisfy the displayed lower bounds; and
2. the cited combination-loss feasibility theorem applies to the repeated-orientation program.

No theorem in this file claims that those obligations have already been formalized.
-/

namespace MatrixMultiplication.FinalCertificate

open MatrixMultiplication.LogBounds

noncomputable section

/-- Exact target `237071 / 100000`. -/
def omegaTarget : ℝ := 237071 / 100000

/-- Conservative truncation of the paper's `8.195519329847103`. -/
def retainedExponentLower : ℝ := 8.195519

/-- Conservative truncation of the paper's `6.016495483291198`. -/
def matrixSizeLower : ℝ := 6.016495

/-- Conservative floor for the freshly reproduced deterministic-series retained exponent. -/
def retainedSeriesFloor : ℝ := 8.195642

/-- Conservative floor for the freshly reproduced deterministic-series matrix size. -/
def matrixSeriesFloor : ℝ := 6.016541

/-- The paper's rounded-up per-unit entropy continuity allowance. -/
def entropyContinuityUpper : ℝ := 0.000003210

/-- The separate allowance for series arithmetic, linear terms, and endpoint conversion. -/
def extraArithmeticReserve : ℝ := 0.000020

def retainedErrorReserve : ℝ :=
  32 * entropyContinuityUpper + extraArithmeticReserve

def matrixErrorReserve : ℝ :=
  8 * entropyContinuityUpper + extraArithmeticReserve

/-- The exact rank-budget expression for `q = 5`, `ℓ⋆ = 4`. -/
def rankBudget : ℝ := 8 * (Real.log 7 / Real.log 2)

theorem omegaTarget_pos : 0 < omegaTarget := by
  norm_num [omegaTarget]

theorem matrixSizeLower_pos : 0 < matrixSizeLower := by
  norm_num [matrixSizeLower]

/-- The paper's rounded error budget still leaves the six-decimal retained-exponent floor. -/
theorem retained_floor_survives_error_budget :
    retainedExponentLower ≤ retainedSeriesFloor - retainedErrorReserve := by
  norm_num [retainedExponentLower, retainedSeriesFloor, retainedErrorReserve,
    entropyContinuityUpper, extraArithmeticReserve]

/-- The paper's rounded error budget still leaves the six-decimal matrix-size floor. -/
theorem matrix_floor_survives_error_budget :
    matrixSizeLower ≤ matrixSeriesFloor - matrixErrorReserve := by
  norm_num [matrixSizeLower, matrixSeriesFloor, matrixErrorReserve,
    entropyContinuityUpper, extraArithmeticReserve]

/-- Exact rational arithmetic at the deliberately truncated lower bounds. -/
theorem truncated_decimal_margin :
    rankBudgetUpper < retainedExponentLower + omegaTarget * matrixSizeLower := by
  norm_num [rankBudgetUpper, retainedExponentLower, omegaTarget, matrixSizeLower]

/-- The analytic rank budget lies strictly below the truncated certificate objective. -/
theorem certified_numeric_slack :
    rankBudget < retainedExponentLower + omegaTarget * matrixSizeLower := by
  exact (eight_logTwo_seven_lt_rankBudgetUpper.trans truncated_decimal_margin)

/--
Positive slack at `target`, positive matrix size, and the feasibility principle imply a strict
bound.  This justifies the paper's passage from a theorem stated with `ω ≤ Ω` to `ω < target`.

The argument is pure ordered-field arithmetic and is shared with every other endpoint module; it
lives in `MatrixMultiplication/FeasibilitySlack.lean`.  This declaration is retained under its
original name and statement as the certificate-local spelling.
-/
theorem strict_of_feasibility_with_slack
    {omega budget retained matrix target : ℝ}
    (hmatrix : 0 < matrix)
    (hslack : budget < retained + target * matrix)
    (feasibility : ∀ Ω, budget ≤ retained + Ω * matrix → omega ≤ Ω) :
    omega < target :=
  MatrixMultiplication.FeasibilitySlack.strict_of_feasibility_with_slack hmatrix hslack feasibility

/--
Conditional end-to-end statement for the supplied certificate.

`hretained` and `hmatrix` are the numerical reconstruction/error-analysis obligations.
`feasibility` is the cited tensor-degeneration/asymptotic-sum-inequality obligation, generalized to
the repeated orientation list by `RepeatedOrientation.arbitrary_orientations`.
-/
theorem omega_lt_237071_of_certificate
    {omega retained matrix : ℝ}
    (hretained : retainedExponentLower ≤ retained)
    (hmatrix : matrixSizeLower ≤ matrix)
    (feasibility : ∀ Ω, rankBudget ≤ retained + Ω * matrix → omega ≤ Ω) :
    omega < omegaTarget := by
  have hmatrixPos : 0 < matrix := matrixSizeLower_pos.trans_le hmatrix
  have hlower :
      retainedExponentLower + omegaTarget * matrixSizeLower ≤
        retained + omegaTarget * matrix := by
    have ht := omegaTarget_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hmatrix ht]
  have hslack : rankBudget < retained + omegaTarget * matrix :=
    certified_numeric_slack.trans_le hlower
  exact strict_of_feasibility_with_slack hmatrixPos hslack feasibility

/--
Version whose assumptions line up directly with the numerical workflow: lower floors for the two
series outputs, followed by one-sided error enclosures for the exact mathematical quantities.
-/
theorem omega_lt_237071_of_series_enclosure
    {omega retainedSeries matrixSeries retainedExact matrixExact : ℝ}
    (hretainedSeries : retainedSeriesFloor ≤ retainedSeries)
    (hmatrixSeries : matrixSeriesFloor ≤ matrixSeries)
    (hretainedError : retainedSeries - retainedErrorReserve ≤ retainedExact)
    (hmatrixError : matrixSeries - matrixErrorReserve ≤ matrixExact)
    (feasibility : ∀ Ω, rankBudget ≤ retainedExact + Ω * matrixExact → omega ≤ Ω) :
    omega < omegaTarget := by
  apply omega_lt_237071_of_certificate
  · exact retained_floor_survives_error_budget.trans <|
      (sub_le_sub_right hretainedSeries retainedErrorReserve).trans hretainedError
  · exact matrix_floor_survives_error_budget.trans <|
      (sub_le_sub_right hmatrixSeries matrixErrorReserve).trans hmatrixError
  · exact feasibility

theorem omegaTarget_eq_decimal : omegaTarget = 2.37071 := by
  norm_num [omegaTarget]

end

end MatrixMultiplication.FinalCertificate
