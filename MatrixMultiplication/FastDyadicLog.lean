import MatrixMultiplication.DyadicEntropy

/-!
# Fast rational denominator bounds for dyadic logarithm certificates

`DyadicEntropy` proves logarithm soundness using the twenty-term rational enclosure of `log 2`.
Unfolding that series independently in hundreds of generated certificate terms is correct but
wasteful.  This module checks the series once against a tight fifteen-decimal rational interval,
then uses those two small rational denominators in every subsequent term.

The new endpoints are slightly wider than the canonical ones and inherit their soundness.  Their
purpose is proof engineering: generated aggregate certificates elaborate much faster while losing
less than `10⁻¹⁴` per logarithm.
-/

noncomputable section

namespace MatrixMultiplication.FastDyadicLog

open AlgebraicComplexity.Analysis
open MatrixMultiplication.DyadicEntropy

/-- Tight rational lower endpoint for `log 2`, checked once against the analytic series. -/
def fastLogTwoLower : ℝ := 693147180559945 / 1000000000000000

/-- Tight rational upper endpoint for `log 2`, checked once against the analytic series. -/
def fastLogTwoUpper : ℝ := 693147180559946 / 1000000000000000

theorem fastLogTwoLower_le_logTwoLower :
    fastLogTwoLower ≤ LogBounds.logTwoLower := by
  norm_num [fastLogTwoLower, LogBounds.logTwoLower, atanhPartial, LogBounds.seriesSteps]

theorem logTwoUpper_le_fastLogTwoUpper :
    LogBounds.logTwoUpper ≤ fastLogTwoUpper := by
  norm_num [fastLogTwoUpper, LogBounds.logTwoUpper, atanhPartial, atanhRemainder,
    LogBounds.seriesSteps]

private theorem fastLogTwoLower_pos : 0 < fastLogTwoLower := by
  norm_num [fastLogTwoLower]

private theorem logTwoUpper_pos : 0 < LogBounds.logTwoUpper := by
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    LogBounds.logTwo_le_logTwoUpper

/-- Faster lower endpoint for `log₂ numerator`. -/
def numeratorLogLower (numerator scale steps : ℕ) : ℝ :=
  scale + logRatioLower (reducedArgument numerator scale) steps / fastLogTwoUpper

/-- Faster upper endpoint for `log₂ numerator`. -/
def numeratorLogUpper (numerator scale steps : ℕ) : ℝ :=
  scale + logRatioUpper (reducedArgument numerator scale) steps / fastLogTwoLower

theorem numeratorLogLower_le_canonical
    {numerator scale steps : ℕ} (hlower : 2 ^ scale ≤ numerator) :
    numeratorLogLower numerator scale steps ≤
      DyadicEntropy.numeratorLogLower numerator scale steps := by
  have hx : 0 ≤ reducedArgument numerator scale := reducedArgument_nonneg hlower
  have hpartial : 0 ≤ logRatioLower (reducedArgument numerator scale) steps := by
    unfold logRatioLower atanhPartial
    positivity
  unfold numeratorLogLower DyadicEntropy.numeratorLogLower
  exact add_le_add (le_refl _) <|
    div_le_div_of_nonneg_left hpartial logTwoUpper_pos
      logTwoUpper_le_fastLogTwoUpper

theorem canonical_le_numeratorLogUpper
    {numerator scale steps : ℕ} (hlower : 2 ^ scale ≤ numerator) :
    DyadicEntropy.numeratorLogUpper numerator scale steps ≤
      numeratorLogUpper numerator scale steps := by
  let x := reducedArgument numerator scale
  have hx0 : 0 ≤ x := reducedArgument_nonneg hlower
  have hx1 : x < 1 := reducedArgument_lt_one hlower
  have hratioNonneg : 0 ≤ Real.log ((1 + x) / (1 - x)) := by
    have hratioOne : (1 : ℝ) ≤ (1 + x) / (1 - x) := by
      apply (le_div_iff₀ (sub_pos.mpr hx1)).2
      linarith
    exact Real.log_nonneg hratioOne
  have hupper : 0 ≤ logRatioUpper x steps :=
    hratioNonneg.trans (le_logRatioUpper hx0 hx1 steps)
  unfold numeratorLogUpper DyadicEntropy.numeratorLogUpper
  dsimp only [x] at hupper ⊢
  exact add_le_add (le_refl _) <|
    div_le_div_of_nonneg_left hupper fastLogTwoLower_pos
      fastLogTwoLower_le_logTwoLower

theorem numeratorLogLower_le
    {numerator scale steps : ℕ} (hlower : 2 ^ scale ≤ numerator) :
    numeratorLogLower numerator scale steps ≤
      Real.log (numerator : ℝ) / Real.log 2 :=
  (numeratorLogLower_le_canonical hlower).trans
    (DyadicEntropy.numeratorLogLower_le hlower)

theorem le_numeratorLogUpper
    {numerator scale steps : ℕ} (hlower : 2 ^ scale ≤ numerator) :
    Real.log (numerator : ℝ) / Real.log 2 ≤
      numeratorLogUpper numerator scale steps :=
  (DyadicEntropy.le_numeratorLogUpper hlower).trans
    (canonical_le_numeratorLogUpper hlower)

/-- Canonical-scale fast lower endpoint for a positive integer. -/
def certifiedLogIntegerLower (steps numerator : ℕ) : ℝ :=
  numeratorLogLower numerator (numeratorBinaryScale numerator) steps

/-- Canonical-scale fast upper endpoint for a positive integer. -/
def certifiedLogIntegerUpper (steps numerator : ℕ) : ℝ :=
  numeratorLogUpper numerator (numeratorBinaryScale numerator) steps

theorem certifiedLogIntegerLower_le {steps numerator : ℕ}
    (hnumerator : 0 < numerator) :
    certifiedLogIntegerLower steps numerator ≤
      Real.log (numerator : ℝ) / Real.log 2 :=
  numeratorLogLower_le (pow_numeratorBinaryScale_le hnumerator)

theorem le_certifiedLogIntegerUpper {steps numerator : ℕ}
    (hnumerator : 0 < numerator) :
    Real.log (numerator : ℝ) / Real.log 2 ≤
      certifiedLogIntegerUpper steps numerator :=
  le_numeratorLogUpper (pow_numeratorBinaryScale_le hnumerator)

end MatrixMultiplication.FastDyadicLog
