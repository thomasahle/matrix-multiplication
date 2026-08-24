import Mathlib

/-!
# Exact arithmetic layer for the repeated-orientation certificate

This file deliberately separates three statements:

1. an exact rational inequality, checked by `norm_num`;
2. the transcendental estimate `8 * log 7 / log 2 < constantUpper`;
3. the combination-loss theorem connecting feasibility to the matrix multiplication exponent.

Only (1) is pure certificate arithmetic.  Theorems using (2) or (3) carry them as explicit
hypotheses, so `#print axioms` does not hide either gap.
-/

namespace RepeatedOrientationVerification

/-- Claimed exponent, exactly `2.37071`. -/
def target : ℚ := 237071 / 100000

/-- Conservatively rounded lower bound for the retained exponent. -/
def eLower : ℚ := 8195519329847103 / 1000000000000000

/-- Conservatively rounded lower bound for the matrix-size exponent. -/
def mLower : ℚ := 6016495483291198 / 1000000000000000

/-- Conservatively rounded upper bound for `8 * log₂ 7`. -/
def constantUpper : ℚ := 2245883937646084 / 100000000000000

/-- Exact rational slack after all reserves recorded in the manuscript. -/
def margin : ℚ := eLower + target * mLower - constantUpper

/-- Lean computes the exact rational slack, with no floating-point arithmetic. -/
theorem margin_eq :
    margin = 2298028976950529 / 50000000000000000000 := by
  norm_num [margin, eLower, target, mLower, constantUpper]

/-- The rounded certificate has strictly positive exact rational slack. -/
theorem margin_pos : 0 < margin := by
  norm_num [margin, eLower, target, mLower, constantUpper]

/-- Equivalent form of the exact certificate inequality over `ℚ`. -/
theorem rational_feasibility :
    constantUpper < eLower + target * mLower := by
  norm_num [eLower, target, mLower, constantUpper]

/-- The same exact inequality, transported to the real numbers. -/
theorem real_feasibility :
    (constantUpper : ℝ) < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ) := by
  exact_mod_cast rational_feasibility

/-- The source-tensor cost appearing in the level-four feasibility condition. -/
def sourceCost : ℝ := 8 * (Real.log 7 / Real.log 2)

/-- The numerical feasibility statement after interpreting the source cost analytically. -/
def NumericallyFeasible : Prop :=
  sourceCost < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ)

/--
The exact rational layer proves numerical feasibility from a separately supplied logarithm bound.
The logarithm bound will be formalized in its own file.
-/
theorem numericallyFeasible_of_log_bound
    (hlog : sourceCost < (constantUpper : ℝ)) : NumericallyFeasible := by
  exact hlog.trans real_feasibility

/--
An explicit theorem schema for the final tensor-theoretic bridge.  A full formal verification of
`omega ≤ 2.37071` must instantiate `combinationLossBridge`; it is not smuggled in as an axiom.
-/
theorem omega_le_target
    (omega : ℝ)
    (combinationLossBridge : NumericallyFeasible → omega ≤ (target : ℝ))
    (hlog : sourceCost < (constantUpper : ℝ)) :
    omega ≤ (target : ℝ) :=
  combinationLossBridge (numericallyFeasible_of_log_bound hlog)

#print axioms margin_pos
#print axioms rational_feasibility
#print axioms real_feasibility
#print axioms numericallyFeasible_of_log_bound
#print axioms omega_le_target

end RepeatedOrientationVerification
