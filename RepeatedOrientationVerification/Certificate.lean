import Mathlib

set_option linter.style.header false

/-!
# Exact arithmetic and logarithm layer for the repeated-orientation certificate

This file deliberately separates two statements:

1. the numerical certificate, including a proof of the logarithm bound;
2. the tensor-theoretic combination-loss bridge from numerical feasibility to `omega`.

The numerical layer is proved in Lean. The final theorem carries the tensor bridge as an explicit
hypothesis, so the remaining mathematical gap is not hidden as an axiom.
-/

namespace RepeatedOrientationVerification

/-- Claimed exponent, exactly `2.37071`. -/
def target : ℚ := 237071 / 100000

/-- Conservatively rounded lower bound for the retained exponent. -/
def eLower : ℚ := 8195519329847103 / 1000000000000000

/-- Conservatively rounded lower bound for the matrix-size exponent. -/
def mLower : ℚ := 6016495483291198 / 1000000000000000

/-- The tighter decimal upper bound recorded in the manuscript. -/
def manuscriptUpper : ℚ := 2245883937646084 / 100000000000000

/--
A purely arithmetic upper bound for `8 * log₂ 7`, selected because Lean can prove it from the
integer inequality `7^462 < 2^1297` without relying on floating-point transcendental evaluation.
-/
def sourceUpper : ℚ := 5188 / 231

/-- Exact rational slack against the manuscript's tighter upper bound. -/
def manuscriptMargin : ℚ := eLower + target * mLower - manuscriptUpper

/-- Exact rational slack against the fully Lean-proved logarithm upper bound. -/
def leanMargin : ℚ := eLower + target * mLower - sourceUpper

/-- Lean computes the manuscript arithmetic exactly. -/
theorem manuscriptMargin_eq :
    manuscriptMargin = 2298028976950529 / 50000000000000000000 := by
  norm_num [manuscriptMargin, eLower, target, mLower, manuscriptUpper]

/-- Lean computes the slack used by the fully formal logarithm proof exactly. -/
theorem leanMargin_eq :
    leanMargin = 125642816377572199 / 11550000000000000000000 := by
  norm_num [leanMargin, eLower, target, mLower, sourceUpper]

/-- The fully formal numerical certificate has strictly positive rational slack. -/
theorem leanMargin_pos : 0 < leanMargin := by
  norm_num [leanMargin, eLower, target, mLower, sourceUpper]

/-- Exact certificate inequality over `ℚ`. -/
theorem rational_feasibility :
    sourceUpper < eLower + target * mLower := by
  norm_num [sourceUpper, eLower, target, mLower]

/-- The same exact inequality, transported to the real numbers. -/
theorem real_feasibility :
    (sourceUpper : ℝ) < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ) := by
  exact_mod_cast rational_feasibility

/-- The finite integer comparison behind the logarithm estimate. -/
theorem seven_pow_lt_two_pow : (7 : ℕ) ^ 462 < 2 ^ 1297 := by
  norm_num

/-- A rational upper approximation to `log₂ 7`, proved only from monotonicity of `log`. -/
theorem log2_seven_lt :
    Real.log 7 / Real.log 2 < (1297 : ℝ) / 462 := by
  have hpReal : (7 : ℝ) ^ 462 < (2 : ℝ) ^ 1297 := by
    exact_mod_cast seven_pow_lt_two_pow
  have hlogpow : Real.log ((7 : ℝ) ^ 462) < Real.log ((2 : ℝ) ^ 1297) :=
    Real.strictMonoOn_log (by positivity) (by positivity) hpReal
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog2]
  nlinarith

/-- The source-tensor cost appearing in the level-four feasibility condition. -/
noncomputable def sourceCost : ℝ := 8 * (Real.log 7 / Real.log 2)

/-- The source cost is below the exact rational upper bound used by this formalization. -/
theorem sourceCost_lt_sourceUpper : sourceCost < (sourceUpper : ℝ) := by
  calc
    sourceCost = 8 * (Real.log 7 / Real.log 2) := rfl
    _ < 8 * ((1297 : ℝ) / 462) :=
      mul_lt_mul_of_pos_left log2_seven_lt (by norm_num)
    _ = (sourceUpper : ℝ) := by norm_num [sourceUpper]

/-- The numerical feasibility statement after interpreting the source cost analytically. -/
def NumericallyFeasible : Prop :=
  sourceCost < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ)

/-- The complete scalar numerical inequality is proved in Lean. -/
theorem numericallyFeasible : NumericallyFeasible := by
  exact sourceCost_lt_sourceUpper.trans real_feasibility

/--
An explicit theorem schema for the final tensor-theoretic bridge. A full formal verification of
`omega ≤ 2.37071` must instantiate `combinationLossBridge`; it is not smuggled in as an axiom.
-/
theorem omega_le_target
    (omega : ℝ)
    (combinationLossBridge : NumericallyFeasible → omega ≤ (target : ℝ)) :
    omega ≤ (target : ℝ) :=
  combinationLossBridge numericallyFeasible

#print axioms manuscriptMargin_eq
#print axioms leanMargin_pos
#print axioms seven_pow_lt_two_pow
#print axioms log2_seven_lt
#print axioms sourceCost_lt_sourceUpper
#print axioms numericallyFeasible
#print axioms omega_le_target

end RepeatedOrientationVerification
