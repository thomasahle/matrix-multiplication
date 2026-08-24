import Mathlib

set_option linter.style.header false

/-!
# Exact arithmetic and logarithm layer for the repeated-orientation certificate

This file proves the scalar arithmetic in Lean. It also states, as explicit hypotheses, the two
remaining interfaces needed for a complete formalization:

* reconstruction of the certified retained exponent and matrix-size lower bounds from the binary
  certificate; and
* the tensor-theoretic combination-loss bridge from feasibility to the matrix multiplication
  exponent.

Neither interface is hidden as an axiom.
-/

namespace RepeatedOrientationVerification

/-- The rounded headline appearing in the manuscript, exactly `2.37071`. -/
def paperTarget : ℚ := 237071 / 100000

/-- A slightly stronger rational endpoint used by the Lean arithmetic, exactly `2.370709`. -/
def target : ℚ := 2370709 / 1000000

/-- Values printed by the external interval checker. -/
def reportedELower : ℚ := 8195519329847103 / 1000000000000000
def reportedMLower : ℚ := 6016495483291198 / 1000000000000000

/--
Slightly truncated lower bounds used by Lean. The extra truncation makes their direction visibly
conservative without relying on decimal-to-binary conversion conventions.
-/
def eLower : ℚ := 8195519329847 / 1000000000000
def mLower : ℚ := 6016495483291 / 1000000000000

/-- The tighter decimal upper bound recorded in the manuscript. -/
def manuscriptUpper : ℚ := 2245883937646084 / 100000000000000

/--
A purely arithmetic upper bound for `8 * log₂ 7`, selected because Lean can prove it from the
integer inequality `7^462 < 2^1297` without relying on floating-point transcendental evaluation.
-/
def sourceUpper : ℚ := 5188 / 231

/-- Exact rational slack at the rounded manuscript target and its tighter external log bound. -/
def manuscriptMargin : ℚ := eLower + paperTarget * mLower - manuscriptUpper

/-- Exact rational slack at the stronger Lean target and the Lean-proved logarithm upper bound. -/
def leanMargin : ℚ := eLower + target * mLower - sourceUpper

/-- The actual Lean endpoint is strictly smaller than the rounded manuscript headline. -/
theorem target_lt_paperTarget : target < paperTarget := by
  norm_num [target, paperTarget]

/-- The Lean bounds are conservative truncations of the externally reported endpoints. -/
theorem eLower_lt_reported : eLower < reportedELower := by
  norm_num [eLower, reportedELower]

theorem mLower_lt_reported : mLower < reportedMLower := by
  norm_num [mLower, reportedMLower]

/-- Lean computes the manuscript-style arithmetic exactly. -/
theorem manuscriptMargin_eq :
    manuscriptMargin = 4596057896661 / 100000000000000000 := by
  norm_num [manuscriptMargin, eLower, paperTarget, mLower, manuscriptUpper]

/-- Lean computes the slack used by the fully formal logarithm proof exactly. -/
theorem leanMargin_eq :
    leanMargin = 1123045738686689 / 231000000000000000000 := by
  norm_num [leanMargin, eLower, target, mLower, sourceUpper]

/-- The fully formal scalar inequality has strictly positive rational slack. -/
theorem leanMargin_pos : 0 < leanMargin := by
  norm_num [leanMargin, eLower, target, mLower, sourceUpper]

/-- Exact certificate-endpoint inequality over `ℚ`. -/
theorem rational_feasibility :
    sourceUpper < eLower + target * mLower := by
  norm_num [sourceUpper, eLower, target, mLower]

/-- The same exact inequality, transported to the real numbers. -/
theorem real_feasibility :
    (sourceUpper : ℝ) < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ) := by
  exact_mod_cast rational_feasibility

/-- The finite integer comparison behind the logarithm estimate. -/
theorem seven_pow_lt_two_pow : (7 : ℕ) ^ 462 < 2 ^ 1297 := by
  set_option maxRecDepth 100000 in
  set_option exponentiation.threshold 2000 in
    decide

/-- A rational upper approximation to `log₂ 7`, proved only from monotonicity of `log`. -/
theorem log2_seven_lt :
    Real.log 7 / Real.log 2 < (1297 : ℝ) / 462 := by
  have hpReal : (7 : ℝ) ^ 462 < (2 : ℝ) ^ 1297 := by
    exact_mod_cast seven_pow_lt_two_pow
  have hlogpow : Real.log ((7 : ℝ) ^ 462) < Real.log ((2 : ℝ) ^ 1297) := by
    exact Real.log_lt_log (by positivity) hpReal
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hscaled : Real.log 7 * (462 : ℝ) < (1297 : ℝ) * Real.log 2 := by
    simpa [mul_comm] using hlogpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog2]
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 462)]
  exact hscaled

/-- The source-tensor cost appearing in the level-four feasibility condition. -/
noncomputable def sourceCost : ℝ := 8 * (Real.log 7 / Real.log 2)

/-- The source cost is below the exact rational upper bound used by this formalization. -/
theorem sourceCost_lt_sourceUpper : sourceCost < (sourceUpper : ℝ) := by
  calc
    sourceCost = 8 * (Real.log 7 / Real.log 2) := rfl
    _ < 8 * ((1297 : ℝ) / 462) :=
      mul_lt_mul_of_pos_left log2_seven_lt (by norm_num)
    _ = (sourceUpper : ℝ) := by norm_num [sourceUpper]

/-- The scalar inequality for the conservative endpoint constants. -/
def NumericallyFeasible : Prop :=
  sourceCost < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ)

/-- The complete scalar endpoint inequality is proved in Lean. -/
theorem numericallyFeasible : NumericallyFeasible := by
  exact sourceCost_lt_sourceUpper.trans real_feasibility

/--
The interface that a future Lean reconstruction of the binary certificate must establish for its
actual retained exponent `E` and matrix-size exponent `M`.
-/
structure EndpointCertificate (E M : ℝ) : Prop where
  eLower_le : (eLower : ℝ) ≤ E
  mLower_le : (mLower : ℝ) ≤ M

/-- Any reconstructed endpoint satisfying the conservative bounds is numerically feasible. -/
theorem endpoint_feasible {E M : ℝ} (h : EndpointCertificate E M) :
    sourceCost < E + (target : ℝ) * M := by
  have htarget : 0 ≤ (target : ℝ) := by norm_num [target]
  calc
    sourceCost < (eLower : ℝ) + (target : ℝ) * (mLower : ℝ) := numericallyFeasible
    _ ≤ E + (target : ℝ) * M :=
      add_le_add h.eLower_le (mul_le_mul_of_nonneg_left h.mLower_le htarget)

/--
The final theorem schema keeps both remaining interfaces explicit. A complete verification must
supply `endpoint` by checking the binary certificate and `combinationLossBridge` by formalizing the
repeated-orientation combination-loss theorem.
-/
theorem omega_le_target
    (omega E M : ℝ)
    (endpoint : EndpointCertificate E M)
    (combinationLossBridge :
      sourceCost < E + (target : ℝ) * M → omega ≤ (target : ℝ)) :
    omega ≤ (target : ℝ) :=
  combinationLossBridge (endpoint_feasible endpoint)

/-- The stronger non-strict endpoint gives the manuscript's strict rounded headline. -/
theorem omega_lt_paperTarget
    (omega E M : ℝ)
    (endpoint : EndpointCertificate E M)
    (combinationLossBridge :
      sourceCost < E + (target : ℝ) * M → omega ≤ (target : ℝ)) :
    omega < (paperTarget : ℝ) := by
  have htarget : (target : ℝ) < (paperTarget : ℝ) := by
    exact_mod_cast target_lt_paperTarget
  exact (omega_le_target omega E M endpoint combinationLossBridge).trans_lt htarget

#print axioms target_lt_paperTarget
#print axioms eLower_lt_reported
#print axioms manuscriptMargin_eq
#print axioms leanMargin_pos
#print axioms seven_pow_lt_two_pow
#print axioms log2_seven_lt
#print axioms sourceCost_lt_sourceUpper
#print axioms numericallyFeasible
#print axioms endpoint_feasible
#print axioms omega_le_target
#print axioms omega_lt_paperTarget

end RepeatedOrientationVerification
