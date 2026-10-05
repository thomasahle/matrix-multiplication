/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Log
import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Examples.CoppersmithWinogradFirstPowerHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.PartitionedLaser
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The first-power Coppersmith--Winograd exponent calculation

This is the classical, non-recursive laser analysis of `CW₆`, whose numerical conclusion is
`ω < 2.3872`.  The finite tensor extraction, entropy estimate, asymptotic sum inequality, and
floating-point-free logarithm certificate are all proved.  The older abstract
`CWFirstPowerLaserConclusion` interface remains available for reusable conditional clients.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open AlgebraicComplexity.Analysis
open Tensor

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- Entropy in nats of the common marginal of the symmetric CW support distribution assigning
mass `b` to each of the three middle constituents and `1/3-b` to each corner constituent. -/
def cwFirstPowerEntropy (b : ℝ) : ℝ :=
  Real.negMulLog (2 / 3 - b) +
    Real.negMulLog (2 * b) +
    Real.negMulLog (1 / 3 - b)

/-- The entropy formula used in the numerical client is exactly the entropy of every marginal of
the standard symmetric six-block CW support distribution. -/
theorem cwFirstPowerEntropy_eq_marginalEntropy
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) :
    cwFirstPowerEntropy b =
      (cwSupportDistribution b hb0 hb1).marginalEntropy c := by
  exact (cwSupportDistribution_marginalEntropy b hb0 hb1 c).symm

/-- Logarithm of the first-power laser value at exponent `ρ`. -/
def cwFirstPowerLogValue (q : ℕ) (b ρ : ℝ) : ℝ :=
  cwFirstPowerEntropy b + b * ρ * Real.log q

/-- The scalar formula is exactly the generic support-laser value of the standard CW
distribution and constituent volumes. -/
theorem cwFirstPowerLogValue_eq_supportLaserLogValue
    (q : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    cwFirstPowerLogValue q b (omega K) =
      supportLaserLogValue K (cwSupportDistribution b hb0 hb1)
        (cwConstituentVolume q) := by
  rw [supportLaserLogValue, cwSupportDistribution_minimumMarginalEntropy,
    cwSupportDistribution_expectedLogVolume]
  unfold cwFirstPowerLogValue cwFirstPowerEntropy
  ring

/-- Exact conclusion of the classical first-power CW laser extraction.  A future generic hashing
theorem should prove this proposition from `AsymptoticSumInequality`; keeping it as data makes the
remaining dependency explicit in the regression client. -/
def CWFirstPowerLaserConclusion (q : ℕ) : Prop :=
  ∀ (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1 / 3),
    supportLaserLogValue K
        (cwSupportDistribution b hb0.le hb1.le)
        (cwConstituentVolume q) ≤ Real.log (q + 2)

/-- The reusable tight-support theorem implies the exact proof obligation used by the classical
first-power CW numerical client.  All tensor realization, constituent, entropy-maximization, and
border-rank steps in this bridge are constructive theorems. -/
theorem cwFirstPowerLaserConclusion_of_tightSupport (q : ℕ) (hq : 0 < q)
    (hLaser : TightSupportLaserConclusion K (cwPartitionedTensor K q)) :
    CWFirstPowerLaserConclusion K q := by
  intro b hb0 hb1
  have hvalue := hLaser cwBlockSupport_isTight
    (cwPartitionedMMCertificate K q hq)
    (cwSupportDistribution b hb0.le hb1.le)
    (cwSupportDistribution_isMaximumEntropy b hb0.le hb1.le)
  rw [cwPartitionedLaserLogValue_eq_supportLaserLogValue K q hq] at hvalue
  exact hvalue.trans (log_cwPartitionedTensor_borderRank_le K q)

/-- The rational distribution parameter used by the checked `q=6` certificate. -/
def cwFirstPowerB : ℝ := 3173 / 10000

/-- The classical rounded target `2.3872`. -/
def cwFirstPowerTarget : ℝ := 1492 / 625

theorem cwFirstPowerB_pos : 0 < cwFirstPowerB := by
  norm_num [cwFirstPowerB]

theorem cwFirstPowerB_lt_one_third : cwFirstPowerB < 1 / 3 := by
  norm_num [cwFirstPowerB]

private theorem negMulLog_eq_mul_log_inv {x : ℝ} (_hx : 0 < x) :
    Real.negMulLog x = x * Real.log x⁻¹ := by
  rw [Real.negMulLog_eq_neg, Real.log_inv]
  ring

/-- Number of rational atanh terms used in the classical CW certificate. -/
private def cwLogSteps : ℕ := 20

private def cwLogALower : ℝ :=
  logRatioLower (4519 / 25481) cwLogSteps

private def cwLogBLower : ℝ :=
  logRatioLower (1827 / 8173) cwLogSteps

private def cwLogCUpper : ℝ :=
  logRatioUpper (49 / 3799) cwLogSteps

private def cwLogThreeHalvesLower : ℝ :=
  logRatioLower (1 / 5) cwLogSteps

private theorem cwLogA_lower : cwLogALower ≤ Real.log (15000 / 10481 : ℝ) := by
  have h := logRatioLower_le (x := (4519 / 25481 : ℝ))
    (by norm_num) (by norm_num) cwLogSteps
  convert h using 1 <;> norm_num [cwLogALower]

private theorem cwLogB_lower : cwLogBLower ≤ Real.log (5000 / 3173 : ℝ) := by
  have h := logRatioLower_le (x := (1827 / 8173 : ℝ))
    (by norm_num) (by norm_num) cwLogSteps
  convert h using 1 <;> norm_num [cwLogBLower]

private theorem cwLogC_upper : Real.log (1924 / 1875 : ℝ) ≤ cwLogCUpper := by
  have h := le_logRatioUpper (x := (49 / 3799 : ℝ))
    (by norm_num) (by norm_num) cwLogSteps
  convert h using 1 <;> norm_num [cwLogCUpper]

private theorem cwLogThreeHalves_lower :
    cwLogThreeHalvesLower ≤ Real.log (3 / 2 : ℝ) := by
  have h := logRatioLower_le (x := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) cwLogSteps
  convert h using 1
  all_goals norm_num [cwLogThreeHalvesLower]

private theorem log_p0_inv_lower :
    (693147 / 1000000 : ℝ) + cwLogALower ≤ Real.log ((10481 / 30000 : ℝ)⁻¹) := by
  calc
    (693147 / 1000000 : ℝ) + cwLogALower ≤
        Real.log 2 + Real.log (15000 / 10481 : ℝ) :=
      add_le_add Analysis.log_two_ge cwLogA_lower
    _ = Real.log (2 * (15000 / 10481 : ℝ)) := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    _ = Real.log ((10481 / 30000 : ℝ)⁻¹) := by norm_num

private theorem log_p1_inv_lower :
    cwLogBLower ≤ Real.log ((19038 / 30000 : ℝ)⁻¹) := by
  convert cwLogB_lower using 1
  all_goals norm_num

private theorem log_p2_inv_lower :
    6 * (693147 / 1000000 : ℝ) - cwLogCUpper ≤
      Real.log ((481 / 30000 : ℝ)⁻¹) := by
  have hmain :
      6 * (693147 / 1000000 : ℝ) - cwLogCUpper ≤
        6 * Real.log 2 - Real.log (1924 / 1875 : ℝ) := by
    linarith [Analysis.log_two_ge, cwLogC_upper]
  apply hmain.trans_eq
  calc
    6 * Real.log 2 - Real.log (1924 / 1875 : ℝ) =
        Real.log ((2 : ℝ) ^ 6) - Real.log (1924 / 1875 : ℝ) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log (((2 : ℝ) ^ 6) / (1924 / 1875 : ℝ)) := by
      exact (Real.log_div (by positivity) (by norm_num)).symm
    _ = Real.log ((481 / 30000 : ℝ)⁻¹) := by norm_num

private theorem log_six_lower :
    cwLogThreeHalvesLower + 2 * (693147 / 1000000 : ℝ) ≤ Real.log 6 := by
  calc
    cwLogThreeHalvesLower + 2 * (693147 / 1000000 : ℝ) ≤
        Real.log (3 / 2 : ℝ) + 2 * Real.log 2 := by
      linarith [cwLogThreeHalves_lower, Analysis.log_two_ge]
    _ = Real.log (3 / 2 : ℝ) + Real.log ((2 : ℝ) ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log ((3 / 2 : ℝ) * (2 : ℝ) ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    _ = Real.log 6 := by norm_num

private theorem log_eight_upper : Real.log 8 ≤ 3 * (693148 / 1000000 : ℝ) := by
  calc
    Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
    _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 3 * (693148 / 1000000 : ℝ) := by linarith [Analysis.log_two_le]

/-- The entire floating-point-free numerical core: twenty rational atanh terms for the three
non-dyadic logarithms, together with the named eight-digit enclosures `Analysis.log_two_ge` and
`Analysis.log_two_le` of `log 2`, leave a positive margin at `2.3872`.  The margin against the
exact values is `5.70·10⁻⁶`; the two rounded `log 2` endpoints spend `2.81·10⁻⁶` of it and leave
`2.89·10⁻⁶`. -/
private theorem cw_rational_separation :
    3 * (693148 / 1000000 : ℝ) <
      (10481 / 30000 : ℝ) * ((693147 / 1000000 : ℝ) + cwLogALower) +
      (19038 / 30000 : ℝ) * cwLogBLower +
      (481 / 30000 : ℝ) * (6 * (693147 / 1000000 : ℝ) - cwLogCUpper) +
      cwFirstPowerB * cwFirstPowerTarget *
        (cwLogThreeHalvesLower + 2 * (693147 / 1000000 : ℝ)) := by
  norm_num [cwLogALower, cwLogBLower,
    cwLogCUpper, cwLogThreeHalvesLower, logRatioLower, logRatioUpper,
    atanhPartial, atanhRemainder, cwLogSteps, cwFirstPowerB, cwFirstPowerTarget]

/-- Certified strict numerical inequality used by the first-power CW exponent argument. -/
theorem log_eight_lt_cwFirstPowerLogValue_target :
    Real.log 8 < cwFirstPowerLogValue 6 cwFirstPowerB cwFirstPowerTarget := by
  have hp0 : (0 : ℝ) < 10481 / 30000 := by norm_num
  have hp1 : (0 : ℝ) < 3173 / 5000 := by norm_num
  have hp2 : (0 : ℝ) < 481 / 30000 := by norm_num
  have h0log :
      (693147 / 1000000 : ℝ) + cwLogALower ≤ Real.log (30000 / 10481 : ℝ) := by
    convert log_p0_inv_lower using 1
    all_goals norm_num
  have h1log : cwLogBLower ≤ Real.log (5000 / 3173 : ℝ) := by
    convert log_p1_inv_lower using 1
    all_goals norm_num
  have h2log :
      6 * (693147 / 1000000 : ℝ) - cwLogCUpper ≤ Real.log (30000 / 481 : ℝ) := by
    convert log_p2_inv_lower using 1
    all_goals norm_num
  have h0 := mul_le_mul_of_nonneg_left h0log hp0.le
  have h1 := mul_le_mul_of_nonneg_left h1log hp1.le
  have h2 := mul_le_mul_of_nonneg_left h2log hp2.le
  have hcoef : 0 ≤ cwFirstPowerB * cwFirstPowerTarget :=
    mul_nonneg cwFirstPowerB_pos.le (by norm_num [cwFirstPowerTarget])
  have h6 :
      cwFirstPowerB * cwFirstPowerTarget *
          (cwLogThreeHalvesLower + 2 * (693147 / 1000000 : ℝ)) ≤
        cwFirstPowerB * cwFirstPowerTarget * Real.log 6 :=
    mul_le_mul_of_nonneg_left log_six_lower hcoef
  rw [cwFirstPowerLogValue, cwFirstPowerEntropy]
  norm_num [cwFirstPowerB]
  rw [negMulLog_eq_mul_log_inv hp0,
    negMulLog_eq_mul_log_inv hp1,
    negMulLog_eq_mul_log_inv hp2]
  norm_num [cwFirstPowerB] at h6 ⊢
  have hsep := cw_rational_separation
  norm_num [cwFirstPowerB] at hsep
  nlinarith [log_eight_upper, hsep]

/-- The proved finite six-constituent extraction gives the first-power laser inequality at the
rational distribution used by the numerical certificate. -/
theorem cwFirstPowerLogValue_omega_le_log_eight :
    cwFirstPowerLogValue 6 cwFirstPowerB (omega K) ≤ Real.log 8 := by
  have hbase := cwFirstPower_base_inequality K 6 (by norm_num)
  have hbase' :
      WordType.ternaryEntropyBase 10481 19038 481 *
          (((6 : ℝ) ^ omega K) ^ 9519) ≤ (8 : ℝ) ^ 30000 := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hbase
  have hentropy :
      Real.log (WordType.ternaryEntropyBase 10481 19038 481) =
        30000 * cwFirstPowerEntropy cwFirstPowerB := by
    rw [WordType.log_ternaryEntropyBase 10481 19038 481
      (by norm_num) (by norm_num) (by norm_num)]
    norm_num [cwFirstPowerEntropy, cwFirstPowerB]
  have hlog := Real.log_le_log (by
    unfold WordType.ternaryEntropyBase
    positivity) hbase'
  have hleft :
      Real.log (WordType.ternaryEntropyBase 10481 19038 481 *
          (((6 : ℝ) ^ omega K) ^ 9519)) =
        30000 * cwFirstPowerLogValue 6 cwFirstPowerB (omega K) := by
    rw [Real.log_mul (by
      unfold WordType.ternaryEntropyBase
      positivity) (by positivity), hentropy, Real.log_pow,
      Real.log_rpow (by norm_num : (0 : ℝ) < 6)]
    unfold cwFirstPowerLogValue cwFirstPowerB
    norm_num
    ring
  have hright : Real.log ((8 : ℝ) ^ 30000) = 30000 * Real.log 8 := by
    rw [Real.log_pow]
    norm_num
  rw [hleft, hright] at hlog
  nlinarith

/-- Conditional only on the named first-power laser-extraction theorem, the fully checked CW₆
calculation gives the historical `ω < 2.3872` bound. -/
theorem coppersmithWinograd_firstPower_omega_lt_of_laserConclusion
    (hlaser : CWFirstPowerLaserConclusion K 6) :
    omega K < cwFirstPowerTarget := by
  by_contra h
  have htarget : cwFirstPowerTarget ≤ omega K := le_of_not_gt h
  have hlogSix : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hmono :
      cwFirstPowerLogValue 6 cwFirstPowerB cwFirstPowerTarget ≤
        cwFirstPowerLogValue 6 cwFirstPowerB (omega K) := by
    unfold cwFirstPowerLogValue
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htarget cwFirstPowerB_pos.le) hlogSix.le
  have hbound := hlaser cwFirstPowerB cwFirstPowerB_pos cwFirstPowerB_lt_one_third
  rw [← cwFirstPowerLogValue_eq_supportLaserLogValue] at hbound
  norm_num at hbound
  linarith [log_eight_lt_cwFirstPowerLogValue_target]

/-- End-to-end first-power Coppersmith--Winograd theorem: over every field,
`omega < 2.3872`.  The extraction and numerical certificate have no remaining hypotheses. -/
theorem coppersmithWinograd_firstPower_omega_lt :
    omega K < cwFirstPowerTarget := by
  by_contra h
  have htarget : cwFirstPowerTarget ≤ omega K := le_of_not_gt h
  have hlogSix : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hmono :
      cwFirstPowerLogValue 6 cwFirstPowerB cwFirstPowerTarget ≤
        cwFirstPowerLogValue 6 cwFirstPowerB (omega K) := by
    unfold cwFirstPowerLogValue
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htarget cwFirstPowerB_pos.le) hlogSix.le
  linarith [log_eight_lt_cwFirstPowerLogValue_target,
    cwFirstPowerLogValue_omega_le_log_eight K]

/-- End-to-end regression theorem exposing only the reusable tight-support extraction statement as
its hypothesis. -/
theorem coppersmithWinograd_firstPower_omega_lt_of_tightSupport
    (hLaser : TightSupportLaserConclusion K (cwPartitionedTensor K 6)) :
    omega K < cwFirstPowerTarget :=
  coppersmithWinograd_firstPower_omega_lt_of_laserConclusion K
    (cwFirstPowerLaserConclusion_of_tightSupport K 6 (by norm_num) hLaser)

/-- More granular endpoint: the historical bound follows from the purely combinatorial
extraction-rate statement for the typed CW partition.  Schönhage's asymptotic sum inequality is
now supplied by the reusable library theorem. -/
theorem coppersmithWinograd_firstPower_omega_lt_of_extraction
    (hextract : TightSupportLaserExtraction K (cwPartitionedTensor K 6)) :
    omega K < cwFirstPowerTarget :=
  coppersmithWinograd_firstPower_omega_lt_of_tightSupport K
    (tightSupportLaserConclusion_of_extraction K hextract)

theorem cwFirstPowerTarget_eq_decimal : cwFirstPowerTarget = 2.3872 := by
  norm_num [cwFirstPowerTarget]

end

end AlgebraicComplexity.Examples
