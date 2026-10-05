/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeLossEndpoint
import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeLoss

/-!
# A CW endpoint from eventual whole-constituent stages

This is the source-aware endpoint for an integral cleanup quotient that becomes positive only
after a finite cutoff.  The finite-prefix issue is discharged by the tail-native laser interface;
the tensor source budget is the existing constructive border-rank certificate for a power of the
Coppersmith--Winograd tensor.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Tensor

universe u

noncomputable section

/-- Eventual whole-constituent CW stages satisfy the volume-weighted Schönhage inequality at every
strictly backed-off mean-volume exponent. -/
theorem retained_add_omega_mul_lowerVolume_le_cwPowerBudget_of_eventualStages
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume lowerVolume : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlower : lowerVolume < volume) :
    retained + omega K * lowerVolume ≤
      (power : ℝ) * Real.log (q + 2) / Real.log 2 := by
  have hrate := data.hasLaserExtractionRate_bits K hlower
  have hsource := log_borderRank_coppersmithWinograd_power_le K q power
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlogTwo).2
  simpa only [mul_comm] using hrate.le_log_borderRank K |>.trans hsource

/-- Strict exponent endpoint with a one-sided retained floor and no finite-prefix stage premise. -/
theorem omega_lt_of_cwPower_eventualWholeConstituentVolumeLoss
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume lowerVolume retainedLower target : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlowerPos : 0 < lowerVolume) (hlower : lowerVolume < volume)
    (hretained : retainedLower ≤ retained)
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retainedLower + target * lowerVolume) :
    omega K < target := by
  have hbudget :=
    retained_add_omega_mul_lowerVolume_le_cwPowerBudget_of_eventualStages
      K q power data hlower
  nlinarith

end

end AlgebraicComplexity.Examples
