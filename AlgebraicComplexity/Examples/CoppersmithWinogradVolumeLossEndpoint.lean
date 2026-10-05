/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint
import AlgebraicComplexity.MatrixMultiplication.SubexponentialVolumeLoss

/-!
# A CW endpoint with subexponential rectangular-volume loss

Method-of-types constructions generally realize their nominal matrix volume only up to a
subexponential integral loss.  This file is the source-specific endpoint for that honest finite
interface.  It combines `SubexponentialLaserVolumeLossSequence.hasLaserExtractionRate_bits` with
the constructive border-rank bound for a power of the Coppersmith--Winograd tensor.

The numerical client chooses any strictly smaller positive mean-volume exponent.  No matrix side
length at repetition one, limiting argument, or rounded dimension is assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Tensor

universe u

noncomputable section

/-- A finite CW extraction sequence with subexponential copy and volume losses satisfies the
volume-weighted Schönhage inequality at every strictly backed-off mean-volume exponent. -/
theorem retained_add_omega_mul_lowerVolume_le_cwPowerBudget
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume lowerVolume : ℝ}
    (hextractions : SubexponentialLaserVolumeLossSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlower : lowerVolume < volume) :
    retained + omega K * lowerVolume ≤
      (power : ℝ) * Real.log (q + 2) / Real.log 2 := by
  have hrate := hextractions.hasLaserExtractionRate_bits K hlower
  have hsource := log_borderRank_coppersmithWinograd_power_le K q power
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlogTwo).2
  simpa only [mul_comm] using hrate.le_log_borderRank K |>.trans hsource

/-- Strict endpoint form for a nominal volume carrying subexponential finite loss. -/
theorem omega_lt_of_cwPower_volumeLossSequence
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume lowerVolume target : ℝ}
    (hextractions : SubexponentialLaserVolumeLossSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlowerPos : 0 < lowerVolume) (hlower : lowerVolume < volume)
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retained + target * lowerVolume) :
    omega K < target := by
  have hbudget := retained_add_omega_mul_lowerVolume_le_cwPowerBudget
    K q power hextractions hlower
  nlinarith

/-- One-sided retained-floor interface.  The semantic sequence may have a larger retained
exponent than the directed numerical floor; the backed-off volume is kept exact. -/
theorem omega_lt_of_cwPower_volumeLossSequence_retainedLower
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume lowerVolume retainedLower target : ℝ}
    (hextractions : SubexponentialLaserVolumeLossSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlowerPos : 0 < lowerVolume) (hlower : lowerVolume < volume)
    (hretained : retainedLower ≤ retained)
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retainedLower + target * lowerVolume) :
    omega K < target := by
  apply omega_lt_of_cwPower_volumeLossSequence K q power hextractions hlowerPos hlower
  exact hmargin.trans_le (add_le_add hretained le_rfl)

end

end AlgebraicComplexity.Examples
