/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.MatrixMultiplication.LaserVolume
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A volume endpoint theorem for powers of the Coppersmith--Winograd tensor

This file is the source-specific final adapter for computer-assisted CW bounds.  A concrete
counting and repair argument should produce a `SubexponentialLaserVolumeSequence` whose copy and
rectangular-volume bases are written in base-two exponent coordinates.  The theorem below then
combines that sequence with the constructive border-rank bound
`borderRank (CW_q) ≤ q + 2` and the rectangular asymptotic sum inequality.

The power, recursion stride, retained exponent, volume exponent, and numerical endpoint are all
parameters.  In particular the same statement accepts both level-three (`power = 4`) and
level-four (`power = 8`) certificates.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Tensor

universe u

noncomputable section

/-- The constructive CW border-rank certificate controls the logarithmic border rank of every
canonical tensor power. -/
theorem log_borderRank_coppersmithWinograd_power_le
    (K : Type u) [Field K] (q power : ℕ) :
    Real.log (borderRank (Tensor.power (coppersmithWinograd K q) power)) ≤
      (power : ℝ) * Real.log (q + 2) := by
  have hborder :
      borderRank (Tensor.power (coppersmithWinograd K q) power) ≤
        (q + 2) ^ power := by
    exact borderRank_le_iff.mpr ((coppersmithWinograd_borderRankLE K q).power power)
  have hlog :
      Real.log (borderRank (Tensor.power (coppersmithWinograd K q) power)) ≤
        Real.log (((q + 2) ^ power : ℕ) : ℝ) := by
    by_cases hzero :
      borderRank (Tensor.power (coppersmithWinograd K q) power) = 0
    · rw [hzero]
      simp only [Nat.cast_zero, Real.log_zero]
      apply Real.log_nonneg
      exact_mod_cast one_le_pow₀ (by omega : 1 ≤ q + 2)
    · apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero hzero
      · exact_mod_cast hborder
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Real.log_pow] using hlog

/-- A finite CW extraction sequence with subexponential loss satisfies the volume-weighted
Schönhage inequality in base-two exponent coordinates. -/
theorem retained_add_omega_mul_volume_le_cwPowerBudget
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume))) :
    retained + omega K * volume ≤
      (power : ℝ) * Real.log (q + 2) / Real.log 2 := by
  have hrate := hextractions.hasLaserExtractionRate_bits.le_log_borderRank K
  have hsource := log_borderRank_coppersmithWinograd_power_le K q power
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlogTwo).2
  simpa only [mul_comm] using hrate.trans hsource

/-- Strict endpoint form.  It intentionally consumes an exact strict scalar margin, allowing a
generated rational/interval checker to remain separate from the tensor semantics. -/
theorem omega_lt_of_cwPower_volumeSequence
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume target : ℝ}
    (hvolume : 0 < volume)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retained + target * volume) :
    omega K < target := by
  have hbudget := retained_add_omega_mul_volume_le_cwPowerBudget
    K q power hextractions
  nlinarith

/-- A one-sided certificate interface: lower bounds for retained exponent and mean-volume
exponent suffice whenever their rational endpoint already has positive source-budget slack. -/
theorem omega_lt_of_cwPower_volumeSequence_lowerBounds
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume retainedLower volumeLower target : ℝ}
    (hvolumeLower : 0 < volumeLower)
    (hretained : retainedLower ≤ retained)
    (hvolume : volumeLower ≤ volume)
    (htarget : 0 ≤ target)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retainedLower + target * volumeLower) :
    omega K < target := by
  apply omega_lt_of_cwPower_volumeSequence K q power
      (hvolumeLower.trans_le hvolume) hextractions
  have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume htarget
  exact hmargin.trans_le (add_le_add hretained hvolumeTerm)

end

end AlgebraicComplexity.Examples
