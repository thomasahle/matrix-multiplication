/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeLossEndpoint
import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.LogBounds

set_option autoImplicit false

/-!
# The total-weight `omega < 2.36999` endpoint with honest finite-volume loss

The total-weight method-of-types construction has nominal mean rectangular side exponent `6`, but
its finite integral dimensions may lose polynomial or other subexponential factors.  Requiring the
three final side floors already at repetition one is therefore an artificial strengthening.

This file records the endpoint in the natural interface.  A semantic construction supplies a
`SubexponentialLaserVolumeLossSequence` at nominal volume `6`; the general absorption theorem uses
the strictly smaller exponent `5.999`.  At retained floor `8.241973`, that backoff leaves the exact
positive rational margin

`17590838479 / 25000000000000 = 0.00070363353916`.

Consequently, no per-leg finite-size floor appears in the theorem below.  The only remaining input
is the actual finite extraction sequence, including its checked count and volume losses.
-/

namespace MatrixMultiplication.TotalWeightVolumeLossEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor

universe u

/-- Nominal mean rectangular side exponent of the total-weight construction. -/
noncomputable def nominalVolume : ℝ := 6

/-- Exact rational endpoint represented by the decimal `2.36999`. -/
noncomputable def acceptanceTarget : ℝ := 236999 / 100000

/-- Strict mean-volume exponent retained after absorbing the finite subexponential volume loss. -/
noncomputable def backedOffVolume : ℝ := 5999 / 1000

/-- Directed retained floor obtained by summing the four certified stage floors. -/
noncomputable def retainedFloor : ℝ :=
  MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.coarseFourFamilyFloor

theorem nominalVolume_pos : 0 < nominalVolume := by
  norm_num [nominalVolume]

theorem backedOffVolume_pos : 0 < backedOffVolume := by
  norm_num [backedOffVolume]

theorem backedOffVolume_lt_nominalVolume : backedOffVolume < nominalVolume := by
  norm_num [backedOffVolume, nominalVolume]

theorem retainedFloor_eq : retainedFloor = (8_241_973 / 1_000_000 : ℝ) :=
  MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.coarseFourFamilyFloor_eq

theorem acceptanceTarget_eq_decimal : acceptanceTarget = 2.36999 := by
  norm_num [acceptanceTarget]

/-- Exact positive margin against the directed upper enclosure for `8 log₂ 7`. -/
theorem rankBudgetUpper_lt_backedOff_endpoint :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + acceptanceTarget * backedOffVolume := by
  rw [retainedFloor_eq]
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper,
    acceptanceTarget, backedOffVolume]

/-- The exact source budget lies below the backed-off endpoint. -/
theorem sourceBudget_lt_backedOff_endpoint :
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 <
      retainedFloor + acceptanceTarget * backedOffVolume := by
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 =
        8 * (Real.log 7 / Real.log 2) := by norm_num; ring
    _ < MatrixMultiplication.LogBounds.rankBudgetUpper :=
      MatrixMultiplication.LogBounds.eight_logTwo_seven_lt_rankBudgetUpper
    _ < retainedFloor + acceptanceTarget * backedOffVolume :=
      rankBudgetUpper_lt_backedOff_endpoint

/-- **Backed-off volume milestone.**

A total-weight finite extraction sequence with the certified retained floor and nominal volume
`6`, allowing separate positive subexponential losses in copy count and integral matrix volume,
proves `omega < 2.36999`. -/
theorem omega_lt_236999_of_volumeLossSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained : ℝ}
    (hextractions : SubexponentialLaserVolumeLossSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * nominalVolume)))
    (hretained : retainedFloor ≤ retained) :
    omega K < acceptanceTarget := by
  exact omega_lt_of_cwPower_volumeLossSequence_retainedLower K 5 8
    hextractions backedOffVolume_pos backedOffVolume_lt_nominalVolume hretained
    sourceBudget_lt_backedOff_endpoint

/-- Exact-floor specialization: after semantic assembly, no numerical hypothesis remains. -/
theorem omega_lt_236999_of_volumeLossSequence_at_floor
    (K : Type u) [Field K]
    {stride : ℕ}
    (hextractions : SubexponentialLaserVolumeLossSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retainedFloor))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * nominalVolume))) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_volumeLossSequence K hextractions le_rfl

end MatrixMultiplication.TotalWeightVolumeLossEndpoint
