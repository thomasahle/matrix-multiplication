/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEventualVolumeLossEndpoint
import MatrixMultiplication.TotalWeightVolumeLossEndpoint

/-!
# The total-weight endpoint from eventual exact stages

The exact fixed-type repair quotient is guaranteed positive only after a finite cutoff.  This
module connects the tail-native semantic interface to the existing directed arithmetic endpoint;
all numerical constants and the source-rank comparison are reused verbatim.
-/

namespace MatrixMultiplication.TotalWeightEventualVolumeLossEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightVolumeLossEndpoint

universe u

/-- The robust `2.36999` endpoint from eventual whole-constituent stages and an arbitrary retained
exponent above the certified floor. -/
theorem omega_lt_236999_of_eventualStages
    (K : Type u) [Field K]
    {stride : ℕ} {retained : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * nominalVolume)))
    (hretained : retainedFloor ≤ retained) :
    omega K < acceptanceTarget := by
  exact omega_lt_of_cwPower_eventualWholeConstituentVolumeLoss K 5 8 data
    backedOffVolume_pos backedOffVolume_lt_nominalVolume hretained
    sourceBudget_lt_backedOff_endpoint

/-- Exact-floor specialization.  The only remaining argument is the eventual semantic stage
family itself. -/
theorem omega_lt_236999_of_eventualStages_at_floor
    (K : Type u) [Field K]
    {stride : ℕ}
    (data : EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retainedFloor))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * nominalVolume))) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_eventualStages K data le_rfl

end MatrixMultiplication.TotalWeightEventualVolumeLossEndpoint
