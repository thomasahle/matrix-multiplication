/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Examples.CoppersmithWinogradDepthOneRateBarrier
import AlgebraicComplexity.Probability.BinaryEntropy

/-!
# Directed arithmetic for the depth-one Coppersmith--Winograd rate barrier

The finite companion module proves that the old depth-one global-competitor rate is at most

`H₂(B) + P(B=true)`,

where `B` records whether a square letter contains a corner constituent.  This file performs the
small directed calculation needed at the one-type/corner budget `P(B=true) ≤ 9/152`:

`H₂(B) + P(B=true) < 433/1000`.

All transcendental comparisons are proved from rationally directed logarithm bounds.  No decimal
evaluation, generated optimizer data, or floating-point computation enters the theorem.  The
result is deliberately an obstruction theorem for the historical global-competitor split; it is
not a claimed route to the modern CW endpoint.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

/-! ## The scalar enclosure -/

/-- The binary-entropy charge at exceptional mass `9/152` is strictly below `0.433` bits after
adding the exceptional mass itself.

Proof sketch: factor `152/9 = 2⁴(19/18)`, use the named upper bound for `log(19/18)`, and bound
`log(152/143)` by the elementary inequality `log x ≤ x-1`.  After multiplication by the positive
`log 2`, the repository's directed lower bound on `log 2` leaves ample rational slack. -/
theorem cwDepthOne_binEntropy_nine_div_152_add_lt :
    Real.binEntropy ((9 : ℝ) / 152) / Real.log 2 + 9 / 152 < 433 / 1000 := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← lt_sub_iff_add_lt, div_lt_iff₀ hlogTwoPos]
  have hlogFirst :
      Real.log ((152 : ℝ) / 9) =
        4 * Real.log 2 + Real.log ((19 : ℝ) / 18) := by
    calc
      Real.log ((152 : ℝ) / 9) =
          Real.log (((2 : ℝ) ^ 4) * ((19 : ℝ) / 18)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 4) + Real.log ((19 : ℝ) / 18) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 4 * Real.log 2 + Real.log ((19 : ℝ) / 18) := by
        rw [Real.log_pow]
        norm_num
  have hlogSecond : Real.log ((152 : ℝ) / 143) ≤ 9 / 143 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (152 : ℝ) / 143)
    convert h using 1; norm_num
  have hbinaryExpansion :
      Real.binEntropy ((9 : ℝ) / 152) =
        (9 / 152 : ℝ) * Real.log (152 / 9) +
          (143 / 152 : ℝ) * Real.log (152 / 143) := by
    norm_num [Real.binEntropy]
  rw [hbinaryExpansion, hlogFirst]
  nlinarith [Analysis.log_nineteen_eighteenths_le, Analysis.log_two_ge, hlogSecond]

/-! ## The structural consequence -/

/-- If corner-containing letters have mass at most `9/152`, some tensor leg has depth-one
double-coarse rate residual strictly below `0.433`.

Proof sketch: the structural barrier chooses a leg with residual at most the Boolean event entropy
plus its mass.  Boolean entropy is `binEntropy` of the true mass; monotonicity on `[0,1/2]` moves
that mass up to `9/152`, and the preceding directed scalar enclosure finishes the proof. -/
theorem exists_leg_depthOne_rateResidual_lt_433_div_1000
    (p : ProbabilityVector CWDepthOneFineLetter)
    (hcorner : (p.pushforward cwDepthOneHasCorner).weight true ≤ (9 : ℝ) / 152) :
    ∃ c : Tensor.Leg,
      (p.pushforward
          (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
        2 * (p.pushforward cwDepthOneCoarseShape).entropyBits < 433 / 1000 := by
  let eventLaw := p.pushforward cwDepthOneHasCorner
  change eventLaw.weight true ≤ (9 : ℝ) / 152 at hcorner
  obtain ⟨c, hresidual⟩ := exists_leg_depthOne_rateResidual_le_cornerEntropy_add_mass p
  refine ⟨c, hresidual.trans_lt ?_⟩
  have hcornerNonneg : 0 ≤ eventLaw.weight true := eventLaw.nonneg true
  have hcutoffHalf : ((9 : ℝ) / 152) ≤ 2⁻¹ := by norm_num
  have hbinary :
      Real.binEntropy (eventLaw.weight true) ≤ Real.binEntropy ((9 : ℝ) / 152) :=
    Real.binEntropy_strictMonoOn.monotoneOn
      ⟨hcornerNonneg, hcorner.trans hcutoffHalf⟩
      ⟨by norm_num, hcutoffHalf⟩ hcorner
  have hentropy :
      eventLaw.entropyBits ≤ Real.binEntropy ((9 : ℝ) / 152) / Real.log 2 := by
    rw [ProbabilityVector.entropyBits_bool_eq_binEntropy_weight_true_div_log_two]
    exact div_le_div_of_nonneg_right hbinary (Real.log_pos (by norm_num)).le
  change eventLaw.entropyBits + eventLaw.weight true < 433 / 1000
  exact (add_le_add hentropy hcorner).trans_lt cwDepthOne_binEntropy_nine_div_152_add_lt

end AlgebraicComplexity.Examples
