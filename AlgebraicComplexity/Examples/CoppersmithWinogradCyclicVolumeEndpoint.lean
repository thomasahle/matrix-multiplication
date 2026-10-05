/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserRateSoundness
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserVolume

set_option autoImplicit false

/-!
# The volume endpoint for a *cyclic* stage family on a CW power

This is the cyclic counterpart of `Examples/CoppersmithWinogradVolumeEndpoint.lean`.  A Mode-B
style construction does not degenerate a single power of the source: it degenerates the three
cyclic leg orientations jointly, and its exponents are naturally stated per three-orientation
unit.  The theorem below is the source-budget adapter for exactly that situation, and its point
is that **no conversion to an ordinary sequence on one unsymmetrized source is owed**.

## Why no normalization is needed

`SubexponentialCyclicLaserVolumeSequence.hasCyclicLaserExtractionRate`
(`MatrixMultiplication/CyclicLaserVolume.lean:107`) produces the rate

```text
(log copyBase + (omega/3) * log volumeBase) / (3 * stride),
```

already divided by the `3 * stride` source copies a cyclic stride consumes, and
`HasCyclicLaserExtractionRate.le_log_borderRank`
(`MatrixMultiplication/CyclicLaserRateSoundness.lean:226`) bounds that rate by the logarithmic
border rank of the **source** tensor rather than of its cyclic product: the border rank of the
cyclic power product is at most `R(T) ^ (3 * k)`, and that `3 * k` cancels the `3 * k` in the
normalization.  So the three source copies are charged once, by the committed interface.

Writing the bases in base-two exponent coordinates per three-orientation unit, that is
`copyBase = 2 ^ (stride * 3 * retained)` and `volumeBase = 2 ^ (3 * stride * 3 * volume)`, the
rate collapses to `(retained + omega * volume) * log 2`, and the CW border-rank certificate
`R(CW_q) ≤ q + 2` bounds it by `power * log (q + 2)`.  Dividing by `log 2` is the statement.
This is precisely the three-source argument of the Total-Weight manuscript's `lem:volume`
(`better_bound/paper.tex:2160-2181`); nothing here changes the construction.

## Provenance

This route replaces an earlier draft of the q20 endpoint adapter that carried an explicit source-isomorphism hypothesis this theorem shows is unnecessary.

## References

* `[coppersmith1990matrix]` --- the `CW_q` construction and its `q + 2` border-rank certificate.
* `[schonhage1981partial]` --- the asymptotic sum inequality behind cyclic laser soundness.
* `better_bound/paper.tex`, `lem:volume` (lines 2160-2181) --- the three-source accounting.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Tensor

universe u

noncomputable section

/-- **The CW power budget for an exact cyclic stage family.**

If the three cyclic orientations of `(CW_q)^{⊗power}` have a subexponential-loss extraction
sequence whose copy and volume bases are `2 ^ (stride * 3 * retained)` and
`2 ^ (3 * stride * 3 * volume)` --- that is, three times the per-source-unit exponents, as a
cyclic unit consumes three copies --- then `retained + omega K * volume ≤ power * log₂ (q + 2)`.

The factor three is not an extra hypothesis to be discharged elsewhere: it is what the committed
cyclic rate normalization already pays for.  See the module docstring for the cancellation. -/
theorem retained_add_omega_mul_volume_le_cwPowerBudget_of_cyclicSequence
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume : ℝ}
    (h : SubexponentialCyclicLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * (3 * retained)))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * (3 * volume)))) :
    retained + omega K * volume ≤
      (power : ℝ) * Real.log (q + 2) / Real.log 2 := by
  have hrate := h.hasCyclicLaserExtractionRate K
  have hstride : (stride : ℝ) ≠ 0 := by exact_mod_cast h.stride_pos.ne'
  have hbits : HasCyclicLaserExtractionRate K
      (Tensor.power (coppersmithWinograd K q) power)
      ((retained + omega K * volume) * Real.log 2) := by
    convert hrate using 1
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    field_simp [hstride]
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  exact (hbits.le_log_borderRank K).trans
    (log_borderRank_coppersmithWinograd_power_le K q power)

end

end AlgebraicComplexity.Examples
