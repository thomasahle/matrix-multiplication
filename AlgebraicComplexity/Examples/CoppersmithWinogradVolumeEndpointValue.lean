/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint
import AlgebraicComplexity.MatrixMultiplication.LaserVolumeRegularization

/-!
# The Coppersmith--Winograd volume endpoint, re-derived through the value API

This is the regression client of the regularization theorem
(`MatrixMultiplication/LaserVolumeRegularization.lean`).  The committed endpoint adapter
`Examples/CoppersmithWinogradVolumeEndpoint.lean` reaches `omega` along the *rate* route:

```text
SubexponentialLaserVolumeSequence → HasLaserExtractionRate → le_log_borderRank → omega bound.
```

Here the same two endpoint theorems are proved again along the *value* route:

```text
SubexponentialLaserVolumeSequence → TauValueCertificate at every repetition
  → V_τ(source) ≥ 2^(retained + 3τ·volume) → Schönhage soundness → omega bound.
```

## What is being checked

The two `_value` theorems below are stated with **the same binders, the same hypotheses, and the
same conclusion** as their committed originals — not merely the same numbers.  The two `example`
declarations pin this: `@original = @value_route` typechecks by proof irrelevance exactly when the
two statements are the same proposition, so the pins fail to compile the moment either route
drifts.  Nothing weaker was possible to claim: the bridge must lose no strength at all, or the
`TotalWeight*` and `Simplified*Endpoint` families cannot be retargeted at it.

The two routes are also *independent*: the value route never mentions `HasLaserExtractionRate`,
`UniformLaserVolumeBaseExtraction`, or `asymptoticSum`; it consumes only
`SubexponentialLaserVolumeSequence.laserVolumeValue_le_asymptoticRank`, which is certificate-level
Schönhage soundness (`TauValueCertificate.term_le_asymptoticRank`).  Both routes therefore rest on
`AlgebraicComplexity.asymptoticSumInequality` and on nothing else beyond it, which is what the
focused audit `AxiomAudit/LaserVolumeRegularization.lean` asserts.

## The idiom future clients should use

`omega_lt_of_cwPower_borderRankBudget` is the shape the bridge exists to make available: a laser
endpoint is one application of `SubexponentialLaserVolumeSequence.omega_lt_of_borderRankLE_bits` to
the source's border-rank certificate and a scalar margin, with no sequence plumbing, no rate
algebra, and no solve-for-`omega` step in the client.  It differs from the committed original only
in trading the hypothesis `0 < volume` for `0 ≤ target`, both of which every numerical client has.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Tensor

universe u

noncomputable section

/-! ## The committed endpoint, re-derived through the value API -/

/-- **The budget theorem along the value route.**  Identical statement to
`retained_add_omega_mul_volume_le_cwPowerBudget`, proved without the laser rate interface.

Proof sketch: the sequence certifies the value `2^(retained + ω·volume)` at the critical exponent
`τ = ω/3` (`laserVolumeValue_bits` at `3·(ω/3) = ω`); regularized soundness bounds that value by
the asymptotic rank of the degenerated CW power, hence by its constructive border rank
`(q+2)^power`; taking logarithms and dividing by `log 2` is the numerical statement. -/
theorem retained_add_omega_mul_volume_le_cwPowerBudget_value
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume))) :
    retained + omega K * volume ≤
      (power : ℝ) * Real.log (q + 2) / Real.log 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvalue :
      laserVolumeValue stride ((2 : ℝ) ^ ((stride : ℝ) * retained))
          ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)) (omega K / 3) =
        (2 : ℝ) ^ (retained + omega K * volume) := by
    rw [laserVolumeValue_bits hextractions.stride_pos,
      show retained + 3 * (omega K / 3) * volume = retained + omega K * volume by ring]
  have hsound :
      laserVolumeValue stride ((2 : ℝ) ^ ((stride : ℝ) * retained))
          ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)) (omega K / 3) ≤
        (borderRank (Tensor.power (coppersmithWinograd K q) power) : ℝ) :=
    (hextractions.laserVolumeValue_le_asymptoticRank K).trans
      (Tensor.asymptoticRank_le_borderRank _)
  have hlog := Real.log_le_log (laserVolumeValue_pos _ _ _ _) hsound
  rw [hvalue, Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hsource := log_borderRank_coppersmithWinograd_power_le K q power
  rw [le_div_iff₀ hlogTwo]
  linarith

/-- **The strict endpoint along the value route.**  Identical statement to
`omega_lt_of_cwPower_volumeSequence`, including the scalar margin hypothesis, proved from the
value-route budget by the same one-line arithmetic step. -/
theorem omega_lt_of_cwPower_volumeSequence_value
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
  have hbudget := retained_add_omega_mul_volume_le_cwPowerBudget_value
    K q power hextractions
  nlinarith

/-! ## Regression pins: the two routes prove the same propositions -/

/-- The budget statement is unchanged by the bridge. -/
example : @retained_add_omega_mul_volume_le_cwPowerBudget =
    @retained_add_omega_mul_volume_le_cwPowerBudget_value := rfl

/-- The strict endpoint statement is unchanged by the bridge. -/
example : @omega_lt_of_cwPower_volumeSequence =
    @omega_lt_of_cwPower_volumeSequence_value := rfl

/-! ## The one-step idiom -/

/-- **The endpoint a future client should write.**  Given a finite extraction sequence in base-two
retained/mean-volume coordinates, a nonnegative target, and a scalar margin against the CW source
budget, `omega < target` in one application of the bridge.

Nothing between the sequence and `omega` is client code: `omega_lt_of_borderRankLE_bits` performs
the `τ = target/3` normalization, the regularization, Schönhage soundness, and the strict
value-to-exponent step. -/
theorem omega_lt_of_cwPower_borderRankBudget
    (K : Type u) [Field K] (q power : ℕ)
    {stride : ℕ} {retained volume target : ℝ}
    (htarget : 0 ≤ target)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K q) power) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hmargin :
      (power : ℝ) * Real.log (q + 2) / Real.log 2 <
        retained + target * volume) :
    omega K < target := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine hextractions.omega_lt_of_borderRankLE_bits K htarget
    ((coppersmithWinograd_borderRankLE K q).power power) ?_
  have hcast : ((((q + 2) ^ power : ℕ)) : ℝ) = ((q : ℝ) + 2) ^ power := by
    push_cast
    ring
  have hmargin' := (div_lt_iff₀ hlogTwo).1 hmargin
  have hstrict : Real.log (((q : ℝ) + 2) ^ power) <
      (retained + target * volume) * Real.log 2 := by
    rw [Real.log_pow]
    linarith
  calc ((((q + 2) ^ power : ℕ)) : ℝ) = ((q : ℝ) + 2) ^ power := hcast
    _ = Real.exp (Real.log (((q : ℝ) + 2) ^ power)) :=
        (Real.exp_log (by positivity)).symm
    _ < Real.exp ((retained + target * volume) * Real.log 2) :=
        Real.exp_lt_exp.mpr hstrict
    _ = (2 : ℝ) ^ (retained + target * volume) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring

end

end AlgebraicComplexity.Examples
