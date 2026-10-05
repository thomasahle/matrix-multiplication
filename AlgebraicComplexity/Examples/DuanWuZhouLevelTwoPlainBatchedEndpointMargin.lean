/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic

set_option autoImplicit false

/-!
# The leaf-value margin of the section 6.3 endpoint

Layer 4 (`AlgebraicComplexity/Examples/`).  `omega_lt_2374631_of_plainBatchedStageAndLeaf` asks for
`exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j`, and no positive-deficit value route can meet it:
`dwz63_logVal_eq_sum` is an equality, so the fifteen cells at their published values reproduce
`dwz63LogVal` exactly (`dwz63_regionProduct_lt_required`, image 109).  This module locates the
slack the endpoint's own proof leaves and turns it into a constant.

## Where the slack is, exactly

`dwz63LogVal` reaches `omega` through **one** channel: `dwz63TrueGlobalRate` = copy rate times
`exp dwz63LogVal`, compared against the declared rational `globalRate` of `dwz63RateData` by
`dwz63_globalRate_lt_trueGlobalRate`, whose value step is the **non-strict**
`dwz63_valRate_le_exp : dwz63ValRate ≤ exp dwz63LogVal`.  The ω bound then needs only
`64 ^ 6 = 68719476736 < globalRate ^ 6`, i.e. `64 < copyRate * valRate`.  So the whole margin is

`log (copyRate * dwz63ValRate / 64)`,

and with the committed rationals

* `dwz63XRate / dwz63HashLossMultiplier = 2.9718193736875…` (the minimum),
* `dwz63ZRate / dwz63CompatRate = 2.9718197040…`,
* `dwz63ValRate = 21.535632886771`,

that is `copyRate * dwz63ValRate = 64.00001103752811`, i.e. **`1.7246136 * 10 ^ (-7)` nats per
letter**.  (The `1.7446 * 10 ^ (-7)` quoted in three docstrings is not this number; the committed
constants give `1.72461 * 10 ^ (-7)`.)

## The constant, and why `10 ^ (-7)` rather than `10 ^ (-8)`

`dwz63LeafMargin := 10 ^ (-7)` uses a little over half the available slack and leaves the rest as
cushion.  The witness is a **second declared rational** `dwz63ValRateMargin := 21.53563`, which
must satisfy two inequalities at once:

* `64 < copyRate * dwz63ValRateMargin` --- so the ω bound still closes: `64.0000024…`;
* `dwz63ValRateMargin * exp dwz63LeafMargin ≤ dwz63ValRate` --- so the shifted value is still
  above it: `log (dwz63ValRate / dwz63ValRateMargin) = 1.340 * 10 ^ (-7) ≥ 10 ^ (-7)`.

Both are proved below, the second through `Real.add_one_le_exp` at `-dwz63LeafMargin` (giving
`exp x ≤ (1 - x)⁻¹`) and then rational arithmetic --- no floating point, and the committed
enclosure table is reused rather than re-derived: the only transcendental input is the committed
`dwz63_valRate_le_exp`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

/-- **The per-letter leaf-value margin of the section 6.3 endpoint.**  The endpoint's own numeric
step has `1.7246 * 10 ^ (-7)` nats of room; this claims `10 ^ (-7)` of it. -/
noncomputable def dwz63LeafMargin : ℝ := 1 / 10 ^ 7

/-- The declared `valRate` at the margin: a rational still above `64 / copyRate` and still below
`dwz63ValRate * exp (-dwz63LeafMargin)`. -/
noncomputable def dwz63ValRateMargin : ℝ := 2153563 / 100000

theorem dwz63LeafMargin_pos : (0 : ℝ) < dwz63LeafMargin := by
  unfold dwz63LeafMargin
  norm_num

theorem dwz63ValRateMargin_pos : (0 : ℝ) < dwz63ValRateMargin := by
  unfold dwz63ValRateMargin
  norm_num

/-- `exp x ≤ (1 - x)⁻¹` at the margin, from the committed `Real.add_one_le_exp`. -/
theorem dwz63_exp_leafMargin_le : Real.exp dwz63LeafMargin ≤ 1 / (1 - dwz63LeafMargin) := by
  have hpos : (0 : ℝ) < 1 - dwz63LeafMargin := by
    unfold dwz63LeafMargin
    norm_num
  have hlow : (1 : ℝ) - dwz63LeafMargin ≤ Real.exp (-dwz63LeafMargin) := by
    have h := Real.add_one_le_exp (-dwz63LeafMargin)
    linarith
  have hprod : Real.exp dwz63LeafMargin * Real.exp (-dwz63LeafMargin) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [le_div_iff₀ hpos]
  nlinarith [Real.exp_pos dwz63LeafMargin, hlow, hprod]

/-- **The shifted value still dominates the margin rate.**  This is the value obligation of the
endpoint variant, at `dwz63LogVal - dwz63LeafMargin` in place of `dwz63LogVal`. -/
theorem dwz63_valRateMargin_le_exp_sub :
    dwz63ValRateMargin ≤ Real.exp (dwz63LogVal - dwz63LeafMargin) := by
  have hrat : dwz63ValRateMargin * (1 / (1 - dwz63LeafMargin)) ≤ dwz63ValRate := by
    unfold dwz63ValRateMargin dwz63LeafMargin dwz63ValRate
    norm_num
  have hkey : dwz63ValRateMargin * Real.exp dwz63LeafMargin ≤ dwz63ValRate := by
    have hmono : dwz63ValRateMargin * Real.exp dwz63LeafMargin ≤
        dwz63ValRateMargin * (1 / (1 - dwz63LeafMargin)) :=
      mul_le_mul_of_nonneg_left dwz63_exp_leafMargin_le dwz63ValRateMargin_pos.le
    exact hmono.trans hrat
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  exact hkey.trans dwz63_valRate_le_exp

/-- **The rank budget still clears at the margin rate.**  `64 < copyRate * dwz63ValRateMargin`, so
the endpoint's numeric step survives the shift. -/
theorem dwz63_rankBudget_lt_marginGlobalRate_pow :
    (68719476736 : ℝ) <
      (min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate)
        * dwz63ValRateMargin) ^ 6 := by
  have hmin : min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate)
      = dwz63XRate / dwz63HashLossMultiplier := by
    refine min_eq_left ?_
    unfold dwz63XRate dwz63HashLossMultiplier dwz63ZRate dwz63CompatRate
    norm_num
  have h64 : (64 : ℝ) < min (dwz63XRate / dwz63HashLossMultiplier)
      (dwz63ZRate / dwz63CompatRate) * dwz63ValRateMargin := by
    rw [hmin]
    unfold dwz63XRate dwz63HashLossMultiplier dwz63ValRateMargin
    norm_num
  calc (68719476736 : ℝ) = 64 ^ 6 := by norm_num
    _ < _ := pow_lt_pow_left₀ h64 (by norm_num) (by norm_num)


/-! ## The assembled leaf value is exactly the variant's demand -/

/-- `exp ((n + 1) * x) ^ 6 = exp x ^ (6 * (n + 1))`: the two spellings of a per-letter rate. -/
theorem dwz63_exp_pow_six_eq (x : ℝ) (n : ℕ) :
    Real.exp (((n : ℝ) + 1) * x) ^ 6 = Real.exp x ^ (6 * (n + 1)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The fit, machine-checked.**  `dwz63_hasTauWeight_symSix_referenceLeaf` at
`ε := dwz63LeafMargin` produces exactly `exp ((n + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6`, and
that **is** `exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (n + 1))` --- the shape the margin variant's
`hleafValue` binder asks for, with equality rather than slack to spare. -/
theorem dwz63_assembledValue_eq_marginDemand (n : ℕ) :
    Real.exp (((n : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6
      = Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (n + 1)) :=
  dwz63_exp_pow_six_eq (dwz63LogVal - dwz63LeafMargin) n

end AlgebraicComplexity.Examples
