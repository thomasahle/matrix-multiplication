/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic

set_option autoImplicit false

/-!
# The opposite-direction `X` atoms, and `log ᾱ_p + H(α_X) < H(α_Z)`

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean`
certifies each of the five `log` atoms of `dwz63EntropyX` from **below**
(`dwz63_atom_x0_ge` … `dwz63_atom_x4_ge`), because the only `X`-side obligation it had was
`log dwz63XRate ≤ dwz63EntropyX` — the direction that says the declared rational rate is
genuinely
achieved.  The count-side rate comparison needs the opposite direction: the ratio
`r = ᾱ_p ᾱ_X / ᾱ_Z` of `Examples/DuanWuZhouLevelTwoCountComparison.lean`'s
`dwz63_hcount_of_rate`
is below one exactly when

`dwz63LogCompat + dwz63EntropyX < dwz63EntropyZ`,

and that needs an **upper** enclosure of `H(α_X)`.  This module supplies the five missing atoms and
the strict inequality.

## The certificates

Each new atom reuses the *same* factorisation `y = 2 ^ m · (1 + x) / (1 - x)` and the same series
point `x` as its committed lower sibling — the `m` and `x` are recorded in the docstrings of
`dwz63_atom_x0_ge` … `dwz63_atom_x4_ge` — and only swaps the engine:
`Analysis/LogConstants.lean`'s `log_le_of_powTwo_add_logRatioUpper` with `log_two_le_sharp` and the
geometric tail `atanhRemainder`, in place of `le_log_of_powTwo_add_logRatioLower` with
`log_two_ge_sharp`.  Every bound is a rational closed by `norm_num` on the finite certificate; no
floating-point evaluation enters.

## The enclosure width, against the margin

Per-atom excess over the true logarithm (dominated by the `log 2 ≤ 0.6931471806` slack
`4.0055 · 10⁻¹¹` times `m`, the geometric tail being below `10⁻¹⁴` in every case):

| atom | `m` | terms | excess |
|---|---|---|---|
| `dwz63_atom_x1_le` (`12500000/5410749`)   | 1  | 6  | `4.006 · 10⁻¹¹` |
| `dwz63_atom_x2_le` (`50000000/20573597`)  | 1  | 7  | `4.006 · 10⁻¹¹` |
| `dwz63_atom_x0_le` (`100000000/12957007`) | 2  | 14 | `8.012 · 10⁻¹¹` |
| `dwz63_atom_x3_le` (`25000000/646269`)    | 5  | 7  | `2.003 · 10⁻¹⁰` |
| `dwz63_atom_x4_le` (`100000000/24731`)    | 11 | 15 | `4.406 · 10⁻¹⁰` |

Weighted by the `X` marginal (whose coordinates sum to one), the total excess carried into
`dwz63_entropyX_le_bound` is **`4.949 · 10⁻¹¹`**, against the per-symbol branch margin
`1.1205 · 10⁻⁷` — a factor of about `2264`.  The committed atoms consume far less still: the
`p`-atoms leave `6.70 · 10⁻¹²` of slack in `dwz63_logCompat_le_bound` and the `z`-atoms
`7.34 · 10⁻¹¹` in `dwz63_entropyZ_ge_bound`.  The three rational bounds are then rounded to a
`10⁻¹³` grid, costing a further `1.1 · 10⁻¹³` in total, and the surviving margin of
`dwz63_logCompat_add_entropyX_lt_entropyZ` is `1.1192 · 10⁻⁷`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `table:result-2nd`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Analysis

/-! ## The five upper enclosures of the `X` marginal's `log` atoms -/

/-- Upper enclosure for `100000000/12957007` (the `X` marginal entropy):
`m = 2`, `14` atanh terms at the series point `x = 12042993/37957007`. -/
theorem dwz63_atom_x0_le :
    Real.log (100000000 / 12957007 : ℝ) ≤
      (20435334631731661 / 10000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 2 14 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (12042993 / 37957007 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `12500000/5410749` (the `X` marginal entropy):
`m = 1`, `6` atanh terms at the series point `x = 839251/11660749`. -/
theorem dwz63_atom_x1_le :
    Real.log (12500000 / 5410749 : ℝ) ≤
      (8373411137530901 / 10000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 1 6 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (839251 / 11660749 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `50000000/20573597` (the `X` marginal entropy):
`m = 1`, `7` atanh terms at the series point `x = 4426403/45573597`. -/
theorem dwz63_atom_x2_le :
    Real.log (50000000 / 20573597 : ℝ) ≤
      (8880144507805069 / 10000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 1 7 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (4426403 / 45573597 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `25000000/646269` (the `X` marginal entropy):
`m = 5`, `7` atanh terms at the series point `x = 134981/1427519`. -/
theorem dwz63_atom_x3_le :
    Real.log (25000000 / 646269 : ℝ) ≤
      (36554152782733089 / 10000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 5 7 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (134981 / 1427519 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `100000000/24731` (the `X` marginal entropy):
`m = 11`, `15` atanh terms at the series point `x = 192777/588473`. -/
theorem dwz63_atom_x4_le :
    Real.log (100000000 / 24731 : ℝ) ≤
      (41524339739892553 / 5000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 11 15 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (192777 / 588473 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-! ## The three aggregated rational bounds -/

/-- **`H(α_X) ≤ 1.0891743501445`**, from the five upper atoms above. -/
theorem dwz63_entropyX_le_bound :
    dwz63EntropyX ≤ (2178348700289 / 2000000000000 : ℝ) := by
  simp only [dwz63EntropyX]
  linarith [dwz63_atom_x0_le, dwz63_atom_x1_le, dwz63_atom_x2_le, dwz63_atom_x3_le,
    dwz63_atom_x4_le]

/-- **`log ᾱ_p ≤ −0.009562941366`**, from the committed `p` atoms.  This is the committed
`dwz63_logCompat_le_log_compatRate` with the right-hand side taken down to a rational, which is
what a comparison against the two entropies needs. -/
theorem dwz63_logCompat_le_bound :
    dwz63LogCompat ≤ (-4781470683 / 500000000000 : ℝ) := by
  simp only [dwz63LogCompat]
  linarith [dwz63_atom_p0_le, dwz63_atom_p1_le, dwz63_atom_p2_le, dwz63_atom_p3_le,
    dwz63_atom_p4_ge, dwz63_atom_p5_ge]

/-- **`H(α_Z) ≥ 1.0796115206986`**, from the committed `z` atoms. -/
theorem dwz63_entropyZ_ge_bound :
    (5398057603493 / 5000000000000 : ℝ) ≤ dwz63EntropyZ := by
  simp only [dwz63EntropyZ]
  linarith [dwz63_atom_z0_ge, dwz63_atom_z1_ge, dwz63_atom_z2_ge, dwz63_atom_z3_ge,
    dwz63_atom_z4_ge]

/-! ## The strict inequality -/

/-- **`log ᾱ_p + H(α_X) < H(α_Z)`.**

Equivalently `ᾱ_p ᾱ_X < ᾱ_Z`: the count-side ratio `r = ᾱ_p ᾱ_X / (ᾱ_Z · hashK)` of
`dwz63_hcount_of_rate` is below one already at `hashK = 1`, with no use of the hash-loss
multiplier.  The surviving margin is `1.1192 · 10⁻⁷` per symbol. -/
theorem dwz63_logCompat_add_entropyX_lt_entropyZ :
    dwz63LogCompat + dwz63EntropyX < dwz63EntropyZ := by
  have hp := dwz63_logCompat_le_bound
  have hx := dwz63_entropyX_le_bound
  have hz := dwz63_entropyZ_ge_bound
  linarith

end AlgebraicComplexity.Examples
