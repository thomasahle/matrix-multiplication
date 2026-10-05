/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEntropyXUpper
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalCompetitorDegree

set_option autoImplicit false

/-!
# `H(α_X) < H(α)`, at the section 6.3 table

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.3
`sec:level-2-global`, `papers/sources/2210.10173/global_value.tex:332-375`, fixes the fifteen-row
joint distribution `α` of the level-two example; `:133` names `N_α = 2^{n H(α) + o(n)}` and
`N_X = 2^{n H(α_X) + o(n)}`, so the ratio `ᾱ_α / ᾱ_X` whose positivity the count side
already knows
is `exp(H(α) - H(α_X))`.

This module proves that ratio is **strictly above one**, which is the growth fact the sharp degree
`⌊N_triple/N_X⌋ + 1` needs in order to be eventually at least `11`.

## Only three logarithms are evaluated

Entropy terms are nonnegative, so a lower bound on `H(α)` may drop any subset of the fifteen.  Four
cells suffice: `α = 20734458` (twice), `20088623` and `10366945`, whose four terms already sum
to more than `1.2098`, against the committed upper bound `H(α_X) ≤ 1.0891744`
(`dwz63_entropyX_le_bound`, `Examples/DuanWuZhouLevelTwoEntropyXUpper.lean:121`).  That is a margin
of `0.1207` per symbol, so only **three** distinct logarithms are enclosed, in the committed
rational-atom style of `dwz63_atom_z0_ge`
(`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean:264`) through
`le_log_of_powTwo_add_logRatioLower` (`Analysis/LogConstants.lean:72`).  No new decision procedure
is introduced.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo` and section
6.3 `sec:level-2-global`, `papers/sources/2210.10173/global_value.tex:132-133, 332-375`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open AlgebraicComplexity.Analysis
open scoped BigOperators

/-! ## The three logarithm atoms -/

/-- Lower enclosure for `100000000/20734458` (cells `(1,2,1)` and `(2,1,1)` of the section 6.3
table): `m = 2`, `20` atanh terms at the series point `x = 2132771/22867229`. -/
theorem dwz63_atom_alpha0_ge :
    (15733732318893591 / 10000000000000000 : ℝ) ≤ Real.log (100000000 / 20734458 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 2 20 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (2132771 / 22867229 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `100000000/20088623` (cell `(1,1,2)` of the section 6.3 table):
`m = 2`, `20` atanh terms at the series point `x = 4911377/45088623`. -/
theorem dwz63_atom_alpha1_ge :
    (8025082754767023 / 5000000000000000 : ℝ) ≤ Real.log (100000000 / 20088623 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 2 20 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (4911377 / 45088623 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `100000000/10366945` (cells `(0,2,2)` and `(2,0,2)` of the section 6.3
table): `m = 3`, `20` atanh terms at the series point `x = 426611/4573389`. -/
theorem dwz63_atom_alpha2_ge :
    (22665478067770031 / 10000000000000000 : ℝ) ≤ Real.log (100000000 / 10366945 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 3 20 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (426611 / 4573389 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-! ## One entropy term -/

/-- **An entropy term, with the logarithm oriented upward.**  `negMulLog (a/M) = (a/M) ·
log (M/a)`. -/
theorem dwz63_negMulLog_ratio (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    Real.negMulLog (a / M) = a / M * Real.log (M / a) := by
  rw [Real.negMulLog, Real.log_div ha.ne' hM.ne', Real.log_div hM.ne' ha.ne']
  ring

/-! ## The entropy lower bound, and the strict comparison -/

/-- **`H(α) ≥ 1.20985831`**, from four of the fifteen cells.

Entropy terms are nonnegative, so the sum over all fifteen cells of the section 6.3 table
(`global_value.tex:332-375`) dominates the sum over `{2, 6, 7, 10}` --- one `10366945`
cell,
the `20088623` cell and the two `20734458` cells --- and those four are
evaluated from the three atoms above.

Proof sketch: `Finset.sum_le_sum_of_subset_of_nonneg` against `Real.negMulLog_nonneg` on the eleven
dropped cells, then `dwz63_negMulLog_ratio` and `linarith` on the three enclosures. -/
theorem dwz63_entropyAlpha_ge_bound :
    (604929156217 / 500000000000 : ℝ) ≤ WordType.profileEntropyNats dwz63Alpha := by
  classical
  have hmass : ((WordType.profileMass dwz63Alpha : ℕ) : ℝ) = 100000000 := by
    rw [profileMass_dwz63Alpha]; norm_num
  have hnn : ∀ i : Fin 15,
      0 ≤ Real.negMulLog
        ((dwz63Alpha i : ℝ) / ((WordType.profileMass dwz63Alpha : ℕ) : ℝ)) := by
    intro i
    rw [hmass]
    refine Real.negMulLog_nonneg ?_ ?_
    · fin_cases i <;> norm_num [dwz63Alpha]
    · fin_cases i <;> norm_num [dwz63Alpha]
  have hsub : ({2, 6, 7, 10} : Finset (Fin 15)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ ↦ hnn i)
  refine le_trans ?_ hsum
  have h2 : ((dwz63Alpha 2 : ℝ)) = 10366945 := by
    rw [show dwz63Alpha 2 = 10366945 from rfl]
    norm_num
  have h6 : ((dwz63Alpha 6 : ℝ)) = 20088623 := by
    rw [show dwz63Alpha 6 = 20088623 from rfl]
    norm_num
  have h7 : ((dwz63Alpha 7 : ℝ)) = 20734458 := by
    rw [show dwz63Alpha 7 = 20734458 from rfl]
    norm_num
  have h10 : ((dwz63Alpha 10 : ℝ)) = 20734458 := by
    rw [show dwz63Alpha 10 = 20734458 from rfl]
    norm_num
  rw [show ({2, 6, 7, 10} : Finset (Fin 15)) = {2, 6, 7, 10} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hmass, h2, h6, h7, h10]
  rw [dwz63_negMulLog_ratio _ _ (by norm_num) (by norm_num),
    dwz63_negMulLog_ratio _ _ (by norm_num) (by norm_num),
    dwz63_negMulLog_ratio _ _ (by norm_num) (by norm_num)]
  linarith [dwz63_atom_alpha0_ge, dwz63_atom_alpha1_ge, dwz63_atom_alpha2_ge]

/-- **`1 < ᾱ_α / ᾱ_X`** (`global_value.tex:132-133`): the joint rate strictly exceeds the `X`
marginal rate, because `H(α_X) ≤ 1.0891744 < 1.2098583 ≤ H(α)`.

This is the growth fact the sharp degree `⌊N_triple/N_X⌋ + 1` needs in order to be eventually at
least `11`. -/
theorem dwz63_one_lt_plainXBase :
    1 < dwz63PlainRateAlpha / Real.exp dwz63EntropyX := by
  rw [dwz63_plainRateAlpha_eq_exp_entropyNats_dwz63Alpha]
  rw [one_lt_div (Real.exp_pos _)]
  refine Real.exp_lt_exp.mpr ?_
  linarith [dwz63_entropyX_le_bound, dwz63_entropyAlpha_ge_bound]

end AlgebraicComplexity.Examples
