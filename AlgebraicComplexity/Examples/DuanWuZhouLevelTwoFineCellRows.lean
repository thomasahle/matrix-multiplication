/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRate

set_option autoImplicit false

/-!
# The nine off-split zero-coordinate rows: degrees, entropies and rate bridges

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63_exists_zeroFineCellWeight`
(`Examples/DuanWuZhouLevelTwoFineCellGeneral.lean`) takes two data about a cell: the leg carrying
its zero coordinate, and the coarse degree `k` shared by every letter of its split row.  This
module supplies both for **every** cell of `table:result-2nd` whose zero coordinate lies **off**
the split leg `Z`, together with the arithmetic bridge that identifies the row's entropy rate with
the published component value.

## Exactly which nine cells, and with which data

`dwz63Alpha`'s order is `(0,0,4) (0,1,3) (0,2,2) (0,3,1) (0,4,0) (1,0,3) (1,1,2) (1,2,1) (1,3,0)
(2,0,2) (2,1,1) (2,2,0) (3,0,1) (3,1,0) (4,0,0)`.  A cell is in scope exactly when `i = 0` or
`j = 0`, i.e. when a zero coordinate sits on `X` or on `Y`:

| `t` | cell | zero leg | `k` = `Z` degree | value |
|---|---|---|---|---|
| `0` | `(0,0,4)` | `X` | `4` | `dwz63LogVal004` |
| `1` | `(0,1,3)` | `X` | `3` | `dwz63LogVal013` |
| `2` | `(0,2,2)` | `X` | `2` | `dwz63LogVal022` |
| `3` | `(0,3,1)` | `X` | `1` | `dwz63LogVal013` |
| `4` | `(0,4,0)` | `X` | `0` | `dwz63LogVal004` |
| `5` | `(1,0,3)` | `Y` | `3` | `dwz63LogVal013` |
| `9` | `(2,0,2)` | `Y` | `2` | `dwz63LogVal022` |
| `12` | `(3,0,1)` | `Y` | `1` | `dwz63LogVal013` |
| `14` | `(4,0,0)` | `Y` | `0` | `dwz63LogVal004` |

The six cells not in scope are the three orbit cells `(1,1,2)`, `(1,2,1)`, `(2,1,1)`, which have no
zero coordinate at all, and `(1,3,0)`, `(2,2,0)`, `(3,1,0)`, whose only zero coordinate is on `Z`
--- the split leg itself, so `SegmentedSplitRestriction.ofLeg Leg.Z` cannot be read off a live leg
there.  Those three belong to another lane.

Only **five** of the fifteen rows are distinct among the nine: rows `5`, `9`, `12`, `14` are
literally rows `1`, `2`, `3`, `4`.  The degree facts are nevertheless stated at all nine indices so
that a client never has to know that.

## The rate bridges

`dwz63_tau_mul_rate_eq_alphaTilde_two` (`Examples/DuanWuZhouLevelTwoFineCellRate.lean`) is the
`(0,2,2)` case.  The others are cheaper:

* rows `1` and `3` are the symmetric split of a degree-`3` (resp. degree-`1`) letter, so
  `H = log 2` and `ones = mass`, and the bridge is `tau * log (2q) = tau * log 12`, matching the
  committed `dwz63LogVal013 = tau * (2 log 2 + log 3)` after `log 6 = log 2 + log 3`;
* rows `0` and `4` are concentrated on a single letter, so `H = 0` and `ones = 0`, and the bridge
  is `0 = 0` --- the committed `dwz63LogVal004` is literally `0`.

No digits are re-derived anywhere: every right-hand side is a committed `dwz63LogVal…`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3, `table:result-2nd`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

/-! ## The degree facts, one per cell in scope -/

/-- Every letter of the `(0,0,4)` split row has coarse degree `4`. -/
theorem dwz63_alphaTildeDegree_zero :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 0 p ≠ 0 →
      cwSquareBlockDegree p = 4 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(0,1,3)` split row has coarse degree `3`. -/
theorem dwz63_alphaTildeDegree_one :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 1 p ≠ 0 →
      cwSquareBlockDegree p = 3 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(0,2,2)` split row has coarse degree `2`. -/
theorem dwz63_alphaTildeDegree_two :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 2 p ≠ 0 →
      cwSquareBlockDegree p = 2 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(0,3,1)` split row has coarse degree `1`. -/
theorem dwz63_alphaTildeDegree_three :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 3 p ≠ 0 →
      cwSquareBlockDegree p = 1 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(0,4,0)` split row has coarse degree `0`. -/
theorem dwz63_alphaTildeDegree_four :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 4 p ≠ 0 →
      cwSquareBlockDegree p = 0 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(1,0,3)` split row has coarse degree `3`. -/
theorem dwz63_alphaTildeDegree_five :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 5 p ≠ 0 →
      cwSquareBlockDegree p = 3 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(2,0,2)` split row has coarse degree `2`. -/
theorem dwz63_alphaTildeDegree_nine :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 9 p ≠ 0 →
      cwSquareBlockDegree p = 2 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(3,0,1)` split row has coarse degree `1`. -/
theorem dwz63_alphaTildeDegree_twelve :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 12 p ≠ 0 →
      cwSquareBlockDegree p = 1 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-- Every letter of the `(4,0,0)` split row has coarse degree `0`. -/
theorem dwz63_alphaTildeDegree_fourteen :
    ∀ p : PositiveWord CWBlock 1, dwz63AlphaTilde 14 p ≠ 0 →
      cwSquareBlockDegree p = 0 := by
  rintro ⟨x, y⟩ h
  revert h
  cases x <;> cases y <;> decide

/-! ## The two symmetric-split rows -/

/-- The one-slice exponent of the `(0,1,3)` split row: one middle per letter. -/
theorem dwz63_middleCountSum_alphaTilde_one :
    (∑ p : PositiveWord CWBlock 1, dwz63AlphaTilde 1 p * cwWordMiddleCount 1 p) = 200000000 := by
  rw [dwz63_middleCountSum_eq]
  norm_num [
      show dwz63AlphaTilde 1 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .last) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 1 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.last, .middle) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 1 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show cwWordMiddleCount 1 ((.last, .middle) : PositiveWord CWBlock 1) = 1 from by decide,
      show cwWordMiddleCount 1 ((.middle, .last) : PositiveWord CWBlock 1) = 1 from by decide,
    ]

/-- The entropy of the `(0,1,3)` split row is `log 2`: two letters of equal mass. -/
theorem dwz63_profileEntropyNats_alphaTilde_one :
    WordType.profileEntropyNats (dwz63AlphaTilde 1) = Real.log 2 := by
  rw [dwz63_profileEntropyNats_eq (dwz63_profileMass_alphaTilde 1)]
  norm_num [
      show dwz63AlphaTilde 1 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.middle, .last) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 1 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 1 ((.last, .middle) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 1 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
    Real.negMulLog]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-- The one-slice exponent of the `(0,3,1)` split row: one middle per letter. -/
theorem dwz63_middleCountSum_alphaTilde_three :
    (∑ p : PositiveWord CWBlock 1, dwz63AlphaTilde 3 p * cwWordMiddleCount 1 p) = 200000000 := by
  rw [dwz63_middleCountSum_eq]
  norm_num [
      show dwz63AlphaTilde 3 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.zero, .middle) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 3 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .zero) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show cwWordMiddleCount 1 ((.middle, .zero) : PositiveWord CWBlock 1) = 1 from by decide,
      show cwWordMiddleCount 1 ((.zero, .middle) : PositiveWord CWBlock 1) = 1 from by decide,
    ]

/-- The entropy of the `(0,3,1)` split row is `log 2`: two letters of equal mass. -/
theorem dwz63_profileEntropyNats_alphaTilde_three :
    WordType.profileEntropyNats (dwz63AlphaTilde 3) = Real.log 2 := by
  rw [dwz63_profileEntropyNats_eq (dwz63_profileMass_alphaTilde 3)]
  norm_num [
      show dwz63AlphaTilde 3 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.zero, .middle) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 3 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .zero) : PositiveWord CWBlock 1) = 100000000 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 3 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
    Real.negMulLog]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-! ## The two single-letter rows -/

/-- The `(0,0,4)` split row has no middles. -/
theorem dwz63_middleCountSum_alphaTilde_zero :
    (∑ p : PositiveWord CWBlock 1, dwz63AlphaTilde 0 p * cwWordMiddleCount 1 p) = 0 := by
  rw [dwz63_middleCountSum_eq]
  norm_num [
      show dwz63AlphaTilde 0 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .last) : PositiveWord CWBlock 1) = 200000000 from rfl,
      show cwWordMiddleCount 1 ((.last, .last) : PositiveWord CWBlock 1) = 0 from by decide,
    ]

/-- The `(0,0,4)` split row is concentrated on one letter, so its entropy vanishes. -/
theorem dwz63_profileEntropyNats_alphaTilde_zero :
    WordType.profileEntropyNats (dwz63AlphaTilde 0) = 0 := by
  rw [dwz63_profileEntropyNats_eq (dwz63_profileMass_alphaTilde 0)]
  norm_num [
      show dwz63AlphaTilde 0 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 0 ((.last, .last) : PositiveWord CWBlock 1) = 200000000 from rfl,
    Real.negMulLog]

/-- The `(0,4,0)` split row has no middles. -/
theorem dwz63_middleCountSum_alphaTilde_four :
    (∑ p : PositiveWord CWBlock 1, dwz63AlphaTilde 4 p * cwWordMiddleCount 1 p) = 0 := by
  rw [dwz63_middleCountSum_eq]
  norm_num [
      show dwz63AlphaTilde 4 ((.zero, .zero) : PositiveWord CWBlock 1) = 200000000 from rfl,
      show dwz63AlphaTilde 4 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show cwWordMiddleCount 1 ((.zero, .zero) : PositiveWord CWBlock 1) = 0 from by decide,
    ]

/-- The `(0,4,0)` split row is concentrated on one letter, so its entropy vanishes. -/
theorem dwz63_profileEntropyNats_alphaTilde_four :
    WordType.profileEntropyNats (dwz63AlphaTilde 4) = 0 := by
  rw [dwz63_profileEntropyNats_eq (dwz63_profileMass_alphaTilde 4)]
  norm_num [
      show dwz63AlphaTilde 4 ((.zero, .zero) : PositiveWord CWBlock 1) = 200000000 from rfl,
      show dwz63AlphaTilde 4 ((.zero, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.zero, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.middle, .last) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .zero) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .middle) : PositiveWord CWBlock 1) = 0 from rfl,
      show dwz63AlphaTilde 4 ((.last, .last) : PositiveWord CWBlock 1) = 0 from rfl,
    Real.negMulLog]

/-! ## The rate bridges -/


/-- **The `(0,1,3)` rate bridge.**  `tau * (mass * log 2 + mass * log q) = mass * dwz63LogVal013`,
i.e. `tau * log (2q) = tau * log 12` per letter. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_one :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 1) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 1)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 1 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 1) : ℝ) * dwz63LogVal013 := by
  have h6 : Real.log (dwz63Q : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show ((dwz63Q : ℕ) : ℝ) = 6 by norm_num [dwz63Q],
      show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [dwz63_profileMass_alphaTilde, dwz63_profileEntropyNats_alphaTilde_one,
    dwz63_middleCountSum_alphaTilde_one, h6, dwz63LogVal013]
  push_cast
  ring

/-- **The `(0,3,1)` rate bridge.**  `tau * (mass * log 2 + mass * log q) = mass * dwz63LogVal013`,
i.e. `tau * log (2q) = tau * log 12` per letter. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_three :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 3) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 3)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 3 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 3) : ℝ) * dwz63LogVal013 := by
  have h6 : Real.log (dwz63Q : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show ((dwz63Q : ℕ) : ℝ) = 6 by norm_num [dwz63Q],
      show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [dwz63_profileMass_alphaTilde, dwz63_profileEntropyNats_alphaTilde_three,
    dwz63_middleCountSum_alphaTilde_three, h6, dwz63LogVal013]
  push_cast
  ring

/-- **The `(0,0,4)` rate bridge.**  A corner: zero entropy, no `q`-power, value `1`. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_zero :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 0) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 0)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 0 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 0) : ℝ) * dwz63LogVal004 := by
  rw [dwz63_profileEntropyNats_alphaTilde_zero, dwz63_middleCountSum_alphaTilde_zero,
    dwz63LogVal004]
  push_cast
  ring

/-- **The `(0,4,0)` rate bridge.**  A corner: zero entropy, no `q`-power, value `1`. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_four :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 4) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 4)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 4 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 4) : ℝ) * dwz63LogVal004 := by
  rw [dwz63_profileEntropyNats_alphaTilde_four, dwz63_middleCountSum_alphaTilde_four,
    dwz63LogVal004]
  push_cast
  ring

/-! ## The four repeated rows

`dwz63AlphaTilde 5 = dwz63AlphaTilde 1`, `9 = 2`, `12 = 3` and `14 = 4` hold by `rfl`, so the
mirrors need no separate arithmetic. -/

theorem dwz63AlphaTilde_one_eq_five : dwz63AlphaTilde 1 = dwz63AlphaTilde 5 := rfl
theorem dwz63AlphaTilde_three_eq_twelve : dwz63AlphaTilde 3 = dwz63AlphaTilde 12 := rfl
theorem dwz63AlphaTilde_four_eq_fourteen : dwz63AlphaTilde 4 = dwz63AlphaTilde 14 := rfl

end AlgebraicComplexity.Examples
