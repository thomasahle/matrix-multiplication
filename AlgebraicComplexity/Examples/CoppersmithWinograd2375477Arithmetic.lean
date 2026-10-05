/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants

/-!
# Exact arithmetic for the classical Coppersmith--Winograd `2.375477` bound

This lightweight client contains the directed real-arithmetic certificate for the sharp numerical
endpoint printed in Coppersmith--Winograd 1990.  The tensor, type-extraction, and value arguments
live in separate modules; this file imports only the reusable logarithm enclosure library.

The exact integral profile is a fine rational reconstruction of the paper's rounded optimizer:

```text
q = 6,  tau = 2375477 / 3000000,
(A,B,C,D) = (148446, 7976570, 65404408, 131096512),
(L,G) = (7,247),  D = [2(L+G)]^3,
N = 3A + 6B + 3C + 3D = 637807518.
```

Every logarithm is enclosed by a finite rational atanh sum.  The final comparison is exact
rational arithmetic: it uses neither floating-point evaluation nor a compiled decision shortcut.

Primary source: Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via Arithmetic
Progressions*, Journal of Symbolic Computation 9(3), 251--280 (1990), pp. 267--272,
DOI 10.1016/S0747-7171(08)80013-2.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Analysis

noncomputable section

/-! ## Directed logarithm certificates -/

/-- Lower enclosure for the first outer marginal ratio `637807518 / 81654440`. -/
theorem cw2375477_log_outer0_ge :
    (20555402758 : ℝ) / 10000000000 ≤ Real.log (637807518 / 81654440 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 2 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (155594879 / 482212639 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the second outer marginal ratio `637807518 / 278146164`. -/
theorem cw2375477_log_outer1_ge :
    (8298897945 : ℝ) / 10000000000 ≤ Real.log (637807518 / 278146164 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 3 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (13585865 / 199016641 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the third outer marginal ratio `637807518 / 261905328`. -/
theorem cw2375477_log_outer2_ge :
    (8900534467 : ℝ) / 10000000000 ≤ Real.log (637807518 / 261905328 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 4 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (6333159 / 64534343 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the fourth outer marginal ratio `637807518 / 15953140`. -/
theorem cw2375477_log_outer3_ge :
    (36883808659 : ℝ) / 10000000000 ≤ Real.log (637807518 / 15953140 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 5 4 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (63653519 / 574153999 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the fifth outer marginal ratio `637807518 / 148446`. -/
theorem cw2375477_log_outer4_ge :
    (83655705612 : ℝ) / 10000000000 ≤ Real.log (637807518 / 148446 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 12 2 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (1654039 / 69213463 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the exceptional leaf's light-letter factor `log (508/7)`. -/
theorem cw2375477_log_fiveHundredEight_sevenths_ge :
    (42845712970 : ℝ) / 10000000000 ≤ Real.log (508 / 7 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 6 3 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (15 / 239 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the exceptional leaf's heavy-letter factor `log (254/247)`. -/
theorem cw2375477_log_twoHundredFiftyFour_twoHundredFortySeven_ge :
    (279459301 : ℝ) / 10000000000 ≤ Real.log (254 / 247 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 0 2 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (7 / 501 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the ordinary constituent factor `log 12`. -/
theorem cw2375477_log_twelve_ge :
    (24849066494 : ℝ) / 10000000000 ≤ Real.log 12 := by
  apply le_log_of_powTwo_add_logRatioLower 3 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the ordinary constituent factor `log 38`. -/
theorem cw2375477_log_thirtyEight_ge :
    (36375861593 : ℝ) / 10000000000 ≤ Real.log 38 := by
  apply le_log_of_powTwo_add_logRatioLower 5 4 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (3 / 35 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Lower enclosure for the exceptional constituent factor `log 6`. -/
theorem cw2375477_log_six_ge :
    (17917594689 : ℝ) / 10000000000 ≤ Real.log 6 := by
  apply le_log_of_powTwo_add_logRatioLower 2 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-! ## Final scalar separation -/

/-- The exact enclosures separate the logarithmic rank budget from the assembled CW-square value
at `tau = 2375477 / 3000000`.

Proof sketch: upper-bound the left occurrence of `log 2` by `log_two_le_sharp`; lower-bound every
positive logarithm on the right by the ten certificates above and `log_two_ge_sharp`.  The middle
line is then a strict rational inequality.  Its exact unnormalized reserve is
`35128792131636387 / 625000000000000 > 56`, leaving substantially more room than the enclosure
errors. -/
theorem cw2375477_scalar_log_inequality :
    (637807518 : ℝ) * (6 * Real.log 2) <
      81654440 * Real.log (637807518 / 81654440 : ℝ) +
      278146164 * Real.log (637807518 / 278146164 : ℝ) +
      261905328 * Real.log (637807518 / 261905328 : ℝ) +
      15953140 * Real.log (637807518 / 15953140 : ℝ) +
      148446 * Real.log (637807518 / 148446 : ℝ) +
      262193022 * Real.log 2 +
      3612896 * Real.log (508 / 7 : ℝ) +
      127483616 * Real.log (254 / 247 : ℝ) +
      (2375477 / 3000000 : ℝ) *
        (47859420 * Real.log 12 +
          196213224 * Real.log 38 +
          775740384 * Real.log 6) := by
  calc
    (637807518 : ℝ) * (6 * Real.log 2) ≤
        637807518 * (6 * (6931471806 / 10000000000 : ℝ)) := by
      nlinarith [log_two_le_sharp]
    _ <
        81654440 * (20555402758 / 10000000000 : ℝ) +
        278146164 * (8298897945 / 10000000000 : ℝ) +
        261905328 * (8900534467 / 10000000000 : ℝ) +
        15953140 * (36883808659 / 10000000000 : ℝ) +
        148446 * (83655705612 / 10000000000 : ℝ) +
        262193022 * (6931471805 / 10000000000 : ℝ) +
        3612896 * (42845712970 / 10000000000 : ℝ) +
        127483616 * (279459301 / 10000000000 : ℝ) +
        (2375477 / 3000000 : ℝ) *
          (47859420 * (24849066494 / 10000000000 : ℝ) +
            196213224 * (36375861593 / 10000000000 : ℝ) +
            775740384 * (17917594689 / 10000000000 : ℝ)) := by
      norm_num
    _ ≤
        81654440 * Real.log (637807518 / 81654440 : ℝ) +
        278146164 * Real.log (637807518 / 278146164 : ℝ) +
        261905328 * Real.log (637807518 / 261905328 : ℝ) +
        15953140 * Real.log (637807518 / 15953140 : ℝ) +
        148446 * Real.log (637807518 / 148446 : ℝ) +
        262193022 * Real.log 2 +
        3612896 * Real.log (508 / 7 : ℝ) +
        127483616 * Real.log (254 / 247 : ℝ) +
        (2375477 / 3000000 : ℝ) *
          (47859420 * Real.log 12 +
            196213224 * Real.log 38 +
            775740384 * Real.log 6) := by
      nlinarith [log_two_ge_sharp, cw2375477_log_outer0_ge,
        cw2375477_log_outer1_ge, cw2375477_log_outer2_ge,
        cw2375477_log_outer3_ge, cw2375477_log_outer4_ge,
        cw2375477_log_fiveHundredEight_sevenths_ge,
        cw2375477_log_twoHundredFiftyFour_twoHundredFortySeven_ge,
        cw2375477_log_twelve_ge, cw2375477_log_thirtyEight_ge,
        cw2375477_log_six_ge]

end

end AlgebraicComplexity.Examples
