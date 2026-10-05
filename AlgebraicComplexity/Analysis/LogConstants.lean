/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Log

/-!
# Named certified logarithm enclosures

`Analysis/Log.lean` provides the atanh machinery: a partial sum `atanhPartial`, a geometric
remainder bound `atanhRemainder`, and the two enclosures `logRatioLower x n ≤ log ((1+x)/(1-x))`
and `log ((1+x)/(1-x)) ≤ logRatioUpper x n` of the *ratio* form of the logarithm.

This file turns that machinery into one-line wrappers for lower and upper ratio enclosures, plus
the matching pair `le_log_of_powTwo_add_logRatioLower` and
`log_le_of_powTwo_add_logRatioUpper` for arguments factored as
`2^m * (1+x)/(1-x)`.  They combine an exact rational identification with a `norm_num` evaluation
of the certificate.  The file also collects the named rational enclosures clients share, so that
no client has to re-derive `log 2` or `log 7` for itself.

A ratio of two logarithms needs no series at all: `mul_log_lt_mul_log_of_pow_lt` turns an exact
integer comparison `x ^ A < y ^ B` into `A log x < B log y`.

Only *canonical* constants live here: `log 2`, `log 3`, `log 5`, `log 7`, `log 11`, and the
parametric machinery that certifies them.  An enclosure whose particular rational argument is a
choice made by one paper — an optimizer value, a tuned parameter, a published numeric target —
belongs with that client, even though its statement is pure analysis; such a theorem keeps the
`AlgebraicComplexity.Analysis` namespace but lives in the client's file.  See
`Examples/SchonhageSecondDesign.lean` (`three_mul_log_five_div_log_six_lt`, the `λ(5, 6) < 2.695`
of the Bini/Schönhage designs) and
`Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean` (the two block-entropy certificate
values at `q = 1` and `q = 5`).

Each enclosure records the series point `x`, the number of terms, and (where it matters) the slack
between the certificate and the true value.  All of them are closed by `norm_num` on a finite
rational expression; none of them appeals to a floating-point evaluation.

## Position in the library

Layer 2 (`AlgebraicComplexity/Analysis/`).  It imports only `Analysis/Log.lean`, and no
declaration here mentions a tensor, a matrix-multiplication construction, an exponent, or a
constant chosen by one paper.  (The client pointers above are prose only.)
-/

namespace AlgebraicComplexity.Analysis

/-! ## One-line wrappers -/

/-- **One-line certified upper enclosure.**  If `(1+x)/(1-x) = y` and the `n`-term atanh
certificate `logRatioUpper x n` is at most `c`, then `log y ≤ c`. -/
theorem log_le_of_logRatioUpper {x y c : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ)
    (hy : (1 + x) / (1 - x) = y) (hc : logRatioUpper x n ≤ c) : Real.log y ≤ c := by
  rw [← hy]
  exact (le_logRatioUpper hx₀ hx₁ n).trans hc

/-- **One-line certified lower enclosure.**  If `(1+x)/(1-x) = y` and `c` is at most the `n`-term
atanh certificate `logRatioLower x n`, then `c ≤ log y`. -/
theorem le_log_of_logRatioLower {x y c : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ)
    (hy : (1 + x) / (1 - x) = y) (hc : c ≤ logRatioLower x n) : c ≤ Real.log y := by
  rw [← hy]
  exact hc.trans (logRatioLower_le hx₀ hx₁ n)

/-- **Certified lower enclosure after extracting a power of two.**  Suppose
`y = 2^m (1+x)/(1-x)`.  A certified lower bound `logTwoLower ≤ log 2`, together with the
`steps`-term atanh lower certificate at `x`, gives the displayed lower bound for `log y`.

The theorem deliberately takes `logTwoLower` as data.  Lightweight clients may use the six-digit
`log_two_ge`, while close numerical certificates can use `log_two_ge_sharp` or a still tighter
paper-local enclosure without duplicating the logarithmic algebra. -/
theorem le_log_of_powTwo_add_logRatioLower
    (m steps : ℕ) {logTwoLower x y c : ℝ}
    (hlogTwo : logTwoLower ≤ Real.log 2)
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hy : (2 : ℝ) ^ m * ((1 + x) / (1 - x)) = y)
    (hc : c ≤ (m : ℝ) * logTwoLower + logRatioLower x steps) :
    c ≤ Real.log y := by
  have hratioPos : 0 < (1 + x) / (1 - x) := by positivity
  calc
    c ≤ (m : ℝ) * logTwoLower + logRatioLower x steps := hc
    _ ≤ (m : ℝ) * Real.log 2 + Real.log ((1 + x) / (1 - x)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg m))
        (logRatioLower_le hx₀ hx₁ steps)
    _ = Real.log y := by
      rw [← Real.log_pow]
      rw [← Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hratioPos.ne']
      rw [hy]

/-- **Certified upper enclosure after extracting a power of two.**  Suppose
`y = 2^m (1+x)/(1-x)`.  A certified upper bound `log 2 ≤ logTwoUpper`, together with the
`steps`-term atanh upper certificate at `x`, gives the displayed upper bound for `log y`.

Proof sketch: split `log y` into `m log 2` and the logarithm of the ratio.  Bound the first term
with `hlogTwo`, the second with `le_logRatioUpper`, and add the two directed inequalities. -/
theorem log_le_of_powTwo_add_logRatioUpper
    (m steps : ℕ) {logTwoUpper x y c : ℝ}
    (hlogTwo : Real.log 2 ≤ logTwoUpper)
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hy : (2 : ℝ) ^ m * ((1 + x) / (1 - x)) = y)
    (hc : (m : ℝ) * logTwoUpper + logRatioUpper x steps ≤ c) :
    Real.log y ≤ c := by
  have hratioPos : 0 < (1 + x) / (1 - x) := by positivity
  calc
    Real.log y = (m : ℝ) * Real.log 2 + Real.log ((1 + x) / (1 - x)) := by
      rw [← hy, Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hratioPos.ne',
        Real.log_pow]
    _ ≤ (m : ℝ) * logTwoUpper + logRatioUpper x steps :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg m))
        (le_logRatioUpper hx₀ hx₁ steps)
    _ ≤ c := hc

/-! ## Certificates from exact integer power comparisons

A rational bound on a *ratio* of two logarithms never needs the atanh series: `A log x < B log y`
is equivalent to `x ^ A < y ^ B`, which `norm_num` decides exactly on the integers.  The lemma
below is the whole content of that idiom, so a client only has to exhibit the power comparison and
divide.
-/

/-- **A logarithm comparison from an exact integer power comparison.**  From `x ^ A < y ^ B` with
`0 < x` one gets `A log x < B log y`.

Combined with `div_lt_iff₀`/`lt_div_iff₀` this certifies a rational bound on a ratio of
logarithms with no floating-point evaluation: the only side condition is a `norm_num` on a
comparison of two integer powers. -/
theorem mul_log_lt_mul_log_of_pow_lt {x y : ℝ} {A B : ℕ} (hx : 0 < x) (h : x ^ A < y ^ B) :
    (A : ℝ) * Real.log x < (B : ℝ) * Real.log y := by
  have hlog := Real.log_lt_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at hlog

/-! ## Named enclosures -/

/-- Certified rational lower bound `log 2 ≥ 0.693147`, from the atanh series at `x = 1/3` with
eight terms. -/
theorem log_two_ge : (693147 : ℝ) / 1000000 ≤ Real.log 2 :=
  le_log_of_logRatioLower (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 8 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log 2 ≤ 0.693148`, from the same eight-term series together
with its geometric remainder bound. -/
theorem log_two_le : Real.log 2 ≤ 693148 / 1000000 :=
  log_le_of_logRatioUpper (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 8 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- Certified rational upper bound `log 3 ≤ 1.098614`, from the atanh series at `x = 1/2` with ten
terms.  The true value is `1.09861228…` and the certificate evaluates to `1.09861350…`. -/
theorem log_three_le : Real.log 3 ≤ 1098614 / 1000000 :=
  log_le_of_logRatioUpper (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 10 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- Certified rational lower bound `log 3 ≥ 1.098611`, from the atanh series at `x = 1/2` with ten
terms.  The true value is `1.09861228…` and the ten-term partial sum is `1.09861222…`; together
with `log_three_le` this pins `log 3` to within `3·10⁻⁶`. -/
theorem log_three_ge : (1098611 : ℝ) / 1000000 ≤ Real.log 3 :=
  le_log_of_logRatioLower (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 10 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational lower bound `log (5/4) ≥ 0.223143`, from the atanh series at `x = 1/9` with
four terms. -/
theorem log_five_quarters_ge : (223143 : ℝ) / 1000000 ≤ Real.log (5 / 4) :=
  le_log_of_logRatioLower (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 4 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational lower bound `log (26/25) ≥ 0.039220`, from the atanh series at `x = 1/51`
with three terms. -/
theorem log_twentysix_twentyfifths_ge : (39220 : ℝ) / 1000000 ≤ Real.log (26 / 25) :=
  le_log_of_logRatioLower (x := (1 / 51 : ℝ)) (by norm_num) (by norm_num) 3 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational lower bound `log (1000/999) ≥ 0.001`. -/
theorem log_thousand_ratio_ge : (1 : ℝ) / 1000 ≤ Real.log (1000 / 999) :=
  le_log_of_logRatioLower (x := (1 / 1999 : ℝ)) (by norm_num) (by norm_num) 1 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational lower bound `log (10000/9997) ≥ 0.0003`. -/
theorem log_ninetynineninetyseven_ratio_ge : (3 : ℝ) / 10000 ≤ Real.log (10000 / 9997) :=
  le_log_of_logRatioLower (x := (3 / 19997 : ℝ)) (by norm_num) (by norm_num) 1 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational lower bound `log (8/7) ≥ 0.133531`, from the atanh series at `x = 1/15`
with three terms.  The true value is `0.13353139…`. -/
theorem log_eight_sevenths_ge : (133531 : ℝ) / 1000000 ≤ Real.log (8 / 7) :=
  le_log_of_logRatioLower (x := (1 / 15 : ℝ)) (by norm_num) (by norm_num) 3 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log (8/7) ≤ 0.133532`, from the same three-term atanh series
together with its geometric remainder bound. -/
theorem log_eight_sevenths_le : Real.log (8 / 7) ≤ 133532 / 1000000 :=
  log_le_of_logRatioUpper (x := (1 / 15 : ℝ)) (by norm_num) (by norm_num) 3 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- The identity `log (8/7) = 3 log 2 - log 7`, which turns the two `8/7` enclosures into
enclosures of `log 7`. -/
theorem log_eight_sevenths_eq : Real.log (8 / 7) = 3 * Real.log 2 - Real.log 7 := by
  rw [Real.log_div (by norm_num) (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

/-- Certified rational upper bound `log 7 ≤ 1.945913`, from `log 7 = 3 log 2 - log (8/7)` with
`log 2 ≤ 0.693148` and `log (8/7) ≥ 0.133531`.  The true value is `1.9459101…`. -/
theorem log_seven_le : Real.log 7 ≤ 1945913 / 1000000 := by
  have h := log_eight_sevenths_ge
  rw [log_eight_sevenths_eq] at h
  linarith [log_two_le]

/-- Certified rational lower bound `log 7 ≥ 1.945909`, from `log 7 = 3 log 2 - log (8/7)` with
`log 2 ≥ 0.693147` and `log (8/7) ≤ 0.133532`. -/
theorem log_seven_ge : (1945909 : ℝ) / 1000000 ≤ Real.log 7 := by
  have h := log_eight_sevenths_le
  rw [log_eight_sevenths_eq] at h
  linarith [log_two_ge]

/-- Certified rational upper bound `log (19/18) ≤ 0.054068`, from the atanh series at `x = 1/37`
with two terms.  The true value is `0.05406722…` and the certificate evaluates to `0.05406724…`.

This is the one enclosure needed by the base case of the uniform block-entropy exponent of
`Examples/GeneralizedCoppersmithWinogradBarrier.lean`, where the parameter `q = 1` contributes
`log (19/6) = log 3 + log (19/18)`. -/
theorem log_nineteen_eighteenths_le : Real.log (19 / 18) ≤ 54068 / 1000000 :=
  log_le_of_logRatioUpper (x := (1 / 37 : ℝ)) (by norm_num) (by norm_num) 2 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-! ## Logarithm increment bounds

Two `n`-independent consequences of the same atanh machinery, used wherever a *ratio* of two
nearby quantities has to be compared with a ratio of two others: an upper bound at the one-term
geometric certificate `n = 0` and a lower bound at the one-term partial sum `n = 1`.  Together they
turn an inequality between logarithmic increments into a polynomial inequality.
-/

/-- **A sharp upper bound for a logarithm increment.**  For `0 < B ≤ A`,

```text
log A - log B ≤ (A² - B²)/(2AB) = (A/B - B/A)/2.
```

This is the `n = 0` case of `log_le_of_logRatioUpper` at the series point `z = (A-B)/(A+B)`, where
the certificate `logRatioUpper z 0 = 2z/(1-z²)` is exactly `(A² - B²)/(2AB)`.  It is markedly
sharper than `Real.log_le_sub_one_of_pos`, which gives only `log A - log B ≤ (A-B)/B`, and it is
the bound that makes small-parameter induction steps go through: at `A/B = 1.42` it overshoots by
`2%` rather than by `20%`. -/
theorem log_sub_log_le_sq_div {A B : ℝ} (hB : 0 < B) (hAB : B ≤ A) :
    Real.log A - Real.log B ≤ (A ^ 2 - B ^ 2) / (2 * A * B) := by
  have hA : 0 < A := lt_of_lt_of_le hB hAB
  have hS : 0 < A + B := by linarith
  set z : ℝ := (A - B) / (A + B) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hS.le
  have hz1 : z < 1 := by rw [hz, div_lt_one hS]; linarith
  have h1p : 1 + z = 2 * A / (A + B) := by rw [hz]; field_simp; ring
  have h1m : 1 - z = 2 * B / (A + B) := by rw [hz]; field_simp; ring
  have hy : (1 + z) / (1 - z) = A / B := by
    rw [h1p, h1m, div_div_div_eq]
    field_simp
  have hcert : logRatioUpper z 0 ≤ (A ^ 2 - B ^ 2) / (2 * A * B) := by
    have hzz : 1 - z ^ 2 = 4 * A * B / (A + B) ^ 2 := by rw [hz]; field_simp; ring
    simp only [logRatioUpper, atanhPartial, atanhRemainder, Finset.range_zero,
      Finset.sum_empty, zero_add, pow_one, mul_zero]
    rw [hzz, hz]
    refine le_of_eq ?_
    field_simp
    ring
  have h := log_le_of_logRatioUpper hz0 hz1 0 hy hcert
  rwa [Real.log_div (ne_of_gt hA) (ne_of_gt hB)] at h

/-- **A sharp lower bound for a unit logarithm increment.**  For `x > 0`,

```text
log (x+1) - log x ≥ 2/(2x+1).
```

This is the `n = 1` case of `le_log_of_logRatioLower` at the series point `z = 1/(2x+1)`, for which
`(1+z)/(1-z) = (x+1)/x` and `logRatioLower z 1 = 2z`.  It is the two-sided companion of
`Real.log_le_sub_one_of_pos`, which gives only `log (x+1) - log x ≥ 1/(x+1)`. -/
theorem two_div_le_log_succ_sub_log {x : ℝ} (hx : 0 < x) :
    2 / (2 * x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hd : (0 : ℝ) < 2 * x + 1 := by linarith
  set z : ℝ := 1 / (2 * x + 1) with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one hd]; linarith
  have h1p : 1 + z = (2 * x + 2) / (2 * x + 1) := by rw [hz]; field_simp; ring
  have h1m : 1 - z = 2 * x / (2 * x + 1) := by rw [hz]; field_simp; ring
  have hy : (1 + z) / (1 - z) = (x + 1) / x := by
    rw [h1p, h1m, div_div_div_eq]
    field_simp
  have hc : 2 / (2 * x + 1) ≤ logRatioLower z 1 := by
    refine le_of_eq ?_
    simp only [logRatioLower, atanhPartial, Finset.sum_range_one, hz]
    norm_num
    ring
  have h := le_log_of_logRatioLower hz0 hz1 1 hy hc
  rwa [Real.log_div (by linarith) (ne_of_gt hx)] at h

/-! ## Eight-digit enclosures

The named enclosures above are calibrated to `10⁻⁶`, which is what the `13/6` form of the
generalized Coppersmith--Winograd universal barrier consumes.  The block below recalibrates the
four prime logarithms `log 2`, `log 3`, `log 5`, `log 7` to `2·10⁻¹⁰`, and assembles from them the
one composite value that the *sharp* form of that barrier --- the thesis constant `2.16805…` of
[Alman2019, Theorem 5.7] --- consumes.

Nothing changes but the number of series terms: each enclosure is still a single `norm_num` on the
atanh certificate of `Analysis/Log.lean`, at a series point with a one-digit numerator, and the
largest rational any of them touches has twenty digits.  The sharp barrier needs eight significant
digits because the constant it certifies is a *ratio* of two logarithms, `2 log 3 / log S̃`, whose
two candidate values `2.16805` and `2.16797` differ in the sixth digit.
-/

/-- Certified rational lower bound `log 2 ≥ 0.6931471805`, from the atanh series at `x = 1/3` with
twelve terms.  The true value is `0.69314718055994530…`; the certificate is within `1.1·10⁻¹⁰`. -/
theorem log_two_ge_sharp : (6931471805 : ℝ) / 10000000000 ≤ Real.log 2 :=
  le_log_of_logRatioLower (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 12 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log 2 ≤ 0.6931471806`, from the same twelve-term series with
its geometric remainder. -/
theorem log_two_le_sharp : Real.log 2 ≤ 6931471806 / 10000000000 :=
  log_le_of_logRatioUpper (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 12 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- Certified rational lower bound `log (3/2) ≥ 0.4054651081`, from the atanh series at `x = 1/5`
with nine terms.  The true value is `0.40546510810816438…`. -/
theorem log_three_halves_ge_sharp : (4054651081 : ℝ) / 10000000000 ≤ Real.log (3 / 2) :=
  le_log_of_logRatioLower (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 9 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log (3/2) ≤ 0.4054651082`, from the same nine-term series with
its geometric remainder. -/
theorem log_three_halves_le_sharp : Real.log (3 / 2) ≤ 4054651082 / 10000000000 :=
  log_le_of_logRatioUpper (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 9 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- The identity `log (3/2) = log 3 - log 2`, which turns the two `3/2` enclosures into enclosures
of `log 3`.  Going through `3/2` rather than through the series point `x = 1/2` of `log_three_ge`
saves nine terms at this precision, because `1/5` converges much faster than `1/2`. -/
theorem log_three_halves_eq : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
  Real.log_div (by norm_num) (by norm_num)

/-- Certified rational lower bound `log 3 ≥ 1.0986122886`, from `log 3 = log 2 + log (3/2)`.  The
true value is `1.09861228866810969…`. -/
theorem log_three_ge_sharp : (10986122886 : ℝ) / 10000000000 ≤ Real.log 3 := by
  have h := log_three_halves_ge_sharp
  rw [log_three_halves_eq] at h
  linarith [log_two_ge_sharp]

/-- Certified rational upper bound `log 3 ≤ 1.0986122888`, from `log 3 = log 2 + log (3/2)`. -/
theorem log_three_le_sharp : Real.log 3 ≤ 10986122888 / 10000000000 := by
  have h := log_three_halves_le_sharp
  rw [log_three_halves_eq] at h
  linarith [log_two_le_sharp]

/-- Certified rational lower bound `log (5/4) ≥ 0.2231435513`, from the atanh series at `x = 1/9`
with seven terms.  The true value is `0.22314355131420975…`. -/
theorem log_five_quarters_ge_sharp : (2231435513 : ℝ) / 10000000000 ≤ Real.log (5 / 4) :=
  le_log_of_logRatioLower (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 7 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log (5/4) ≤ 0.2231435514`, from the same seven-term series with
its geometric remainder. -/
theorem log_five_quarters_le_sharp : Real.log (5 / 4) ≤ 2231435514 / 10000000000 :=
  log_le_of_logRatioUpper (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 7 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- The identity `log (5/4) = log 5 - 2 log 2`, which turns the two `5/4` enclosures into
enclosures of `log 5`. -/
theorem log_five_quarters_eq : Real.log (5 / 4) = Real.log 5 - 2 * Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- Certified rational lower bound `log 5 ≥ 1.6094379123`, from `log 5 = 2 log 2 + log (5/4)`.  The
true value is `1.60943791243410037…`. -/
theorem log_five_ge_sharp : (16094379123 : ℝ) / 10000000000 ≤ Real.log 5 := by
  have h := log_five_quarters_ge_sharp
  rw [log_five_quarters_eq] at h
  linarith [log_two_ge_sharp]

/-- Certified rational upper bound `log 5 ≤ 1.6094379126`, from `log 5 = 2 log 2 + log (5/4)`. -/
theorem log_five_le_sharp : Real.log 5 ≤ 16094379126 / 10000000000 := by
  have h := log_five_quarters_le_sharp
  rw [log_five_quarters_eq] at h
  linarith [log_two_le_sharp]

/-- Certified rational lower bound `log (8/7) ≥ 0.1335313926`, from the atanh series at `x = 1/15`
with six terms.  The true value is `0.13353139262452262…`. -/
theorem log_eight_sevenths_ge_sharp : (1335313926 : ℝ) / 10000000000 ≤ Real.log (8 / 7) :=
  le_log_of_logRatioLower (x := (1 / 15 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log (8/7) ≤ 0.1335313927`, from the same six-term series with
its geometric remainder. -/
theorem log_eight_sevenths_le_sharp : Real.log (8 / 7) ≤ 1335313927 / 10000000000 :=
  log_le_of_logRatioUpper (x := (1 / 15 : ℝ)) (by norm_num) (by norm_num) 6 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- Certified rational lower bound `log 7 ≥ 1.9459101488`, from `log 7 = 3 log 2 - log (8/7)`.  The
true value is `1.94591014905531330…`. -/
theorem log_seven_ge_sharp : (19459101488 : ℝ) / 10000000000 ≤ Real.log 7 := by
  have h := log_eight_sevenths_le_sharp
  rw [log_eight_sevenths_eq] at h
  linarith [log_two_ge_sharp]

/-- Certified rational upper bound `log 7 ≤ 1.9459101492`, from `log 7 = 3 log 2 - log (8/7)`. -/
theorem log_seven_le_sharp : Real.log 7 ≤ 19459101492 / 10000000000 := by
  have h := log_eight_sevenths_ge_sharp
  rw [log_eight_sevenths_eq] at h
  linarith [log_two_le_sharp]

/-! ### Certified `log 11`

The atanh series at `x = 1/23` gives `log (12/11)` to ten digits in five terms; `log 12` is
`2 log 2 + log 3`. -/

theorem log_twelve_elevenths_ge_sharp : (870113769 : ℝ) / 10000000000 ≤ Real.log (12 / 11) :=
  le_log_of_logRatioLower (x := (1 / 23 : ℝ)) (by norm_num) (by norm_num) 5
    (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

theorem log_twelve_elevenths_le_sharp : Real.log (12 / 11) ≤ 870113770 / 10000000000 :=
  log_le_of_logRatioUpper (x := (1 / 23 : ℝ)) (by norm_num) (by norm_num) 5
    (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder,
      Finset.sum_range_succ])

theorem log_twelve_elevenths_eq :
    Real.log (12 / 11) = 2 * Real.log 2 + Real.log 3 - Real.log 11 := by
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 from by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [Real.log_div (by norm_num) (by norm_num), h12]

/-- Certified rational upper bound `log 11 ≤ 2.3978952731`.  The true value is
`2.39789527279837…`. -/
theorem log_eleven_le_sharp : Real.log 11 ≤ 23978952731 / 10000000000 := by
  have h := log_twelve_elevenths_ge_sharp
  rw [log_twelve_elevenths_eq] at h
  linarith [log_two_le_sharp, log_three_le_sharp]

/-- Certified rational lower bound `log 11 ≥ 2.3978952726`. -/
theorem log_eleven_ge_sharp : (23978952726 : ℝ) / 10000000000 ≤ Real.log 11 := by
  have h := log_twelve_elevenths_le_sharp
  rw [log_twelve_elevenths_eq] at h
  linarith [log_two_ge_sharp, log_three_ge_sharp]

end AlgebraicComplexity.Analysis
