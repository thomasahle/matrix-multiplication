/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants

/-!
# Exact arithmetic for the Duan--Wu--Zhou level-two endpoint `omega < 2.374631`

This lightweight client carries the directed real-arithmetic certificate behind
[DuanWuZhou2022] `global_value.tex` section 6.3 --- the fully published second-power record.
It imports only the reusable logarithm enclosure library; the tensor, hashing, compatibility
and hole-repair arguments live in `MatrixMultiplication/AsymmetricGlobalValue.lean`, and the
assembly of these numbers into a bound on `omega` lives in
`Examples/DuanWuZhouLevelTwoGlobal.lean`.

## The parameters

```text
q = 6,  tau = 2374631 / 3000000,  a = 0.03477403,  b = 0.00021015,
beta = 69022217 / 5000000000    (the free split of the (1,2,1) and (2,1,1) components),
alpha : the fifteen-entry table of `table:result-2nd`, over the denominator D = 10 ^ 8.
```

## Routing

The four `AsymmetricGlobal.GlobalRateData` fields certified here are *rationals*, and the
fifth --- `hashLossRate` --- is declared as `ambientRate * (1 + 10 ^ (-10))`.  The ambient rate
`2 ^ H(alpha)` then cancels out of the hashing branch
`ambientRate * xRate / hashLossRate = xRate / (1 + 10 ^ (-10))`, so no enclosure of
`2 ^ H(alpha)` is needed anywhere and the endpoint comparison is exact rational arithmetic.
The price is the single dual (Gibbs) certificate `dwz63_gibbsDeficit_le_log_hashLossMultiplier`
below, which is what makes the declared `hashLossRate` an upper bound for
`max_{alpha in D_alpha} 2 ^ H(alpha')`.

Each of the four rate rationals sits at fifteen significant digits with a further `10 ^ (-9)`
relative back-off; the back-off absorbs the `m * (error of the ten-digit `log 2` constant)` of
the power-of-two extraction, and 98.8 % of the true margin survives it.

## What is certified

* the finite data identities: the fifteen-entry `alpha` table sums to `10 ^ 8`, its `X` and `Z`
  marginals are the two published five-entry profiles, the Gibbs partition sum `W` is exact,
  and the average-split mass identity `2P + Q = D * alpha_Z(2) * D` holds;
* forty-six directed atanh enclosures (28 lower, 18 upper), each a single `norm_num` on a
  finite rational certificate --- no floating point, no compiled decision procedure;
* the five aggregated obligations they combine into: the two entropy rates from below, the
  compatibility rate from above, the leaf value rate from below, and the Gibbs deficit;
* the exact rational endpoint `min (xRate / K) (zRate / compatRate) * valRate > 64`, with
  `64 = (q + 2) ^ 2 = Rtilde(CW_6 tensor CW_6)`.

Numeric preparation, including the exact `Fraction` verification of every certificate below and
the reproduction of section 6.3 to forty digits, is `better_bound/dwz_endpoint_prep/`
(`PREP.md`, `routing_a_prime.py`, `certificate.json`).

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, sections 6.2--6.3 and `lem:non-rot-values`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Analysis

noncomputable section

/-! ## The published parameters

`q = 6` is load-bearing: at `q = 5` the same optimizer gives `min * alphabar_val = 48.8845`
against `(q + 2) ^ 2 = 49`, so the construction fails there.  (That regression is verified
exactly in `better_bound/dwz_endpoint_prep/reproduce_63.py`; certifying it in Lean would need a
second, upper-directed copy of the whole atom table and is not carried here.) -/

/-- The Coppersmith--Winograd parameter of the level-two construction.  The tensor analysed is
`CW_6 tensor CW_6`, whose asymptotic rank is at most `(q + 2) ^ 2 = 64`. -/
def dwz63Q : ℕ := 6

/-- The exponent parameter `tau = 2374631 / 3000000`; the endpoint is `omega < 3 * tau`. -/
def dwz63Tau : ℝ := 2374631 / 3000000

/-- `3 * tau = 2.374631`, the published bound. -/
theorem dwz63_three_mul_tau : 3 * dwz63Tau = 2374631 / 1000000 := by
  norm_num [dwz63Tau]

/-- The split parameter `a = 0.03477403` of the `(0,2,2)` and `(2,0,2)` components: their
restricted splitting is `(a, 1 - 2a, a)`. -/
def dwz63A : ℝ := 3477403 / 100000000

/-- The split parameter `b = 0.00021015` of the `(1,1,2)` component. -/
def dwz63B : ℝ := 21015 / 100000000

/-- The **free** split parameter of the `(1,2,1)` and `(2,1,1)` components.

Section 6.3 writes their value as `2 ^ (2/3) q ^ tau (q ^ (3 tau) + 2) ^ (1/3)`, whose constant
contains the transcendental exponent `q ^ (3 tau) = 6 ^ 2.374631`.  That constant is the
supremum over `beta` of the `lem:non-rot-values` (d) bound
`(4 / ((1 - 2 beta) ^ (1 - 2 beta) beta ^ (2 beta))) ^ (1/3) q ^ ((2 - 2 beta) tau)`, so **any**
rational `beta` gives a valid lower bound and no enclosure of `6 ^ (3 tau)` is ever needed.  The
value below is the optimum `1 / (2 + q ^ (3 tau))` to ten digits; it loses a relative
`3.1 * 10 ^ (-20)` against a margin of `1.7 * 10 ^ (-7)`.  The committed `2.375477` client
performs the same rationalization with `beta = 7 / 508`. -/
def dwz63Beta : ℝ := 69022217 / 5000000000

/-! ## The finite certificate data

The published table, transcribed over the denominator `D = 10 ^ 8` and checked for the two
identities the analysis actually uses: that it is a probability distribution, and that its two
one-dimensional marginals are the profiles the entropy rates below are computed from.  `alpha`
is symmetric in its first two arguments, so the `Y` marginal equals the `X` marginal and is not
restated. -/

/-- The fifteen entries of `table:result-2nd`, in the order
`(0,0,4) (0,1,3) (0,2,2) (0,3,1) (0,4,0) (1,0,3) (1,1,2) (1,2,1) (1,3,0) (2,0,2) (2,1,1)
(2,2,0) (3,0,1) (3,1,0) (4,0,0)`, sum to the denominator `D = 10 ^ 8`: `alpha` is a genuine
probability distribution on the support `{(i,j,k) : i + j + k = 4}`. -/
theorem dwz63_alpha_sum :
    (20860 + 1211153 + 10366945 + 1333318 + 24731 +
        1211153 + 20088623 + 20734458 + 1251758 + 10366945 +
        20734458 + 10045791 + 1333318 + 1251758 + 24731 : ℕ) = 100000000 := by
  norm_num

/-- The `X` marginal of `alpha` at `i = 0`. -/
theorem dwz63_alphaX_marginal_0 : (20860 + 1211153 + 10366945 + 1333318 + 24731 : ℕ) = 12957007 := by
  norm_num

/-- The `X` marginal of `alpha` at `i = 1`. -/
theorem dwz63_alphaX_marginal_1 : (1211153 + 20088623 + 20734458 + 1251758 : ℕ) = 43285992 := by
  norm_num

/-- The `X` marginal of `alpha` at `i = 2`. -/
theorem dwz63_alphaX_marginal_2 : (10366945 + 20734458 + 10045791 : ℕ) = 41147194 := by
  norm_num

/-- The `X` marginal of `alpha` at `i = 3`. -/
theorem dwz63_alphaX_marginal_3 : (1333318 + 1251758 : ℕ) = 2585076 := by
  norm_num

/-- The `X` marginal of `alpha` at `i = 4`. -/
theorem dwz63_alphaX_marginal_4 : (24731 : ℕ) = 24731 := by
  norm_num

/-- The `Z` marginal of `alpha` at `k = 0`. -/
theorem dwz63_alphaZ_marginal_0 : (24731 + 1251758 + 10045791 + 1251758 + 24731 : ℕ) = 12598769 := by
  norm_num

/-- The `Z` marginal of `alpha` at `k = 1`. -/
theorem dwz63_alphaZ_marginal_1 : (1333318 + 20734458 + 20734458 + 1333318 : ℕ) = 44135552 := by
  norm_num

/-- The `Z` marginal of `alpha` at `k = 2`. -/
theorem dwz63_alphaZ_marginal_2 : (10366945 + 20088623 + 10366945 : ℕ) = 40822513 := by
  norm_num

/-- The `Z` marginal of `alpha` at `k = 3`. -/
theorem dwz63_alphaZ_marginal_3 : (1211153 + 1211153 : ℕ) = 2422306 := by
  norm_num

/-- The `Z` marginal of `alpha` at `k = 4`. -/
theorem dwz63_alphaZ_marginal_4 : (20860 : ℕ) = 20860 := by
  norm_num

/-- **The Gibbs partition sum.**  Weak duality for the transportation polytope: for any positive
product weights `w(i,j,k) = u i * v j * w k` on the support and any distribution `p` with the
given marginals, `H(p) <= log (sum w) - sum p log w`.  The witness below is the
inverse-iterative-proportional-fitting fixed point rounded to denominator `10 ^ 6`; its partition
sum is exact. -/
theorem dwz63_partitionSum_eq :
    ((20881 / 500000 * 542361 / 1000000 * 921 / 100000 +
      20881 / 500000 * 165329 / 125000 * 21927 / 100000 +
      20881 / 500000 * 104033 / 62500 * 1491349 / 1000000 +
      20881 / 500000 * 8157 / 31250 * 1223123 / 1000000 +
      20881 / 500000 * 393 / 31250 * 470879 / 1000000 +
      101843 / 1000000 * 542361 / 1000000 * 21927 / 100000 +
      101843 / 1000000 * 165329 / 125000 * 1491349 / 1000000 +
      101843 / 1000000 * 104033 / 62500 * 1223123 / 1000000 +
      101843 / 1000000 * 8157 / 31250 * 470879 / 1000000 +
      128169 / 1000000 * 542361 / 1000000 * 1491349 / 1000000 +
      128169 / 1000000 * 165329 / 125000 * 1223123 / 1000000 +
      128169 / 1000000 * 104033 / 62500 * 470879 / 1000000 +
      20099 / 1000000 * 542361 / 1000000 * 1223123 / 1000000 +
      20099 / 1000000 * 165329 / 125000 * 470879 / 1000000 +
      121 / 125000 * 542361 / 1000000 * 470879 / 1000000 : ℚ)) =
      249999816060193851 / 250000000000000000 := by
  norm_num

/-- **The average-split mass identity.**  The pooled requirement cell at `k = 2` splits the mass
`alpha(+,+,2)` into the two-letter part `P` and the middle-letter part `Q`; `2P + Q` must
recover `D * (D * alpha_Z(2))`.  This is the one arithmetic consequence of
[DuanWuZhou2022]'s requirement-partition claim that is checkable in closed form. -/
theorem dwz63_average_split_mass :
    (2 * (2 * 10366945 * 3477403 + 20088623 * 21015)
        + (2 * 10366945 * (100000000 - 2 * 3477403) + 20088623 * (100000000 - 2 * 21015)) : ℕ)
      = 100000000 * 40822513 := by
  norm_num

/-! ## The forty-six directed logarithm enclosures

Every entry of `better_bound/dwz_endpoint_prep/certificate.json`.  Each is one application of
a `LogConstants` wrapper at the recorded series point, with the recorded number of atanh terms,
closed by `norm_num` on a finite rational certificate.  Five of them --- the four rate rationals
and `100000000 / 3477403`, `20000000 / 4203` --- are upper enclosures with a power of two
extracted, and use `log_le_of_powTwo_add_logRatioUpper`; without it their series point would be
`x = 0.93` and about two hundred terms. -/

/-- Lower enclosure for `100000000/12957007` (the `X` marginal entropy):
`m = 2`, `14` atanh terms at the series point `x = 12042993/37957007`. -/
theorem dwz63_atom_x0_ge :
    (20435334629731583 / 10000000000000000 : ℝ) ≤ Real.log (100000000 / 12957007 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 2 14 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (12042993 / 37957007 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `12500000/5410749` (the `X` marginal entropy):
`m = 1`, `6` atanh terms at the series point `x = 839251/11660749`. -/
theorem dwz63_atom_x1_ge :
    (1046676392066359 / 1250000000000000 : ℝ) ≤ Real.log (12500000 / 5410749 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (839251 / 11660749 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `50000000/20573597` (the `X` marginal entropy):
`m = 1`, `7` atanh terms at the series point `x = 4426403/45573597`. -/
theorem dwz63_atom_x2_ge :
    (1776028901361011 / 2000000000000000 : ℝ) ≤ Real.log (50000000 / 20573597 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 7 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (4426403 / 45573597 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `25000000/646269` (the `X` marginal entropy):
`m = 5`, `7` atanh terms at the series point `x = 134981/1427519`. -/
theorem dwz63_atom_x3_ge :
    (913853819443327 / 250000000000000 : ℝ) ≤ Real.log (25000000 / 646269 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 5 7 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (134981 / 1427519 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `100000000/24731` (the `X` marginal entropy):
`m = 11`, `15` atanh terms at the series point `x = 192777/588473`. -/
theorem dwz63_atom_x4_ge :
    (20762169867196271 / 2500000000000000 : ℝ) ≤ Real.log (100000000 / 24731 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 11 15 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (192777 / 588473 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `29718193739847/10000000000000` (the declared rational rate itself):
`m = 1`, `10` atanh terms at the series point `x = 9718193739847/49718193739847`. -/
theorem dwz63_atom_xRate_le :
    Real.log (29718193739847 / 10000000000000 : ℝ) ≤
      (5445871745675061 / 5000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 1 10 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ))
      (x := (9718193739847 / 49718193739847 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `100000000/12598769` (the `Z` marginal entropy):
`m = 2`, `15` atanh terms at the series point `x = 12401231/37598769`. -/
theorem dwz63_atom_z0_ge :
    (828628430038507 / 400000000000000 : ℝ) ≤ Real.log (100000000 / 12598769 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 2 15 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (12401231 / 37598769 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `781250/344809` (the `Z` marginal entropy):
`m = 1`, `6` atanh terms at the series point `x = 22908/367717`. -/
theorem dwz63_atom_z1_ge :
    (511190350283509 / 625000000000000 : ℝ) ≤ Real.log (781250 / 344809 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (22908 / 367717 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `100000000/40822513` (the `Z` marginal entropy):
`m = 1`, `7` atanh terms at the series point `x = 9177487/90822513`. -/
theorem dwz63_atom_z2_ge :
    (8959364674820347 / 10000000000000000 : ℝ) ≤ Real.log (100000000 / 40822513 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 1 7 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (9177487 / 90822513 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `50000000/1211153` (the `Z` marginal entropy):
`m = 5`, `8` atanh terms at the series point `x = 351347/2773653`. -/
theorem dwz63_atom_z3_ge :
    (37204502066716993 / 10000000000000000 : ℝ) ≤ Real.log (50000000 / 1211153 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 5 8 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (351347 / 2773653 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `5000000/1043` (the `Z` marginal entropy):
`m = 12`, `6` atanh terms at the series point `x = 11373/144877`. -/
theorem dwz63_atom_z4_ge :
    (5296932509173911 / 625000000000000 : ℝ) ≤ Real.log (5000000 / 1043 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 12 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (11373 / 144877 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `294353582345457/100000000000000` (the declared rational rate itself):
`m = 1`, `10` atanh terms at the series point `x = 94353582345457/494353582345457`. -/
theorem dwz63_atom_zRate_le :
    Real.log (294353582345457 / 100000000000000 : ℝ) ≤
      (2159223039624293 / 2000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 1 10 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ))
      (x := (94353582345457 / 494353582345457 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `100000000/3477403` (the compatibility rate):
`m = 4`, `13` atanh terms at the series point `x = 2772597/9727403`. -/
theorem dwz63_atom_p0_le :
    Real.log (100000000 / 3477403 : ℝ) ≤ (8397211088309031 / 2500000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 4 13 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (2772597 / 9727403 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `50000000/46522597` (the compatibility rate):
`m = 0`, `5` atanh terms at the series point `x = 3477403/96522597`. -/
theorem dwz63_atom_p1_le :
    Real.log (50000000 / 46522597 : ℝ) ≤ (144169707768893 / 2000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (3477403 / 96522597 : ℝ)) (by norm_num) (by norm_num) 5
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `20000000/4203` (the compatibility rate):
`m = 12`, `6` atanh terms at the series point `x = 10877/145373`. -/
theorem dwz63_atom_p2_le :
    Real.log (20000000 / 4203 : ℝ) ≤ (8467688996993809 / 1000000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 12 6 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ)) (x := (10877 / 145373 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `10000000/9995797` (the compatibility rate):
`m = 0`, `2` atanh terms at the series point `x = 4203/19995797`. -/
theorem dwz63_atom_p3_le :
    Real.log (10000000 / 9995797 : ℝ) ≤ (2101941754009 / 5000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (4203 / 19995797 : ℝ)) (by norm_num) (by norm_num) 2
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `816450260000000/14504450740003` (the compatibility rate):
`m = 5`, `13` atanh terms at the series point `x = 11009619884997/40018521365003`. -/
theorem dwz63_atom_p4_ge :
    (20152552208931029 / 5000000000000000 : ℝ) ≤
      Real.log (816450260000000 / 14504450740003 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 5 13 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ))
      (x := (11009619884997 / 40018521365003 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `408225130000000/393720679259997` (the compatibility rate):
`m = 0`, `4` atanh terms at the series point `x = 14504450740003/801945809259997`. -/
theorem dwz63_atom_p5_ge :
    (22610680902771 / 625000000000000 : ℝ) ≤
      Real.log (408225130000000 / 393720679259997 : ℝ) := by
  apply le_log_of_logRatioLower (x := (14504450740003 / 801945809259997 : ℝ))
      (by norm_num) (by norm_num) 4
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `1000000000000000/990482639134399` (the declared rational rate itself):
`m = 0`, `3` atanh terms at the series point `x = 9517360865601/1990482639134399`. -/
theorem dwz63_atom_pRate_le :
    Real.log (1000000000000000 / 990482639134399 : ℝ) ≤
      (95629403728077 / 10000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (9517360865601 / 1990482639134399 : ℝ))
      (by norm_num) (by norm_num) 3
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `2` (the leaf value rate):
`m = 1`, `0` atanh terms at the series point `x = 0`. -/
theorem dwz63_atom_v0_ge :
    (1386294361 / 2000000000 : ℝ) ≤ Real.log 2 := by
  apply le_log_of_powTwo_add_logRatioLower 1 0 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (0 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `3` (the leaf value rate):
`m = 1`, `10` atanh terms at the series point `x = 1/5`. -/
theorem dwz63_atom_v1_ge :
    (10986122886081641 / 10000000000000000 : ℝ) ≤ Real.log 3 := by
  apply le_log_of_powTwo_add_logRatioLower 1 10 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `19` (the leaf value rate):
`m = 4`, `7` atanh terms at the series point `x = 3/35`. -/
theorem dwz63_atom_v2_ge :
    (920137180914581 / 312500000000000 : ℝ) ≤ Real.log 19 := by
  apply le_log_of_powTwo_add_logRatioLower 4 7 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (3 / 35 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `100000000/3477403` (the leaf value rate):
`m = 4`, `13` atanh terms at the series point `x = 2772597/9727403`. -/
theorem dwz63_atom_v3_ge :
    (33588844349236081 / 10000000000000000 : ℝ) ≤ Real.log (100000000 / 3477403 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 4 13 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (2772597 / 9727403 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `50000000/46522597` (the leaf value rate):
`m = 0`, `5` atanh terms at the series point `x = 3477403/96522597`. -/
theorem dwz63_atom_v4_ge :
    (720848538844461 / 10000000000000000 : ℝ) ≤ Real.log (50000000 / 46522597 : ℝ) := by
  apply le_log_of_logRatioLower (x := (3477403 / 96522597 : ℝ)) (by norm_num) (by norm_num) 5
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `20000000/4203` (the leaf value rate):
`m = 12`, `6` atanh terms at the series point `x = 10877/145373`. -/
theorem dwz63_atom_v5_ge :
    (84676889957938043 / 10000000000000000 : ℝ) ≤ Real.log (20000000 / 4203 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 12 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (10877 / 145373 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `10000000/9995797` (the leaf value rate):
`m = 0`, `2` atanh terms at the series point `x = 4203/19995797`. -/
theorem dwz63_atom_v6_ge :
    (4203883508017 / 10000000000000000 : ℝ) ≤ Real.log (10000000 / 9995797 : ℝ) := by
  apply le_log_of_logRatioLower (x := (4203 / 19995797 : ℝ)) (by norm_num) (by norm_num) 2
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `5000000000/69022217` (the leaf value rate):
`m = 6`, `6` atanh terms at the series point `x = 9102783/147147217`. -/
theorem dwz63_atom_v7_ge :
    (21413823763891343 / 5000000000000000 : ℝ) ≤ Real.log (5000000000 / 69022217 : ℝ) := by
  apply le_log_of_powTwo_add_logRatioLower 6 6 log_two_ge_sharp
      (logTwoLower := (6931471805 / 10000000000 : ℝ)) (x := (9102783 / 147147217 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `2500000000/2430977783` (the leaf value rate):
`m = 0`, `4` atanh terms at the series point `x = 69022217/4930977783`. -/
theorem dwz63_atom_v8_ge :
    (279971756193631 / 10000000000000000 : ℝ) ≤ Real.log (2500000000 / 2430977783 : ℝ) := by
  apply le_log_of_logRatioLower (x := (69022217 / 4930977783 : ℝ)) (by norm_num) (by norm_num) 4
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `21535632886771/1000000000000` (the declared rational rate itself):
`m = 4`, `9` atanh terms at the series point `x = 5535632886771/37535632886771`. -/
theorem dwz63_atom_vRate_le :
    Real.log (21535632886771 / 1000000000000 : ℝ) ≤ (1534854453493149 / 500000000000000 : ℝ) := by
  apply log_le_of_powTwo_add_logRatioUpper 4 9 log_two_le_sharp
      (logTwoUpper := (6931471806 / 10000000000 : ℝ))
      (x := (5535632886771 / 37535632886771 : ℝ)) <;>
    norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `250000000000000000/249999816060193851` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 183939806149/499999816060193851`. -/
theorem dwz63_atom_g0_ge :
    (919699369 / 1250000000000000 : ℝ) ≤
      Real.log (250000000000000000 / 249999816060193851 : ℝ) := by
  apply le_log_of_logRatioLower (x := (183939806149 / 499999816060193851 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `1490051696823/1490000000000` (a Gibbs dual ratio):
`m = 0`, `2` atanh terms at the series point `x = 51696823/2980051696823`. -/
theorem dwz63_atom_g1_ge :
    (346952524751 / 10000000000000000 : ℝ) ≤ Real.log (1490051696823 / 1490000000000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (51696823 / 2980051696823 : ℝ))
      (by norm_num) (by norm_num) 2
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `75697153534023/75697062500000` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 91034023/151394216034023`. -/
theorem dwz63_atom_g2_ge :
    (240521799 / 200000000000000 : ℝ) ≤ Real.log (75697153534023 / 75697062500000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (91034023 / 151394216034023 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Lower enclosure for `3239676929105477/3239670312500000` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 6616605477/6479347241605477`. -/
theorem dwz63_atom_g3_ge :
    (2552959901 / 1250000000000000 : ℝ) ≤ Real.log (3239676929105477 / 3239670312500000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (6616605477 / 6479347241605477 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `29761562500000/29761433689713` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 128810287/59522996189713`. -/
theorem dwz63_atom_g4_le :
    Real.log (29761562500000 / 29761433689713 : ℝ) ≤ (43280847823 / 10000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (128810287 / 59522996189713 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `552031250000/552020398401` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 10851599/1104051648401`. -/
theorem dwz63_atom_g5_le :
    Real.log (552031250000 / 552020398401 : ℝ) ≤ (98288870967 / 5000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (10851599 / 1104051648401 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `1211153000000000/1211152565099421` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 434900579/2422305565099421`. -/
theorem dwz63_atom_g6_le :
    Real.log (1211153000000000 / 1211152565099421 : ℝ) ≤ (1795399331 / 5000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (434900579 / 2422305565099421 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `25110778750000000/25110739931247103` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 38818752897/50221518681247103`. -/
theorem dwz63_atom_g7_le :
    Real.log (25110778750000000 / 25110739931247103 : ℝ) ≤ (386475299 / 250000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (38818752897 / 50221518681247103 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `12959036250000000/12959028326673737` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 7923326263/25918064576673737`. -/
theorem dwz63_atom_g8_le :
    Real.log (12959036250000000 / 12959028326673737 : ℝ) ≤
      (611413421 / 1000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (7923326263 / 25918064576673737 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `391174889585529/391174375000000` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 514585529/782349264585529`. -/
theorem dwz63_atom_g9_ge :
    (6577439927 / 5000000000000000 : ℝ) ≤ Real.log (391174889585529 / 391174375000000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (514585529 / 782349264585529 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `103669450000000000/103669436050005141` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 13949994859/207338886050005141`. -/
theorem dwz63_atom_g10_le :
    Real.log (103669450000000000 / 103669436050005141 : ℝ) ≤
      (1345622631 / 10000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (13949994859 / 207338886050005141 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `8639357500000000/8639346902497641` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 10597502359/17278704402497641`. -/
theorem dwz63_atom_g11_le :
    Real.log (8639357500000000 / 8639346902497641 : ℝ) ≤ (3066636859 / 2500000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (10597502359 / 17278704402497641 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `697624375000000/697623226254687` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 1148745313/1395247601254687`. -/
theorem dwz63_atom_g12_le :
    Real.log (697624375000000 / 697623226254687 : ℝ) ≤ (658661767 / 400000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (1148745313 / 1395247601254687 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Upper enclosure for `13333180000000000/13333158315186897` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 21684813103/26666338315186897`. -/
theorem dwz63_atom_g13_le :
    Real.log (13333180000000000 / 13333158315186897 : ℝ) ≤
      (16263810087 / 10000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (21684813103 / 26666338315186897 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `1564706229284909/1564697500000000` (a Gibbs dual ratio):
`m = 0`, `1` atanh term at the series point `x = 8729284909/3129403729284909`. -/
theorem dwz63_atom_g14_ge :
    (55788806201 / 10000000000000000 : ℝ) ≤
      Real.log (1564706229284909 / 1564697500000000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (8729284909 / 3129403729284909 : ℝ))
      (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-- Upper enclosure for `30913750000000/30901755043599` (a Gibbs dual ratio):
`m = 0`, `2` atanh terms at the series point `x = 11994956401/61815505043599`. -/
theorem dwz63_atom_g15_le :
    Real.log (30913750000000 / 30901755043599 : ℝ) ≤ (3880889282743 / 10000000000000000 : ℝ) := by
  apply log_le_of_logRatioUpper (x := (11994956401 / 61815505043599 : ℝ))
      (by norm_num) (by norm_num) 2
  · norm_num
  · norm_num [logRatioUpper, logRatioLower, atanhPartial, atanhRemainder,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- Lower enclosure for `10000000001/10000000000` (the hash-loss multiplier `K`):
`m = 0`, `1` atanh term at the series point `x = 1/20000000001`. -/
theorem dwz63_atom_hashK_ge :
    (999999 / 10000000000000000 : ℝ) ≤ Real.log (10000000001 / 10000000000 : ℝ) := by
  apply le_log_of_logRatioLower (x := (1 / 20000000001 : ℝ)) (by norm_num) (by norm_num) 1
  · norm_num
  · norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ,
      Finset.sum_range_zero]

/-! ## The five aggregated obligations

Each expression below is the certificate normal form of one section 6.3 quantity: every atom is
oriented above `1`, and the coefficients are the exact rationals the paper produces.  The
aggregation is a single `linarith` over the directed atom enclosures --- a positive coefficient
consumes the atom's lower enclosure, a negative one its upper enclosure --- and the final
rational comparison is exact. -/

/-- **`H_e(alpha_X)`**, the natural-logarithm entropy of the `X` marginal
`[12957007, 43285992, 41147194, 2585076, 24731] / 10 ^ 8`.  Its exponential is
`alphabar_X = 2 ^ H(alpha_X)`, the rate of `N_X`. -/
def dwz63EntropyX : ℝ :=
  5410749 / 12500000 * Real.log (12500000 / 5410749 : ℝ)
    + 20573597 / 50000000 * Real.log (50000000 / 20573597 : ℝ)
    + 12957007 / 100000000 * Real.log (100000000 / 12957007 : ℝ)
    + 646269 / 25000000 * Real.log (25000000 / 646269 : ℝ)
    + 24731 / 100000000 * Real.log (100000000 / 24731 : ℝ)

/-- **`H_e(alpha_Z)`**, the natural-logarithm entropy of the `Z` marginal
`[12598769, 44135552, 40822513, 2422306, 20860] / 10 ^ 8`.  Its exponential is
`alphabar_Z = 2 ^ H(alpha_Z)`, the rate of `N_Z`. -/
def dwz63EntropyZ : ℝ :=
  344809 / 781250 * Real.log (781250 / 344809 : ℝ)
    + 40822513 / 100000000 * Real.log (100000000 / 40822513 : ℝ)
    + 12598769 / 100000000 * Real.log (100000000 / 12598769 : ℝ)
    + 1211153 / 50000000 * Real.log (50000000 / 1211153 : ℝ)
    + 1043 / 5000000 * Real.log (5000000 / 1043 : ℝ)

/-- **`log alphabar_p`**, the logarithm of the compatibility rate of
`Analysis/CompatibilityRate.lean`.  It collects the boundary components' binary splits,
the `a`- and `b`-splits of `(0,2,2)`/`(2,0,2)` and `(1,1,2)`, and subtracts the pooled
average split at `k = 2` --- the two negative coefficients below.  It is *negative*:
`alphabar_p = 0.99048...` is a loss. -/
def dwz63LogCompat : ℝ :=
  200801797517531 / 1000000000000000 * Real.log (10000000 / 9995797 : ℝ)
    - 393720679259997 / 1000000000000000 * Real.log (408225130000000 / 393720679259997 : ℝ)
    + 96459440871233 / 500000000000000 * Real.log (50000000 / 46522597 : ℝ)
    + 7210009128767 / 500000000000000 * Real.log (100000000 / 3477403 : ℝ)
    - 14504450740003 / 1000000000000000 * Real.log (816450260000000 / 14504450740003 : ℝ)
    + 84432482469 / 1000000000000000 * Real.log (20000000 / 4203 : ℝ)

/-- **`log alphabar_val`**, the logarithm of the leaf value rate
`prod V^(6)(T_{i,j,k}, alphatilde)^{alpha(i,j,k)}`.  The six component values are
`1` on the three corners, `(2q)^tau` on the six `(0,1,3)`-type components, `(q^2+2)^tau`
on `(2,2,0)`, the `a`-split formula on `(0,2,2)`/`(2,0,2)`, the `b`-split formula on
`(1,1,2)`, and --- at the free rational `beta` of the note below --- the same
`lem:non-rot-values` (d) formula on `(1,2,1)` and `(2,1,1)`. -/
def dwz63LogVal : ℝ :=
  200801797517531 / 3000000000000000 * Real.log (10000000 / 9995797 : ℝ)
    + 8400834456757769 / 62500000000000000 * Real.log (2500000000 / 2430977783 : ℝ)
    + 229055578535496890023 / 1500000000000000000000 * Real.log (50000000 / 46522597 : ℝ)
    + 705331274218198411068559 / 375000000000000000000000 * Real.log 2
    + 499082010641799661068559 / 375000000000000000000000 * Real.log 3
    + 7951682242707 / 100000000000000 * Real.log 19
    + 17121111187453109977 / 1500000000000000000000 * Real.log (100000000 / 3477403 : ℝ)
    + 238523043242231 / 62500000000000000 * Real.log (5000000000 / 69022217 : ℝ)
    + 28144160823 / 1000000000000000 * Real.log (20000000 / 4203 : ℝ)

/-- **The Gibbs deficit**, the dual bound on the hash loss:
`H_e(alpha') - H_e(alpha) <= log W + sum_c alpha(c) log (alpha(c) / (u_i v_j w_k))`
uniformly over every `alpha'` in `D_alpha` (every distribution sharing the three
marginals of `alpha`).  The right-hand side is what this expression is; certifying it
below `log (1 + 10 ^ (-10))` is exactly what makes
`hashLossRate := ambientRate * (1 + 10 ^ (-10))` a legitimate upper bound for
`max_{alpha' in D_alpha} 2 ^ H(alpha')`. -/
def dwz63GibbsDeficit : ℝ :=
  2073389 / 20000000 * Real.log (103669450000000000 / 103669436050005141 : ℝ)
    + 1211153 / 100000000 * Real.log (1211153000000000 / 1211152565099421 : ℝ)
    + 10367229 / 50000000 * Real.log (12959036250000000 / 12959028326673737 : ℝ)
    - Real.log (250000000000000000 / 249999816060193851 : ℝ)
    - 1211153 / 100000000 * Real.log (75697153534023 / 75697062500000 : ℝ)
    + 10367229 / 50000000 * Real.log (8639357500000000 / 8639346902497641 : ℝ)
    - 625879 / 50000000 * Real.log (391174889585529 / 391174375000000 : ℝ)
    + 20088623 / 100000000 * Real.log (25110778750000000 / 25110739931247103 : ℝ)
    + 666659 / 50000000 * Real.log (13333180000000000 / 13333158315186897 : ℝ)
    + 10045791 / 100000000 * Real.log (697624375000000 / 697623226254687 : ℝ)
    - 2073389 / 20000000 * Real.log (3239676929105477 / 3239670312500000 : ℝ)
    + 666659 / 50000000 * Real.log (29761562500000 / 29761433689713 : ℝ)
    - 625879 / 50000000 * Real.log (1564706229284909 / 1564697500000000 : ℝ)
    + 24731 / 100000000 * Real.log (552031250000 / 552020398401 : ℝ)
    - 1043 / 5000000 * Real.log (1490051696823 / 1490000000000 : ℝ)
    + 24731 / 100000000 * Real.log (30913750000000 / 30901755043599 : ℝ)

/-! ### The declared rational rates

Fifteen significant digits with a `10 ^ (-9)` relative back-off, in the direction each field is
consumed: `xRate`, `zRate` and `valRate` from below (they sit in denominators of the modulus, or
multiply the copy count), `compatRate` from above (it sits in a numerator).  Getting `compatRate`
or the hash-loss multiplier the wrong way round is the silent-unsoundness direction; both are
recorded here with the enclosure that fixes their sign. -/

/-- The declared `xRate`, a lower bound for `alphabar_X = 2 ^ H(alpha_X) = 2.971819376956...`. -/
def dwz63XRate : ℝ := 29718193739847 / 10000000000000

/-- The declared `zRate`, a lower bound for `alphabar_Z = 2 ^ H(alpha_Z) = 2.943535826398...`. -/
def dwz63ZRate : ℝ := 294353582345457 / 100000000000000

/-- The declared `compatRate`, an **upper** bound for `alphabar_p = 0.990482638143...`. -/
def dwz63CompatRate : ℝ := 990482639134399 / 1000000000000000

/-- The declared `valRate`, a lower bound for `alphabar_val = 21.535632908306...`. -/
def dwz63ValRate : ℝ := 21535632886771 / 1000000000000

/-- The hash-loss multiplier `K = 1 + 10 ^ (-10)`.  The declared `hashLossRate` is
`ambientRate * K`; the true multiplier is `exp (1.96701 * 10 ^ (-11))`, so `K` carries a factor
of five of cushion. -/
def dwz63HashLossMultiplier : ℝ := 10000000001 / 10000000000

theorem dwz63XRate_pos : (0 : ℝ) < dwz63XRate := by
  norm_num [dwz63XRate]

theorem dwz63ZRate_pos : (0 : ℝ) < dwz63ZRate := by
  norm_num [dwz63ZRate]

theorem dwz63CompatRate_pos : (0 : ℝ) < dwz63CompatRate := by
  norm_num [dwz63CompatRate]

theorem dwz63ValRate_pos : (0 : ℝ) < dwz63ValRate := by
  norm_num [dwz63ValRate]

theorem dwz63HashLossMultiplier_pos : (0 : ℝ) < dwz63HashLossMultiplier := by
  norm_num [dwz63HashLossMultiplier]

/-- **The `xRate` obligation.**  The declared rational is below alphabar_X, so the rate it
    declares is genuinely achieved: `log dwz63XRate <= dwz63EntropyX`. -/
theorem dwz63_log_xRate_le : Real.log dwz63XRate ≤ dwz63EntropyX := by
  simp only [dwz63XRate, dwz63EntropyX]
  linarith [dwz63_atom_xRate_le, dwz63_atom_x0_ge, dwz63_atom_x1_ge, dwz63_atom_x2_ge,
    dwz63_atom_x3_ge, dwz63_atom_x4_ge]

/-- The exponential form of the preceding obligation: the declared rational rate is at most
    alphabar_X = `Real.exp dwz63EntropyX`. -/
theorem dwz63_xRate_le_exp : dwz63XRate ≤ Real.exp dwz63EntropyX := by
  have h := Real.exp_le_exp.mpr dwz63_log_xRate_le
  rwa [Real.exp_log dwz63XRate_pos] at h

/-- **The `zRate` obligation.**  The declared rational is below alphabar_Z, so the rate it
    declares is genuinely achieved: `log dwz63ZRate <= dwz63EntropyZ`. -/
theorem dwz63_log_zRate_le : Real.log dwz63ZRate ≤ dwz63EntropyZ := by
  simp only [dwz63ZRate, dwz63EntropyZ]
  linarith [dwz63_atom_zRate_le, dwz63_atom_z0_ge, dwz63_atom_z1_ge, dwz63_atom_z2_ge,
    dwz63_atom_z3_ge, dwz63_atom_z4_ge]

/-- The exponential form of the preceding obligation: the declared rational rate is at most
    alphabar_Z = `Real.exp dwz63EntropyZ`. -/
theorem dwz63_zRate_le_exp : dwz63ZRate ≤ Real.exp dwz63EntropyZ := by
  have h := Real.exp_le_exp.mpr dwz63_log_zRate_le
  rwa [Real.exp_log dwz63ZRate_pos] at h

/-- **The `compatRate` obligation.**  The declared rational is above alphabar_p, the direction
    a numerator needs: `dwz63LogCompat <= log dwz63CompatRate`. -/
theorem dwz63_logCompat_le_log_compatRate : dwz63LogCompat ≤ Real.log dwz63CompatRate := by
  simp only [dwz63CompatRate, dwz63LogCompat]
  have hinv : Real.log (990482639134399 / 1000000000000000 : ℝ) =
      -Real.log (1000000000000000 / 990482639134399 : ℝ) := by
    have hrecip : ((1000000000000000 : ℝ) / 990482639134399)⁻¹ = 990482639134399 / 1000000000000000 := by
      norm_num
    rw [← hrecip, Real.log_inv]
  linarith [hinv, dwz63_atom_pRate_le, dwz63_atom_p0_le, dwz63_atom_p1_le, dwz63_atom_p2_le,
    dwz63_atom_p3_le, dwz63_atom_p4_ge, dwz63_atom_p5_ge]

/-- The exponential form: alphabar_p = `Real.exp dwz63LogCompat` is at most the declared rational. -/
theorem dwz63_exp_le_compatRate : Real.exp dwz63LogCompat ≤ dwz63CompatRate := by
  have h := Real.exp_le_exp.mpr dwz63_logCompat_le_log_compatRate
  rwa [Real.exp_log dwz63CompatRate_pos] at h

/-- **The `valRate` obligation.**  The declared rational is below alphabar_val, so the rate it
    declares is genuinely achieved: `log dwz63ValRate <= dwz63LogVal`. -/
theorem dwz63_log_valRate_le : Real.log dwz63ValRate ≤ dwz63LogVal := by
  simp only [dwz63ValRate, dwz63LogVal]
  linarith [dwz63_atom_vRate_le, dwz63_atom_v0_ge, dwz63_atom_v1_ge, dwz63_atom_v2_ge,
    dwz63_atom_v3_ge, dwz63_atom_v4_ge, dwz63_atom_v5_ge, dwz63_atom_v6_ge, dwz63_atom_v7_ge,
    dwz63_atom_v8_ge]

/-- The exponential form of the preceding obligation: the declared rational rate is at most
    alphabar_val = `Real.exp dwz63LogVal`. -/
theorem dwz63_valRate_le_exp : dwz63ValRate ≤ Real.exp dwz63LogVal := by
  have h := Real.exp_le_exp.mpr dwz63_log_valRate_le
  rwa [Real.exp_log dwz63ValRate_pos] at h

/-- **The hash-loss obligation.**  The Gibbs deficit is below `log K`, so
    `max_{alpha' in D_alpha} 2 ^ H(alpha') <= 2 ^ H(alpha) * K`: declaring
    `hashLossRate := ambientRate * K` is sound.  The certified deficit is
    `1.96702 * 10 ^ (-11)` nats against `log K >= 9.99999 * 10 ^ (-11)`. -/
theorem dwz63_gibbsDeficit_le_log_hashLossMultiplier :
    dwz63GibbsDeficit ≤ Real.log dwz63HashLossMultiplier := by
  simp only [dwz63GibbsDeficit, dwz63HashLossMultiplier]
  linarith [dwz63_atom_hashK_ge, dwz63_atom_g0_ge, dwz63_atom_g1_ge, dwz63_atom_g2_ge,
    dwz63_atom_g3_ge, dwz63_atom_g4_le, dwz63_atom_g5_le, dwz63_atom_g6_le, dwz63_atom_g7_le,
    dwz63_atom_g8_le, dwz63_atom_g9_ge, dwz63_atom_g10_le, dwz63_atom_g11_le, dwz63_atom_g12_le,
    dwz63_atom_g13_le, dwz63_atom_g14_ge, dwz63_atom_g15_le]

/-! ## The exact rational endpoint

With `ambientRate` cancelled the two branches of `[DuanWuZhou2022]`'s `min` are
`xRate / K` and `zRate / compatRate`, and the endpoint comparison is pure rational arithmetic
against `64 = (q + 2) ^ 2 = Rtilde(CW_6 tensor CW_6)`. -/

/-- **Branch one binds.**  The hashing branch `xRate / K = 2.97181937368751` is strictly
    below the combination-loss branch `zRate / compatRate = 2.97181970400509`, so the `min` of
    `eq:numeric_conclusion_g` genuinely selects a branch and the anti-vacuity concern about a
    degenerate `min` does not arise.  (Branch one is also the tighter of the two published
    margins: relative `1.7456 * 10 ^ (-7)` against branch two's `2.8661 * 10 ^ (-7)`.) -/
theorem dwz63_branchOne_lt_branchTwo :
    dwz63XRate / dwz63HashLossMultiplier < dwz63ZRate / dwz63CompatRate := by
  norm_num [dwz63XRate, dwz63HashLossMultiplier, dwz63ZRate, dwz63CompatRate]

/-- **The endpoint.**  `min (xRate / K) (zRate / compatRate) * valRate > 64`, exactly.  The
    excess is `110375281109181864037 / 10000000001000000000000000`,
    a relative margin of `1.7246 * 10 ^ (-7)`, which is `98.8 %` of the true margin of the
    published parameters.  `norm_num` decides it outright. -/
theorem dwz63_endpoint_gt_64 :
    (64 : ℝ) <
      min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) *
        dwz63ValRate := by
  rw [min_eq_left dwz63_branchOne_lt_branchTwo.le]
  norm_num [dwz63XRate, dwz63HashLossMultiplier, dwz63ValRate]

end

end AlgebraicComplexity.Examples
