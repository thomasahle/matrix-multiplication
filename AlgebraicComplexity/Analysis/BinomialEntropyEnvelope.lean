/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A loss-free entropy envelope for binomial coefficients

The method-of-types estimate `binom(n, k) ≤ n^n / (k^k (n-k)^{n-k})` is usually stated with a
Stirling correction.  For a *proportional* schedule `n = (p+m)N`, `k = pN` the correction is not
needed: one term of the binomial expansion of `(x + y)^n = 1` at `x = p/(p+m)` is already at most
one, which gives the bound with no loss at all and, crucially, with a *geometric* right-hand side
`Φ^N`.

A geometric envelope is what a hashing schedule needs.  The competitor count of an affine-hashing
pass fixes the modulus, the modulus enters Behrend's bound as `M^{1+o(1)}`, and the removal lemma
`Growth.sqrt_log_le_mul_sqrt_succ` only absorbs `√(log M)` when `log M` grows linearly in `N`.  A
linear-in-`N` loss inside the envelope would therefore have to be paid for inside the base, which
degrades the certified constant.  See
`Examples/CoppersmithWinogradRectangularRate.lean` for the client.

## Main definitions and results

* `choose_mul_split_pow_le_one` -- one term of a binomial expansion of `1` is at most `1`;
* `binomialEntropyBase p m = (p+m)^(p+m) / (p^p · m^m)` -- the two-letter entropy base;
* `choose_scaled_le_binomialEntropyBase_pow` -- `binom((p+m)N, pN) ≤ (binomialEntropyBase p m)^N`,
  with no subexponential factor;
* `log_binomialEntropyBase` -- its logarithm, `(p+m) log (p+m) - p log p - m log m`;
* `factorial_mul_factorial_le_of_le` -- the Schur-type comparison
  `(x+d)! · y! ≤ (y+d)! · x!` for `x ≤ y`, which is how a client decides *which* leg of a
  multi-letter type carries the largest fiber.

## Position in the library

Layer 2 (`AlgebraicComplexity/Analysis/`).  Nothing here mentions a tensor, a
matrix-multiplication construction, or a numerical bound.
-/

namespace AlgebraicComplexity.Analysis

open scoped BigOperators

/-! ## One term of a binomial expansion -/

/-- **One term of a binomial expansion is at most one.**  For `x, y ≥ 0` with `x + y = 1` and
`k ≤ n`, `binom(n, k) · x^k · y^{n-k} ≤ 1`.

This is the loss-free form of the method-of-types upper bound: taking `x = k/n` gives
`binom(n, k) ≤ n^n / (k^k (n-k)^{n-k})` with no Stirling correction. -/
theorem choose_mul_split_pow_le_one {n k : ℕ} (hkn : k ≤ n) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) :
    ((n.choose k : ℕ) : ℝ) * (x ^ k * y ^ (n - k)) ≤ 1 := by
  classical
  have hsum : (x + y) ^ n =
      ∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i) * ((n.choose i : ℕ) : ℝ) :=
    add_pow x y n
  have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ i ∈ Finset.range (n + 1),
      0 ≤ x ^ i * y ^ (n - i) * ((n.choose i : ℕ) : ℝ) := by
    intro i _
    exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)) (Nat.cast_nonneg _)
  have hsingle := Finset.single_le_sum hnonneg hmem
  rw [← hsum, hxy, one_pow] at hsingle
  calc ((n.choose k : ℕ) : ℝ) * (x ^ k * y ^ (n - k))
      = x ^ k * y ^ (n - k) * ((n.choose k : ℕ) : ℝ) := by ring
    _ ≤ 1 := hsingle

/-! ## The two-letter entropy base -/

/-- The two-letter entropy base `(p+m)^(p+m) / (p^p · m^m)`.  It is the exact exponential growth
rate of `binom((p+m)N, pN)` in `N`. -/
noncomputable def binomialEntropyBase (p m : ℕ) : ℝ :=
  ((p + m : ℕ) : ℝ) ^ (p + m) / ((p : ℝ) ^ p * (m : ℝ) ^ m)

theorem binomialEntropyBase_pos {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    0 < binomialEntropyBase p m := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  unfold binomialEntropyBase
  positivity

/-- **The envelope is exact, with no subexponential loss:** `binom((p+m)N, pN) ≤ Φ^N`. -/
theorem choose_scaled_le_binomialEntropyBase_pow {p m : ℕ} (hp : 0 < p) (hm : 0 < m) (N : ℕ) :
    ((Nat.choose ((p + m) * N) (p * N) : ℕ) : ℝ) ≤ binomialEntropyBase p m ^ N := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  set x : ℝ := (p : ℝ) / ((p + m : ℕ) : ℝ) with hxdef
  set y : ℝ := (m : ℝ) / ((p + m : ℕ) : ℝ) with hydef
  have hxpos : 0 < x := div_pos hpR hsR
  have hypos : 0 < y := div_pos hmR hsR
  have hs0 : ((p + m : ℕ) : ℝ) ≠ 0 := hsR.ne'
  have hxy : x + y = 1 := by
    rw [hxdef, hydef, ← add_div, div_eq_one_iff_eq hs0]
    push_cast
    ring
  have hbase : x ^ p * y ^ m = 1 / binomialEntropyBase p m := by
    unfold binomialEntropyBase
    rw [hxdef, hydef, div_pow, div_pow, div_mul_div_comm, ← pow_add, one_div_div]
  have hΦpos : 0 < binomialEntropyBase p m := binomialEntropyBase_pos hp hm
  have hkn : p * N ≤ (p + m) * N := Nat.mul_le_mul_right N (by omega)
  have hsub : (p + m) * N - p * N = m * N := by
    rw [add_mul]
    exact Nat.add_sub_cancel_left _ _
  have hle := choose_mul_split_pow_le_one hkn hxpos.le hypos.le hxy
  rw [hsub, pow_mul, pow_mul, ← mul_pow, hbase] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (pow_pos hΦpos N).le
  rwa [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hΦpos.ne', one_pow, mul_one,
    one_mul] at hmul

/-- The envelope is at least `1`, as it must be to dominate a positive integer count. -/
theorem one_le_binomialEntropyBase {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    1 ≤ binomialEntropyBase p m := by
  have h := choose_scaled_le_binomialEntropyBase_pow hp hm 1
  rw [pow_one, mul_one, mul_one] at h
  have h1 : (1 : ℝ) ≤ ((Nat.choose (p + m) p : ℕ) : ℝ) := by
    have : 0 < Nat.choose (p + m) p := Nat.choose_pos (by omega)
    exact_mod_cast this
  linarith

/-- Explicit logarithm of the two-letter entropy base. -/
theorem log_binomialEntropyBase {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    Real.log (binomialEntropyBase p m) =
      ((p + m : ℕ) : ℝ) * Real.log ((p + m : ℕ) : ℝ)
        - (p : ℝ) * Real.log (p : ℝ) - (m : ℝ) * Real.log (m : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  have hA : (0 : ℝ) < ((p + m : ℕ) : ℝ) ^ (p + m) := pow_pos hsR _
  have hP : (0 : ℝ) < (p : ℝ) ^ p := pow_pos hpR _
  have hM : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hmR _
  unfold binomialEntropyBase
  rw [Real.log_div hA.ne' (mul_pos hP hM).ne', Real.log_mul hP.ne' hM.ne',
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-! ## A Schur-type factorial comparison

`∏ x_i !` over a partition of a fixed total is larger the more spread out the partition is.  The
two-part instance below is the only form the clients need: it decides which leg of a multi-letter
word type has the smallest marginal type class, hence the largest type-restricted fiber. -/

/-- **Moving mass to the larger part increases the factorial product.**  For `x ≤ y`,
`(x+d)! · y! ≤ (y+d)! · x!`.

Equivalently `binom(x+d, d) ≤ binom(y+d, d)`, which is how it is proved. -/
theorem factorial_mul_factorial_le_of_le {x y d : ℕ} (h : x ≤ y) :
    (x + d).factorial * y.factorial ≤ (y + d).factorial * x.factorial := by
  have hx : (x + d).choose d * (d.factorial * x.factorial) = (x + d).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show d ≤ x + d by omega)
    rw [show x + d - d = x from by omega] at this
    calc (x + d).choose d * (d.factorial * x.factorial)
        = (x + d).choose d * d.factorial * x.factorial := by ring
      _ = (x + d).factorial := this
  have hy : (y + d).choose d * (d.factorial * y.factorial) = (y + d).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show d ≤ y + d by omega)
    rw [show y + d - d = y from by omega] at this
    calc (y + d).choose d * (d.factorial * y.factorial)
        = (y + d).choose d * d.factorial * y.factorial := by ring
      _ = (y + d).factorial := this
  have hchoose : (x + d).choose d ≤ (y + d).choose d :=
    Nat.choose_le_choose d (by omega)
  calc (x + d).factorial * y.factorial
      = (x + d).choose d * (d.factorial * x.factorial * y.factorial) := by rw [← hx]; ring
    _ ≤ (y + d).choose d * (d.factorial * x.factorial * y.factorial) :=
        Nat.mul_le_mul_right _ hchoose
    _ = (y + d).choose d * (d.factorial * y.factorial) * x.factorial := by ring
    _ = (y + d).factorial * x.factorial := by rw [hy]

end AlgebraicComplexity.Analysis
