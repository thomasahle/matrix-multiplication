/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BinomialEntropyEnvelope
import AlgebraicComplexity.Analysis.FactorialEntropyBounds
import AlgebraicComplexity.Analysis.Subexponential
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Proportional ternary multinomial estimates

The method of types needs a lower bound for the word class whose three multiplicities are
`a * k`, `b * k`, and `c * k`.  This module proves the exact entropy base up to an explicit cubic
loss.  The result is independent of tensors and named laser-method constructions.

The proof uses Mathlib's global Stirling bounds.  Keeping the loss explicit makes the finite
hashing theorem usable directly; `ternaryMultinomialLoss_subexponential` then removes it at the
rate level.

`ternaryEntropyBase_right_zero` identifies the two-letter specialization of `ternaryEntropyBase`
with the `binomialEntropyBase` of `Analysis/BinomialEntropyEnvelope.lean`, so the two entropy
formulas are one.  The arbitrary-alphabet `proportionalEntropyBase` of
`Analysis/ProportionalMultinomial.lean` is still a third copy; unifying it is left
open.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

/-- A three-letter multiplicity vector in documented coordinate order. -/
def ternaryCounts (a b c : ℕ) : Fin 3 → ℕ
  | 0 => a
  | 1 => b
  | 2 => c

/-- Multinomial coefficient for three displayed multiplicities. -/
def ternaryMultinomial (a b c : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (ternaryCounts a b c)

/-- Division-free factorial specification of `ternaryMultinomial`. -/
theorem ternaryMultinomial_spec (a b c : ℕ) :
    a.factorial * b.factorial * c.factorial * ternaryMultinomial a b c =
      (a + b + c).factorial := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin 3)) (ternaryCounts a b c)
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [huniv] at h
  unfold ternaryMultinomial
  rw [huniv]
  simpa [ternaryCounts, add_assoc, mul_assoc] using h

/-- Exponential growth base of the proportional type `(a*k,b*k,c*k)`.  The factors of `e`
cancel mathematically but are retained so the Stirling proof remains syntactically direct. -/
noncomputable def ternaryEntropyBase (a b c : ℕ) : ℝ :=
  ((((a + b + c : ℕ) : ℝ) / Real.exp 1) ^ (a + b + c)) /
    ((((a : ℝ) / Real.exp 1) ^ a) *
      (((b : ℝ) / Real.exp 1) ^ b) *
      (((c : ℝ) / Real.exp 1) ^ c))

/-- **The two-letter envelope base is the three-letter base with an empty third letter.**

`Analysis/BinomialEntropyEnvelope.lean` introduces `binomialEntropyBase p m = (p+m)^{p+m} /
(p^p m^m)` for the loss-free binomial envelope, and this file introduces `ternaryEntropyBase` in
the Stirling form that keeps the cancelling factors of `e`.  They are the same function of a
type profile, and this lemma says so; in particular `log_binomialEntropyBase` and
`log_ternaryEntropyBase` are interderivable rather than two independent entropy formulas. -/
theorem ternaryEntropyBase_right_zero (p m : ℕ) :
    ternaryEntropyBase p m 0 = Analysis.binomialEntropyBase p m := by
  have hp : (0 : ℝ) < (p : ℝ) ^ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · simp [h]
    · exact pow_pos (by exact_mod_cast h) p
  have hm : (0 : ℝ) < (m : ℝ) ^ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact pow_pos (by exact_mod_cast h) m
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold ternaryEntropyBase Analysis.binomialEntropyBase
  simp only [Nat.add_zero, Nat.cast_zero, div_pow, pow_zero, mul_one]
  rw [pow_add]
  field_simp
  ring

/-- The logarithm of the ternary entropy base is total mass times Shannon entropy (in nats).
This is the analytic bridge from exact proportional multinomial estimates to entropy formulas. -/
theorem log_ternaryEntropyBase (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (ternaryEntropyBase a b c) =
      ((a + b + c : ℕ) : ℝ) *
        (Real.negMulLog ((a : ℝ) / (a + b + c : ℕ)) +
          Real.negMulLog ((b : ℝ) / (a + b + c : ℕ)) +
          Real.negMulLog ((c : ℝ) / (a + b + c : ℕ))) := by
  have hsum : 0 < a + b + c := by omega
  have hterm (d : ℕ) (hd : 0 < d) :
      Real.log ((((d : ℝ) / Real.exp 1) ^ d)) =
        (d : ℝ) * (Real.log d - 1) := by
    rw [Real.log_pow, Real.log_div (by positivity) (Real.exp_ne_zero 1),
      Real.log_exp]
  have hden :
      Real.log (((((a : ℝ) / Real.exp 1) ^ a) *
          (((b : ℝ) / Real.exp 1) ^ b) *
          (((c : ℝ) / Real.exp 1) ^ c))) =
        (a : ℝ) * (Real.log a - 1) +
          (b : ℝ) * (Real.log b - 1) +
          (c : ℝ) * (Real.log c - 1) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      hterm a ha, hterm b hb, hterm c hc]
  unfold ternaryEntropyBase
  rw [Real.log_div (by positivity) (by positivity), hterm (a + b + c) hsum, hden]
  simp only [Real.negMulLog_eq_neg]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  push_cast
  have hsumReal : (0 : ℝ) < (a : ℝ) + b + c := by exact_mod_cast hsum
  field_simp [hsumReal.ne']
  ring

/-- Cubic Stirling loss for a fixed positive ternary multiplicity profile. -/
noncomputable def ternaryMultinomialLoss (a b c : ℕ) (k : ℕ) : ℝ :=
  (Real.exp 1) ^ 3 * ((a * b * c : ℕ) : ℝ) * (k : ℝ) ^ 3

/-- The explicit ternary Stirling loss is subexponential in the replication parameter. -/
theorem ternaryMultinomialLoss_subexponential (a b c : ℕ) :
    AlgebraicComplexity.Growth.Subexponential
      (ternaryMultinomialLoss a b c) := by
  unfold ternaryMultinomialLoss
  apply AlgebraicComplexity.Growth.Subexponential.const_mul
    (AlgebraicComplexity.Growth.Subexponential.natCast_pow 3)
  positivity

private theorem proportionalPow_term (d k : ℕ) :
    ((((d * k : ℕ) : ℝ) / Real.exp 1) ^ (d * k)) =
      (((k : ℝ) ^ d * (((d : ℝ) / Real.exp 1) ^ d) : ℝ) ^ k) := by
  push_cast
  rw [pow_mul]
  congr 1
  rw [show (d : ℝ) * (k : ℝ) / Real.exp 1 =
      (k : ℝ) * ((d : ℝ) / Real.exp 1) by ring, mul_pow]

/-- Scaling all three multiplicities by `k` raises their normalized entropy ratio to the `k`th
power. -/
theorem ternaryEntropyBase_mul_scaled_terms
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ternaryEntropyBase a b c ^ k *
        ((((a * k : ℕ) : ℝ) / Real.exp 1) ^ (a * k) *
          (((b * k : ℕ) : ℝ) / Real.exp 1) ^ (b * k) *
          (((c * k : ℕ) : ℝ) / Real.exp 1) ^ (c * k)) =
      ((((a + b + c) * k : ℕ) : ℝ) / Real.exp 1) ^
        ((a + b + c) * k) := by
  rw [proportionalPow_term a k, proportionalPow_term b k,
    proportionalPow_term c k, proportionalPow_term (a + b + c) k]
  rw [← mul_pow, ← mul_pow, ← mul_pow]
  congr 1
  unfold ternaryEntropyBase
  have ha' : ((a : ℝ) / Real.exp 1) ^ a ≠ 0 := by positivity
  have hb' : ((b : ℝ) / Real.exp 1) ^ b ≠ 0 := by positivity
  have hc' : ((c : ℝ) / Real.exp 1) ^ c ≠ 0 := by positivity
  rw [show (k : ℝ) ^ (a + b + c) =
      (k : ℝ) ^ a * (k : ℝ) ^ b * (k : ℝ) ^ c by
        rw [pow_add, pow_add]]
  field_simp

/-- A fixed positive ternary type has its entropy growth base up to the explicit cubic loss. -/
theorem ternaryEntropyBase_pow_le_cubic_mul_multinomial
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k) :
    ternaryEntropyBase a b c ^ k ≤
      ternaryMultinomialLoss a b c k *
        (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ) := by
  let ta : ℝ := (((a * k : ℕ) : ℝ) / Real.exp 1) ^ (a * k)
  let tb : ℝ := (((b * k : ℕ) : ℝ) / Real.exp 1) ^ (b * k)
  let tc : ℝ := (((c * k : ℕ) : ℝ) / Real.exp 1) ^ (c * k)
  have hta : 0 < ta := by dsimp [ta]; positivity
  have htb : 0 < tb := by dsimp [tb]; positivity
  have htc : 0 < tc := by dsimp [tc]; positivity
  have hspec :
      (((a * k).factorial : ℕ) : ℝ) * (((b * k).factorial : ℕ) : ℝ) *
          (((c * k).factorial : ℕ) : ℝ) *
          (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ) =
        ((((a + b + c) * k).factorial : ℕ) : ℝ) := by
    have h := ternaryMultinomial_spec (a * k) (b * k) (c * k)
    rw [show a * k + b * k + c * k = (a + b + c) * k by ring] at h
    exact_mod_cast h
  have hfa := factorial_le_exp_mul_self_mul (Nat.mul_pos ha hk)
  have hfb := factorial_le_exp_mul_self_mul (Nat.mul_pos hb hk)
  have hfc := factorial_le_exp_mul_self_mul (Nat.mul_pos hc hk)
  have hraw :
      ternaryEntropyBase a b c ^ k * (ta * tb * tc) ≤
        (ternaryMultinomialLoss a b c k *
          (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ)) *
            (ta * tb * tc) := by
    calc
      ternaryEntropyBase a b c ^ k * (ta * tb * tc) =
          ((((a + b + c) * k : ℕ) : ℝ) / Real.exp 1) ^
            ((a + b + c) * k) := by
        exact ternaryEntropyBase_mul_scaled_terms a b c k ha hb hc
      _ ≤ ((((a + b + c) * k).factorial : ℕ) : ℝ) :=
        pow_div_exp_le_factorial (by positivity)
      _ = (((a * k).factorial : ℕ) : ℝ) * (((b * k).factorial : ℕ) : ℝ) *
          (((c * k).factorial : ℕ) : ℝ) *
          (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ) := hspec.symm
      _ ≤ (Real.exp 1 * ((a * k : ℕ) : ℝ) * ta) *
          (Real.exp 1 * ((b * k : ℕ) : ℝ) * tb) *
          (Real.exp 1 * ((c * k : ℕ) : ℝ) * tc) *
          (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ) := by
        gcongr
      _ = (ternaryMultinomialLoss a b c k *
          (ternaryMultinomial (a * k) (b * k) (c * k) : ℝ)) *
            (ta * tb * tc) := by
        dsimp [ta, tb, tc, ternaryMultinomialLoss] at hfa hfb hfc ⊢
        push_cast
        ring
  exact le_of_mul_le_mul_right hraw (mul_pos (mul_pos hta htb) htc)

end AlgebraicComplexity.WordType
