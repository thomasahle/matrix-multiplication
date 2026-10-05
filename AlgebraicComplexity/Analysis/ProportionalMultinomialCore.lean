/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.FactorialEntropyBounds
import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Probability.IntegralProfileCore
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Core proportional multinomial estimates on arbitrary finite alphabets

For a fixed positive integer profile `a : I → ℕ`, the multinomial coefficient of the
scaled profile `k ⋅ a` has the Shannon-entropy exponential base, up to an explicit polynomial
loss of degree `|I|`.  This is the finite-alphabet method-of-types estimate needed by recursive
laser-method arguments.  The theorem is stated for an arbitrary finite alphabet and uses no
ordering of that alphabet.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

universe u

variable {I : Type u} [Fintype I]

/-- The exponential part of Stirling's formula for one factorial. -/
noncomputable def factorialEntropyTerm (d : ℕ) : ℝ :=
  (((d : ℝ) / Real.exp 1) ^ d)

/-- Exponential growth base of the multinomial coefficients of the proportional profile `k ⋅ a`. -/
noncomputable def proportionalEntropyBase (a : I → ℕ) : ℝ :=
  factorialEntropyTerm (profileMass a) /
    ∏ i, factorialEntropyTerm (a i)

/-- Explicit polynomial loss in the lower method-of-types estimate. -/
noncomputable def proportionalMultinomialLoss (a : I → ℕ) (k : ℕ) : ℝ :=
  (Real.exp 1) ^ Fintype.card I * (∏ i, (a i : ℝ)) *
    (k : ℝ) ^ Fintype.card I

/-- Explicit linear loss in the upper method-of-types estimate. -/
noncomputable def proportionalMultinomialUpperLoss (a : I → ℕ) (k : ℕ) : ℝ :=
  Real.exp 1 * (profileMass a : ℝ) * (k : ℝ)

/-- The method-of-types loss for a fixed profile is subexponential in the repetition count. -/
theorem proportionalMultinomialLoss_subexponential (a : I → ℕ) :
    AlgebraicComplexity.Growth.Subexponential
      (proportionalMultinomialLoss a) := by
  have hconst :
      0 ≤ (Real.exp 1) ^ Fintype.card I * (∏ i, (a i : ℝ)) := by
    positivity
  convert AlgebraicComplexity.Growth.Subexponential.const_mul
      (AlgebraicComplexity.Growth.Subexponential.natCast_pow (Fintype.card I)) hconst using 1
  funext n
  unfold proportionalMultinomialLoss
  ring

/-- The upper method-of-types loss for a fixed profile is subexponential. -/
theorem proportionalMultinomialUpperLoss_subexponential (a : I → ℕ) :
    AlgebraicComplexity.Growth.Subexponential
      (proportionalMultinomialUpperLoss a) := by
  have hconst : 0 ≤ Real.exp 1 * (profileMass a : ℝ) := by
    positivity
  convert AlgebraicComplexity.Growth.Subexponential.const_mul
      (AlgebraicComplexity.Growth.Subexponential.natCast_pow 1) hconst using 1
  funext n
  unfold proportionalMultinomialUpperLoss
  ring

/-- Division-free factorial specification of a proportional multinomial coefficient. -/
theorem proportionalMultinomial_spec (a : I → ℕ) (k : ℕ) :
    (∏ i, (proportionalCounts a k i).factorial) *
        Nat.multinomial Finset.univ (proportionalCounts a k) =
      (profileMass a * k).factorial := by
  have h := Nat.multinomial_spec (Finset.univ : Finset I) (proportionalCounts a k)
  simpa only [proportionalCounts, profileMass, Finset.sum_mul] using h

private theorem factorialEntropyTerm_mul (d k : ℕ) :
    factorialEntropyTerm (d * k) =
      (((k : ℝ) ^ d * factorialEntropyTerm d) : ℝ) ^ k := by
  unfold factorialEntropyTerm
  push_cast
  rw [pow_mul]
  congr 1
  rw [show (d : ℝ) * (k : ℝ) / Real.exp 1 =
      (k : ℝ) * ((d : ℝ) / Real.exp 1) by ring, mul_pow]

/-- The Stirling exponential term is positive, including at multiplicity zero. -/
theorem factorialEntropyTerm_pos_zeroSafe (d : ℕ) :
    0 < factorialEntropyTerm d := by
  cases d with
  | zero => simp [factorialEntropyTerm]
  | succ d =>
      unfold factorialEntropyTerm
      positivity

private theorem factorialEntropyTerm_pos (d : ℕ) :
    0 < factorialEntropyTerm d :=
  factorialEntropyTerm_pos_zeroSafe d

/-- The logarithm/entropy identity for an arbitrary nonzero integral profile.  Unlike
`log_proportionalEntropyBase`, this statement permits structural zeroes. -/
theorem log_proportionalEntropyBase_of_profileMass_pos
    (a : I → ℕ) (hmass : 0 < profileMass a) :
    Real.log (proportionalEntropyBase a) =
      (profileMass a : ℝ) * profileEntropyNats a := by
  classical
  have hmassReal : (0 : ℝ) < profileMass a := by exact_mod_cast hmass
  have hsum : (∑ i, (a i : ℝ)) = (profileMass a : ℝ) := by
    exact_mod_cast (rfl : (∑ i, a i) = profileMass a)
  have hlogTerm (d : ℕ) :
      Real.log (factorialEntropyTerm d) =
        (d : ℝ) * (Real.log d - 1) := by
    cases d with
    | zero => simp [factorialEntropyTerm]
    | succ d =>
        unfold factorialEntropyTerm
        rw [Real.log_pow, Real.log_div (by positivity) (Real.exp_ne_zero 1),
          Real.log_exp]
  have hdenNe : (∏ i, factorialEntropyTerm (a i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (factorialEntropyTerm_pos_zeroSafe (a i)).ne'
  have hlogDen :
      Real.log (∏ i, factorialEntropyTerm (a i)) =
        ∑ i, (a i : ℝ) * (Real.log (a i) - 1) := by
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      exact hlogTerm (a i)
    · intro i _
      exact (factorialEntropyTerm_pos_zeroSafe (a i)).ne'
  have hentropyTerm (i : I) :
      (profileMass a : ℝ) *
          Real.negMulLog ((a i : ℝ) / (profileMass a : ℝ)) =
        (a i : ℝ) * (Real.log (profileMass a) - Real.log (a i)) := by
    by_cases hai : a i = 0
    · simp [hai, Real.negMulLog]
    · have haiPos : 0 < a i := Nat.pos_of_ne_zero hai
      rw [Real.negMulLog_eq_neg]
      change (profileMass a : ℝ) *
          (-(((a i : ℝ) / (profileMass a : ℝ)) *
            Real.log ((a i : ℝ) / (profileMass a : ℝ)))) =
        (a i : ℝ) * (Real.log (profileMass a) - Real.log (a i))
      rw [Real.log_div (show (a i : ℝ) ≠ 0 by exact_mod_cast hai)
        hmassReal.ne']
      field_simp [hmassReal.ne']
      ring
  have hdenExpand :
      (∑ i, (a i : ℝ) * (Real.log (a i) - 1)) =
        (∑ i, (a i : ℝ) * Real.log (a i)) - (profileMass a : ℝ) := by
    calc
      (∑ i, (a i : ℝ) * (Real.log (a i) - 1)) =
          ∑ i, ((a i : ℝ) * Real.log (a i) - (a i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (a i : ℝ) * Real.log (a i)) -
          ∑ i, (a i : ℝ) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i, (a i : ℝ) * Real.log (a i)) - (profileMass a : ℝ) := by
        rw [hsum]
  have hrhsExpand :
      (∑ i, (a i : ℝ) *
          (Real.log (profileMass a) - Real.log (a i))) =
        (profileMass a : ℝ) * Real.log (profileMass a) -
          ∑ i, (a i : ℝ) * Real.log (a i) := by
    calc
      (∑ i, (a i : ℝ) *
          (Real.log (profileMass a) - Real.log (a i))) =
          ∑ i, ((a i : ℝ) * Real.log (profileMass a) -
            (a i : ℝ) * Real.log (a i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (a i : ℝ) * Real.log (profileMass a)) -
          ∑ i, (a i : ℝ) * Real.log (a i) := by
        rw [Finset.sum_sub_distrib]
      _ = (profileMass a : ℝ) * Real.log (profileMass a) -
          ∑ i, (a i : ℝ) * Real.log (a i) := by
        rw [← Finset.sum_mul, hsum]
  unfold proportionalEntropyBase profileEntropyNats
  rw [Real.log_div (factorialEntropyTerm_pos_zeroSafe (profileMass a)).ne' hdenNe,
    hlogTerm (profileMass a), hlogDen, Finset.mul_sum]
  simp_rw [hentropyTerm]
  rw [hdenExpand, hrhsExpand]
  ring

/-- The logarithm of the proportional multinomial base is the total profile mass times Shannon
entropy.  This is the analytic bridge from the exact finite count to the usual entropy exponent. -/
theorem log_proportionalEntropyBase [Nonempty I]
    (a : I → ℕ) (ha : ∀ i, 0 < a i) :
    Real.log (proportionalEntropyBase a) =
      (profileMass a : ℝ) * profileEntropyNats a := by
  refine log_proportionalEntropyBase_of_profileMass_pos a ?_
  unfold profileMass
  exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty

private theorem prod_factorialEntropyTerm_mul (a : I → ℕ) (k : ℕ) :
    (∏ i, factorialEntropyTerm (a i * k)) =
      (((k : ℝ) ^ profileMass a * ∏ i, factorialEntropyTerm (a i)) : ℝ) ^ k := by
  classical
  calc
    (∏ i, factorialEntropyTerm (a i * k)) =
        ∏ i, (((k : ℝ) ^ a i * factorialEntropyTerm (a i)) : ℝ) ^ k := by
      apply Finset.prod_congr rfl
      intro i _
      exact factorialEntropyTerm_mul (a i) k
    _ = (∏ i, ((k : ℝ) ^ a i * factorialEntropyTerm (a i))) ^ k := by
      rw [Finset.prod_pow]
    _ = (((k : ℝ) ^ profileMass a * ∏ i, factorialEntropyTerm (a i)) : ℝ) ^ k := by
      congr 1
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rfl

/-- Scaling all multiplicities by `k` raises their normalized entropy ratio to the `k`th power. -/
theorem proportionalEntropyBase_mul_scaled_terms (a : I → ℕ) (k : ℕ) :
    proportionalEntropyBase a ^ k *
        (∏ i, factorialEntropyTerm (a i * k)) =
      factorialEntropyTerm (profileMass a * k) := by
  classical
  rw [prod_factorialEntropyTerm_mul, factorialEntropyTerm_mul, ← mul_pow]
  congr 1
  unfold proportionalEntropyBase
  have hden : (∏ i, factorialEntropyTerm (a i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (factorialEntropyTerm_pos (a i)).ne'
  field_simp

private theorem prod_factorial_upper (a : I → ℕ) (k : ℕ)
    (ha : ∀ i, 0 < a i) (hk : 0 < k) :
    (∏ i, (((a i * k).factorial : ℕ) : ℝ)) ≤
      ∏ i, Real.exp 1 * ((a i * k : ℕ) : ℝ) *
        factorialEntropyTerm (a i * k) := by
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    simpa only [factorialEntropyTerm] using
      factorial_le_exp_mul_self_mul (Nat.mul_pos (ha i) hk)

private theorem prod_factorial_upper_eq_loss (a : I → ℕ) (k : ℕ) :
    (∏ i, Real.exp 1 * ((a i * k : ℕ) : ℝ) *
        factorialEntropyTerm (a i * k)) =
      proportionalMultinomialLoss a k *
        ∏ i, factorialEntropyTerm (a i * k) := by
  classical
  have hterms :
      (∏ i, factorialEntropyTerm (a i * k)) =
        ∏ i, factorialEntropyTerm (k * a i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.mul_comm]
  simp_rw [Nat.cast_mul]
  unfold proportionalMultinomialLoss
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hterms]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

/-- A fixed positive finite-alphabet type has its entropy growth base up to an explicit
`|I|`-degree polynomial loss. -/
theorem proportionalEntropyBase_pow_le_loss_mul_multinomial [Nonempty I]
    (a : I → ℕ) (k : ℕ) (ha : ∀ i, 0 < a i) (hk : 0 < k) :
    proportionalEntropyBase a ^ k ≤
      proportionalMultinomialLoss a k *
        (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := by
  classical
  have hmass : 0 < profileMass a := by
    unfold profileMass
    exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hspec :
      (∏ i, (((a i * k).factorial : ℕ) : ℝ)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) =
        (((profileMass a * k).factorial : ℕ) : ℝ) := by
    exact_mod_cast proportionalMultinomial_spec a k
  have hterms : 0 < ∏ i, factorialEntropyTerm (a i * k) := by
    exact Finset.prod_pos fun i _ ↦ factorialEntropyTerm_pos (a i * k)
  have hraw :
      proportionalEntropyBase a ^ k *
          (∏ i, factorialEntropyTerm (a i * k)) ≤
        (proportionalMultinomialLoss a k *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ)) *
            (∏ i, factorialEntropyTerm (a i * k)) := by
    calc
      proportionalEntropyBase a ^ k *
          (∏ i, factorialEntropyTerm (a i * k)) =
          factorialEntropyTerm (profileMass a * k) :=
        proportionalEntropyBase_mul_scaled_terms a k
      _ ≤ (((profileMass a * k).factorial : ℕ) : ℝ) := by
        simpa only [factorialEntropyTerm] using
          pow_div_exp_le_factorial (Nat.mul_pos hmass hk)
      _ = (∏ i, (((a i * k).factorial : ℕ) : ℝ)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := hspec.symm
      _ ≤ (∏ i, Real.exp 1 * ((a i * k : ℕ) : ℝ) *
            factorialEntropyTerm (a i * k)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (prod_factorial_upper a k ha hk) (by positivity)
      _ = (proportionalMultinomialLoss a k *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ)) *
            (∏ i, factorialEntropyTerm (a i * k)) := by
        rw [prod_factorial_upper_eq_loss]
        ring
  exact le_of_mul_le_mul_right hraw hterms

private theorem prod_factorialEntropyTerm_le_factorial (a : I → ℕ) (k : ℕ)
    (ha : ∀ i, 0 < a i) (hk : 0 < k) :
    (∏ i, factorialEntropyTerm (a i * k)) ≤
      ∏ i, (((a i * k).factorial : ℕ) : ℝ) := by
  apply Finset.prod_le_prod
  · intro i _
    exact (factorialEntropyTerm_pos (a i * k)).le
  · intro i _
    simpa only [factorialEntropyTerm] using
      pow_div_exp_le_factorial (Nat.mul_pos (ha i) hk)

/-- A matching upper method-of-types estimate.  Together with
`proportionalEntropyBase_pow_le_loss_mul_multinomial`, this sandwiches every fixed positive
finite-alphabet type class between the same entropy base and explicit polynomial factors. -/
theorem multinomial_le_upperLoss_mul_proportionalEntropyBase_pow [Nonempty I]
    (a : I → ℕ) (k : ℕ) (ha : ∀ i, 0 < a i) (hk : 0 < k) :
    (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) ≤
      proportionalMultinomialUpperLoss a k * proportionalEntropyBase a ^ k := by
  classical
  have hmass : 0 < profileMass a := by
    unfold profileMass
    exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hspec :
      (∏ i, (((a i * k).factorial : ℕ) : ℝ)) *
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) =
        (((profileMass a * k).factorial : ℕ) : ℝ) := by
    exact_mod_cast proportionalMultinomial_spec a k
  have hterms : 0 < ∏ i, factorialEntropyTerm (a i * k) := by
    exact Finset.prod_pos fun i _ ↦ factorialEntropyTerm_pos (a i * k)
  have hraw :
      (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) *
          (∏ i, factorialEntropyTerm (a i * k)) ≤
        (proportionalMultinomialUpperLoss a k * proportionalEntropyBase a ^ k) *
          (∏ i, factorialEntropyTerm (a i * k)) := by
    calc
      (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) *
          (∏ i, factorialEntropyTerm (a i * k)) ≤
          (Nat.multinomial Finset.univ (proportionalCounts a k) : ℝ) *
            (∏ i, (((a i * k).factorial : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (prod_factorialEntropyTerm_le_factorial a k ha hk) (by positivity)
      _ = (((profileMass a * k).factorial : ℕ) : ℝ) := by
        rw [mul_comm]
        exact hspec
      _ ≤ Real.exp 1 * (((profileMass a * k : ℕ) : ℝ)) *
          factorialEntropyTerm (profileMass a * k) := by
        simpa only [factorialEntropyTerm] using
          factorial_le_exp_mul_self_mul (Nat.mul_pos hmass hk)
      _ = (proportionalMultinomialUpperLoss a k * proportionalEntropyBase a ^ k) *
          (∏ i, factorialEntropyTerm (a i * k)) := by
        rw [← proportionalEntropyBase_mul_scaled_terms a k]
        unfold proportionalMultinomialUpperLoss
        push_cast
        ring
  exact le_of_mul_le_mul_right hraw hterms

end AlgebraicComplexity.WordType
