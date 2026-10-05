/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.StructuralZeroEntropyIdentity
import AlgebraicComplexity.Combinatorics.WordType

/-! # Structural-zero multinomial upper bound -/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

universe u

variable {I : Type u} [Fintype I]

/-- Each empirical probability factor is positive after being raised to its own count: zero
probabilities occur only with exponent zero. -/
private theorem empiricalProbability_pow_pos
    (a : I → ℕ) (hmass : 0 < profileMass a) (i : I) :
    0 < (((a i : ℝ) / (profileMass a : ℝ)) ^ a i) := by
  by_cases hai : a i = 0
  · simp [hai]
  · exact pow_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hai)
      (by exact_mod_cast hmass)) _

/-- Exact method-of-types upper bound, valid with arbitrary structural zeroes. -/
theorem multinomial_le_exp_profileEntropy
    (a : I → ℕ) (hmass : 0 < profileMass a) :
    (Nat.multinomial Finset.univ a : ℝ) ≤
      Real.exp ((profileMass a : ℝ) * profileEntropyNats a) := by
  classical
  let p : I → ℝ := fun i ↦ (a i : ℝ) / (profileMass a : ℝ)
  have hmassRealNe : (profileMass a : ℝ) ≠ 0 := by exact_mod_cast hmass.ne'
  have hsum : ∑ i, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div]
    have hcast : (∑ i, (a i : ℝ)) = (profileMass a : ℝ) := by
      exact_mod_cast (rfl : (∑ i, a i) = profileMass a)
    rw [hcast, div_self hmassRealNe]
  have haType : a ∈ types I (profileMass a) := by
    rw [mem_types]
    rfl
  have hterm :
      (Nat.multinomial Finset.univ a : ℝ) * ∏ i, p i ^ a i ≤ 1 := by
    have hsingle :
        (Nat.multinomial Finset.univ a : ℝ) * ∏ i, p i ^ a i ≤
          ∑ jointType ∈ Finset.piAntidiag Finset.univ (profileMass a),
            (Nat.multinomial Finset.univ jointType : ℝ) *
              ∏ i, p i ^ jointType i := by
      apply Finset.single_le_sum
        (f := fun jointType : I → ℕ ↦
          (Nat.multinomial Finset.univ jointType : ℝ) *
            ∏ i, p i ^ jointType i)
        (s := Finset.piAntidiag Finset.univ (profileMass a))
      · intro jointType hjointType
        positivity
      · simpa [types] using haType
    calc
      _ ≤ ∑ jointType ∈ Finset.piAntidiag Finset.univ (profileMass a),
          (Nat.multinomial Finset.univ jointType : ℝ) *
            ∏ i, p i ^ jointType i := hsingle
      _ = (∑ i, p i) ^ profileMass a := by
        symm
        simpa using Finset.sum_pow_eq_sum_piAntidiag
          (Finset.univ : Finset I) p (profileMass a)
      _ = 1 := by rw [hsum, one_pow]
  have hprodPos : 0 < ∏ i, p i ^ a i := by
    exact Finset.prod_pos fun i _ ↦ empiricalProbability_pow_pos a hmass i
  have hlogProduct :
      Real.log (∏ i, p i ^ a i) =
        -((profileMass a : ℝ) * profileEntropyNats a) := by
    rw [Real.log_prod (fun i _ ↦ (empiricalProbability_pow_pos a hmass i).ne')]
    simp_rw [Real.log_pow]
    unfold profileEntropyNats
    change (∑ i, (a i : ℝ) * Real.log (p i)) =
      -((profileMass a : ℝ) * ∑ i, Real.negMulLog (p i))
    calc
      (∑ i, (a i : ℝ) * Real.log (p i)) =
          ∑ i, -((profileMass a : ℝ) * Real.negMulLog (p i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.negMulLog_eq_neg]
        dsimp [p]
        field_simp [hmassRealNe]
      _ = -(∑ i, (profileMass a : ℝ) * Real.negMulLog (p i)) := by
        rw [Finset.sum_neg_distrib]
      _ = -((profileMass a : ℝ) * ∑ i, Real.negMulLog (p i)) := by
        congr 1
        rw [Finset.mul_sum]
  have hprodExp :
      (∏ i, p i ^ a i) =
        Real.exp (-((profileMass a : ℝ) * profileEntropyNats a)) := by
    rw [← hlogProduct, Real.exp_log hprodPos]
  let entropyExponent : ℝ := (profileMass a : ℝ) * profileEntropyNats a
  have hcancel :
      Real.exp entropyExponent * (∏ i, p i ^ a i) = 1 := by
    rw [hprodExp, ← Real.exp_add]
    simp [entropyExponent]
  calc
    (Nat.multinomial Finset.univ a : ℝ) =
        (Nat.multinomial Finset.univ a : ℝ) *
          (Real.exp entropyExponent * ∏ i, p i ^ a i) := by rw [hcancel, mul_one]
    _ = Real.exp entropyExponent *
        ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, p i ^ a i) := by ring
    _ ≤ Real.exp entropyExponent * 1 :=
      mul_le_mul_of_nonneg_left hterm (Real.exp_nonneg _)
    _ = Real.exp ((profileMass a : ℝ) * profileEntropyNats a) := by
      simp [entropyExponent]

end AlgebraicComplexity.WordType
