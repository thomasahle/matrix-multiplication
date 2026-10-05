/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.Combinatorics.MappedType
import AlgebraicComplexity.Probability.Finite
import Mathlib.Algebra.BigOperators.Field

/-!
# Integral profiles as finite probability vectors

This module normalizes nonzero integral profiles and proves the elementary pushforward and scaling
identities.  It deliberately does not import entropy, KL divergence, multinomial estimates, or
asymptotic counting.  Semantic profile clients should prefer this module to `IntegralProfileCore`.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

variable {I : Type u} [Fintype I]

/-- Normalize an arbitrary nonzero integral profile to a finite probability vector. -/
noncomputable def normalizedProfileProbability
    (a : I → ℕ) (hmass : 0 < profileMass a) : ProbabilityVector I where
  weight i := (a i : ℝ) / (profileMass a : ℝ)
  nonneg i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div]
    have hsum : (∑ i, (a i : ℝ)) = (profileMass a : ℝ) := by
      exact_mod_cast (rfl : (∑ i, a i) = profileMass a)
    rw [hsum, div_self]
    exact_mod_cast hmass.ne'

@[simp] theorem normalizedProfileProbability_weight
    (a : I → ℕ) (hmass : 0 < profileMass a) (i : I) :
    (normalizedProfileProbability a hmass).weight i =
      (a i : ℝ) / (profileMass a : ℝ) :=
  rfl

/-- A pushforward coordinate of the normalized empirical distribution is the normalized mapped
integral profile. -/
theorem normalizedProfileProbability_pushforward_weight
    {J : Type v} [Fintype J] [DecidableEq J]
    (a : I → ℕ) (hmass : 0 < profileMass a) (coordinate : I → J) (j : J) :
    ((normalizedProfileProbability a hmass).pushforward coordinate).weight j =
      (mappedType coordinate a j : ℝ) / (profileMass a : ℝ) := by
  rw [ProbabilityVector.pushforward_weight]
  unfold mappedType letterFiber
  rw [Finset.sum_filter]
  have hterm (i : I) :
      (if coordinate i = j then
          (normalizedProfileProbability a hmass).weight i else 0) =
        (if coordinate i = j then (a i : ℝ) else 0) /
          (profileMass a : ℝ) := by
    by_cases h : coordinate i = j <;>
      simp [h, normalizedProfileProbability_weight]
  simp_rw [hterm]
  rw [← Finset.sum_div]
  congr 1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : coordinate i = j <;> simp [h]

/-- Scaling every integral count by a positive factor leaves the normalized empirical law
unchanged. -/
theorem normalizedProfileProbability_proportionalCounts
    (a : I → ℕ) (hmass : 0 < profileMass a)
    {k : ℕ} (hk : 0 < k) :
    normalizedProfileProbability (proportionalCounts a k) (by
      simpa [profileMass, proportionalCounts, Finset.sum_mul] using
        Nat.mul_pos hmass hk) =
      normalizedProfileProbability a hmass := by
  apply ProbabilityVector.ext
  funext i
  simp only [normalizedProfileProbability_weight, proportionalCounts]
  have hscaledMass : profileMass (fun i ↦ a i * k) = profileMass a * k := by
    simp [profileMass, Finset.sum_mul]
  change ((a i * k : ℕ) : ℝ) /
      (profileMass (fun j ↦ a j * k) : ℝ) =
    (a i : ℝ) / (profileMass a : ℝ)
  rw [hscaledMass, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne')

end AlgebraicComplexity.WordType
