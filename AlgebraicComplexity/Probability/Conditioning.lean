/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Pushforward
import Mathlib.Algebra.BigOperators.Field

/-!
# Conditioning finite probability vectors on deterministic fibers

This file supplies a zero-safe conditional law for the repository's elementary finite
`ProbabilityVector` API.  Given a law `p : ProbabilityVector I` and a finite label
`label : I → K`, `p.conditionOnFiber label k` normalizes the mass in the fiber over `k` whenever
that fiber has positive mass.  A zero-mass fiber is assigned an arbitrary point mass; its choice
is semantically irrelevant because the corresponding outer mixture coefficient is zero.

The main theorem, `mixture_conditionOnFiber`, reconstructs `p` exactly as the mixture of these
conditional laws under `p.pushforward label`.  This is the finite disintegration identity needed
to reveal an exceptional event in entropy arguments, without imposing full support or hiding a
division-by-zero premise.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {I : Type u} {K : Type v}
variable [Fintype I] [Nonempty I] [Fintype K] [DecidableEq K]

/-- The conditional law of `p` on one deterministic fiber.

When the fiber has zero `p`-mass, the definition uses an arbitrary point mass.  This convention
makes conditioning total while leaving every mixture reconstruction independent of the fallback.
-/
noncomputable def conditionOnFiber
    (p : ProbabilityVector I) (label : I → K) (k : K) : ProbabilityVector I := by
  classical
  by_cases hk : (p.pushforward label).weight k = 0
  · exact pointMass (Classical.choice (inferInstance : Nonempty I))
  · exact
      { weight := fun i ↦
          if label i = k then p.weight i / (p.pushforward label).weight k else 0
        nonneg := fun i ↦ by
          by_cases hi : label i = k
          · simp only [hi, if_pos]
            exact div_nonneg (p.nonneg i) ((p.pushforward label).nonneg k)
          · simp [hi]
        total := by
          calc
            (∑ i, if label i = k then
                p.weight i / (p.pushforward label).weight k else 0) =
                (∑ i, if label i = k then p.weight i else 0) /
                  (p.pushforward label).weight k := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : label i = k <;> simp [hi]
            _ = (p.pushforward label).weight k / (p.pushforward label).weight k := by
              rfl
            _ = 1 := div_self hk }

/-- A zero-mass fiber uses the documented point-mass fallback. -/
@[simp] theorem conditionOnFiber_eq_pointMass_of_weight_eq_zero
    [DecidableEq I]
    (p : ProbabilityVector I) (label : I → K) (k : K)
    (hk : (p.pushforward label).weight k = 0) :
    p.conditionOnFiber label k =
      pointMass (Classical.choice (inferInstance : Nonempty I)) := by
  classical
  unfold conditionOnFiber
  split
  · apply ext
    funext i
    simp [pointMass]
  · rename_i hne
    exact (hne hk).elim

/-- On a positive-mass fiber, conditioning has the expected normalized coordinate formula. -/
@[simp] theorem conditionOnFiber_weight_of_ne
    (p : ProbabilityVector I) (label : I → K) (k : K)
    (hk : (p.pushforward label).weight k ≠ 0) (i : I) :
    (p.conditionOnFiber label k).weight i =
      if label i = k then p.weight i / (p.pushforward label).weight k else 0 := by
  classical
  unfold conditionOnFiber
  split
  · rename_i hzero
    exact (hk hzero).elim
  · rfl

/-- A positive-mass conditional law vanishes outside its defining fiber. -/
theorem conditionOnFiber_weight_eq_zero_of_ne
    (p : ProbabilityVector I) (label : I → K) (k : K)
    (hk : (p.pushforward label).weight k ≠ 0) {i : I} (hi : label i ≠ k) :
    (p.conditionOnFiber label k).weight i = 0 := by
  simp [conditionOnFiber_weight_of_ne p label k hk, hi]

/-- On a positive-mass fiber, a conditional coordinate is positive exactly when the original
coordinate is positive and has the requested label. -/
theorem conditionOnFiber_weight_pos_iff_of_ne
    (p : ProbabilityVector I) (label : I → K) (k : K)
    (hk : (p.pushforward label).weight k ≠ 0) (i : I) :
    0 < (p.conditionOnFiber label k).weight i ↔
      label i = k ∧ 0 < p.weight i := by
  have hmass : 0 < (p.pushforward label).weight k :=
    lt_of_le_of_ne ((p.pushforward label).nonneg k) (Ne.symm hk)
  rw [conditionOnFiber_weight_of_ne p label k hk]
  by_cases hi : label i = k
  · simpa only [hi, if_pos, true_and] using
      (div_pos_iff_of_pos_right hmass :
        0 < p.weight i / (p.pushforward label).weight k ↔ 0 < p.weight i)
  · simp [hi]

/-- Multiplying a conditional coordinate by its outer mass recovers the corresponding part of
the original coordinate, including the zero-mass case.

Proof sketch: for positive fiber mass this is cancellation.  If the fiber mass is zero, every
nonnegative summand defining that mass is zero, so the selected original coordinate is zero too.
-/
theorem pushforward_weight_mul_conditionOnFiber_weight
    (p : ProbabilityVector I) (label : I → K) (k : K) (i : I) :
    (p.pushforward label).weight k * (p.conditionOnFiber label k).weight i =
      if label i = k then p.weight i else 0 := by
  classical
  by_cases hk : (p.pushforward label).weight k = 0
  · have hsum : ∑ j, (if label j = k then p.weight j else 0) = 0 := by
      simpa only [pushforward_weight] using hk
    have hnonneg : ∀ j : I, 0 ≤ if label j = k then p.weight j else 0 := by
      intro j
      by_cases hj : label j = k
      · simpa [hj] using p.nonneg j
      · simp [hj]
    have hall : (fun j : I ↦ if label j = k then p.weight j else 0) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    rw [hk, zero_mul]
    exact (congrFun hall i).symm
  · rw [conditionOnFiber_weight_of_ne p label k hk]
    by_cases hi : label i = k
    · simp only [hi, if_pos]
      exact mul_div_cancel₀ (p.weight i) hk
    · simp [hi]

/-- Every finite law is exactly the mixture of its deterministic-fiber conditional laws.

Proof sketch: at each source coordinate, the summand indexed by its actual label recovers the
original weight; all other label summands vanish.  The preceding cancellation lemma handles empty
fibers without any separate support assumption.
-/
theorem mixture_conditionOnFiber
    (p : ProbabilityVector I) (label : I → K) :
    (p.pushforward label).mixture (p.conditionOnFiber label) = p := by
  classical
  ext i
  simp only [mixture_weight]
  calc
    (∑ k, (p.pushforward label).weight k *
        (p.conditionOnFiber label k).weight i) =
        ∑ k, if label i = k then p.weight i else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      exact pushforward_weight_mul_conditionOnFiber_weight p label k i
    _ = p.weight i := by simp

end ProbabilityVector

end AlgebraicComplexity
