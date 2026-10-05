/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeiblerBasic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Kullback--Leibler divergence for finite probability vectors

This module extends the elementary identities and Gibbs inequality in
`Probability/KullbackLeiblerBasic.lean` with deterministic data processing.  The reference
distribution is assumed to have full support, which keeps the divergence real-valued and is
exactly the situation after restricting to the structural support of a compatibility model.

The main result is deterministic data processing: pushing two distributions through a finite map
cannot increase their KL divergence.  The proof is the finite log-sum inequality, with all zero
coordinates of the first distribution handled explicitly.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {ι : Type u} [Fintype ι]

private theorem scaled_normalized_term
    {p q P Q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hP : 0 < P) (hQ : 0 < Q) :
    P * ((p / P) * Real.log ((p / P) / (q / Q))) =
      p * Real.log (p / q) - p * Real.log (P / Q) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · rw [Real.log_div (div_ne_zero hp.ne' hP.ne') (div_ne_zero hq.ne' hQ.ne'),
      Real.log_div hp.ne' hP.ne', Real.log_div hq.ne' hQ.ne',
      Real.log_div hp.ne' hq.ne', Real.log_div hP.ne' hQ.ne']
    field_simp [hP.ne']
    ring

/-- Sum over one fiber, expressed as an indicator sum over the ambient finite type. -/
private theorem sum_fiber_eq_sum_ite
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (b : κ) (g : ι → ℝ) :
    (∑ i : {i : ι // f i = b}, g i) =
      ∑ i, if f i = b then g i else 0 := by
  classical
  calc
    (∑ i : {i : ι // f i = b}, g i) =
        ∑ i ∈ Finset.univ.filter (fun i ↦ f i = b), g i :=
      (Finset.sum_subtype (Finset.univ.filter fun i ↦ f i = b)
        (fun i ↦ by simp) g).symm
    _ = ∑ i, if f i = b then g i else 0 := by
      rw [← Finset.sum_filter]

/-- The mass of a pushforward coordinate is the sum over its fiber. -/
theorem pushforward_weight_eq_sum_fiber
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p : ProbabilityVector ι) (b : κ) :
    (p.pushforward f).weight b = ∑ i : {i : ι // f i = b}, p.weight i := by
  rw [pushforward_weight, sum_fiber_eq_sum_ite]

/-- Log-sum inequality on one fiber. -/
private theorem pushforward_term_le_fiber_sum
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) (hf : Function.Surjective f) (b : κ) :
    (p.pushforward f).weight b *
        Real.log ((p.pushforward f).weight b / (q.pushforward f).weight b) ≤
      ∑ i : {i : ι // f i = b},
        p.weight i * Real.log (p.weight i / q.weight i) := by
  let P := (p.pushforward f).weight b
  let Q := (q.pushforward f).weight b
  have hQ : 0 < Q := pushforward_weight_pos_of_surjective f q hq hf b
  change P * Real.log (P / Q) ≤
    ∑ i : {i : ι // f i = b},
      p.weight i * Real.log (p.weight i / q.weight i)
  by_cases hPzero : P = 0
  · have hpFiber : ∀ i : {i : ι // f i = b}, p.weight i = 0 := by
      intro i
      have hsum : ∑ j : {j : ι // f j = b}, p.weight j = 0 := by
        rw [← pushforward_weight_eq_sum_fiber f p b]
        exact hPzero
      have hnonneg : ∀ j : {j : ι // f j = b}, 0 ≤ p.weight j :=
        fun j ↦ p.nonneg j
      have hall : (fun j : {j : ι // f j = b} ↦ p.weight j) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
      exact congrFun hall i
    simp [hPzero, hpFiber]
  · have hPnonneg : 0 ≤ P := (p.pushforward f).nonneg b
    have hP : 0 < P := lt_of_le_of_ne hPnonneg (Ne.symm hPzero)
    let r : {i : ι // f i = b} → ℝ := fun i ↦ p.weight i / P
    let s : {i : ι // f i = b} → ℝ := fun i ↦ q.weight i / Q
    have hr : ∀ i, 0 ≤ r i := fun i ↦ div_nonneg (p.nonneg i) hP.le
    have hs : ∀ i, 0 < s i := fun i ↦ div_pos (hq i) hQ
    have hrMass : ∑ i, r i = 1 := by
      dsimp [r]
      rw [← Finset.sum_div, ← pushforward_weight_eq_sum_fiber f p b]
      exact div_self hP.ne'
    have hsMass : ∑ i, s i = 1 := by
      dsimp [s]
      rw [← Finset.sum_div, ← pushforward_weight_eq_sum_fiber f q b]
      exact div_self hQ.ne'
    have hconditional : 0 ≤ ∑ i, r i * Real.log (r i / s i) :=
      sum_mul_log_div_nonneg r s hr hs (hrMass.trans hsMass.symm)
    have hscaled : 0 ≤ P * ∑ i, r i * Real.log (r i / s i) :=
      mul_nonneg hP.le hconditional
    have hid :
        P * ∑ i, r i * Real.log (r i / s i) =
          (∑ i : {i : ι // f i = b},
            p.weight i * Real.log (p.weight i / q.weight i)) -
          P * Real.log (P / Q) := by
      have hPsum : ∑ i : {i : ι // f i = b}, p.weight i = P := by
        rw [← pushforward_weight_eq_sum_fiber f p b]
      calc
        P * ∑ i, r i * Real.log (r i / s i) =
            ∑ i : {i : ι // f i = b},
              P * (r i * Real.log (r i / s i)) := by rw [Finset.mul_sum]
        _ = ∑ i : {i : ι // f i = b},
              (p.weight i * Real.log (p.weight i / q.weight i) -
                p.weight i * Real.log (P / Q)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact scaled_normalized_term (p.nonneg i) (hq i) hP hQ
        _ = (∑ i : {i : ι // f i = b},
                p.weight i * Real.log (p.weight i / q.weight i)) -
              ∑ i : {i : ι // f i = b},
                p.weight i * Real.log (P / Q) := by rw [Finset.sum_sub_distrib]
        _ = (∑ i : {i : ι // f i = b},
                p.weight i * Real.log (p.weight i / q.weight i)) -
              P * Real.log (P / Q) := by
          rw [← Finset.sum_mul, hPsum]
    rw [hid] at hscaled
    exact sub_nonneg.mp hscaled

/-- **Deterministic data processing for finite KL divergence.**  Pushing probability vectors
through a surjection cannot increase divergence.  Surjectivity merely removes empty output
coordinates; any map can be replaced by its range subtype. -/
theorem klDiv_pushforward_le
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) (hf : Function.Surjective f) :
    (p.pushforward f).klDiv (q.pushforward f) ≤ p.klDiv q := by
  let g : ι → ℝ := fun i ↦ p.weight i * Real.log (p.weight i / q.weight i)
  change (∑ b, (p.pushforward f).weight b *
      Real.log ((p.pushforward f).weight b / (q.pushforward f).weight b)) ≤ ∑ i, g i
  calc
    (∑ b, (p.pushforward f).weight b *
        Real.log ((p.pushforward f).weight b / (q.pushforward f).weight b)) ≤
        ∑ b, ∑ i : {i : ι // f i = b},
          g i :=
      Finset.sum_le_sum fun b _ ↦ pushforward_term_le_fiber_sum f p q hq hf b
    _ = ∑ i, g i := Fintype.sum_fiberwise f g

/-- Data processing in bits. -/
theorem klDivBits_pushforward_le
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) (hf : Function.Surjective f) :
    (p.pushforward f).klDivBits (q.pushforward f) ≤ p.klDivBits q := by
  unfold klDivBits
  exact div_le_div_of_nonneg_right (klDiv_pushforward_le f p q hq hf)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

end ProbabilityVector

end AlgebraicComplexity
