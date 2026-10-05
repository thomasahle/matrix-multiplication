/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy
import AlgebraicComplexity.Probability.KullbackLeiblerDefs
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary identities and nonnegativity for finite KL divergence

This module proves the part of finite Kullback--Leibler theory needed by entropy-gap and coupling
arguments: expansion against a positive reference, the information-projection identity, Gibbs'
inequality, and a derivative-free coordinatewise quadratic bound.  Deterministic data processing
lives downstream in `Probability/KullbackLeibler.lean`.

Keeping this leaf separate prevents a client that only compares entropy with KL divergence from
loading the finite-fiber/data-processing proof environment.  The historical KL module re-exports
every declaration here with the same name.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u

namespace ProbabilityVector

variable {ι : Type u} [Fintype ι]

/-- Expanding KL against a full-support reference gives negative entropy minus the expected
log-density of the reference. -/
theorem klDiv_eq_neg_entropy_sub_expectation_log
    (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i) :
    p.klDiv q = -p.entropy - p.expectation (fun i ↦ Real.log (q.weight i)) := by
  unfold klDiv entropy expectation
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p.weight i = 0
  · simp [hp]
  · rw [Real.log_div hp (hq i).ne', Real.negMulLog_eq_neg]
    ring

/-- If two laws have the same expectation of the reference log-density, KL is exactly their
entropy gap.  This is the finite information-projection identity used by compatibility pooling. -/
theorem klDiv_eq_entropy_sub_of_expectation_log_eq
    (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i)
    (hlog : p.expectation (fun i ↦ Real.log (q.weight i)) =
      q.expectation (fun i ↦ Real.log (q.weight i))) :
    p.klDiv q = q.entropy - p.entropy := by
  rw [klDiv_eq_neg_entropy_sub_expectation_log p q hq, hlog,
    entropy_eq_neg_expectation_log q]
  ring

/-- Every scalar relative-entropy gap is nonnegative when its reference mass is positive. -/
private theorem zero_le_mul_log_div_add_sub
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log (p / q) + q - p := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa using hq.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hp.le
    have hratio : p * (q / p - 1) = q - p := by
      field_simp [hp.ne']
    rw [hratio] at hscaled
    rw [Real.log_div hp.ne' hq.ne']
    nlinarith

/-- On the positive-excess side, one scalar KL gap dominates
`(p - q)² / (p + q)`.

Proof sketch: write `p / q = 1 + x` and apply the elementary logarithm bound
`2x / (x + 2) ≤ log (1 + x)`. -/
private theorem sq_sub_div_add_le_mul_log_div_add_sub
    {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) :
    (p - q) ^ 2 / (p + q) ≤ p * Real.log (p / q) + q - p := by
  have hp : 0 < p := hq.trans_le hqp
  let x : ℝ := (p - q) / q
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hqp) hq.le
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hone : 1 + x = p / q := by
    dsimp only [x]
    field_simp [hq.ne']
    ring
  rw [hone] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hp.le
  have hpq : p + q ≠ 0 := (add_pos hp hq).ne'
  have hxTwoEq : x + 2 = (p + q) / q := by
    dsimp only [x]
    field_simp [hq.ne']
    ring
  have hratio : 2 * x / (x + 2) = 2 * (p - q) / (p + q) := by
    calc
      2 * x / (x + 2) = (2 * (p - q)) / q / ((p + q) / q) := by
        rw [hxTwoEq]
        dsimp only [x]
        ring
      _ = 2 * (p - q) / (p + q) :=
        div_div_div_cancel_right₀ hq.ne' _ _
  have hid :
      p * (2 * x / (x + 2)) + q - p = (p - q) ^ 2 / (p + q) := by
    rw [hratio]
    rw [eq_div_iff hpq]
    have hcancel :
        (2 * (p - q) / (p + q)) * (p + q) = 2 * (p - q) :=
      div_mul_cancel₀ _ hpq
    calc
      (p * (2 * (p - q) / (p + q)) + q - p) * (p + q) =
          p * ((2 * (p - q) / (p + q)) * (p + q)) +
            (q - p) * (p + q) := by ring
      _ = p * (2 * (p - q)) + (q - p) * (p + q) := by rw [hcancel]
      _ = (p - q) ^ 2 := by ring
  rw [← hid]
  linarith

/-- Below the reference mass, the normalized relative-entropy gap dominates one quarter of the
squared discrepancy.

Proof sketch: apply `1 - s⁻¹ ≤ log s` at `s = √x`.  Since
`log x = 2 log √x`, this bounds the gap below by `(1 - √x)²`.  Finally
`(1 - x)² = (1 - √x)² (1 + √x)² ≤ 4 (1 - √x)²`. -/
private theorem quarter_sq_sub_one_le_relativeEntropyGap_of_le_one
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (x - 1) ^ 2 / 4 ≤ x * Real.log x - x + 1 := by
  let s : ℝ := Real.sqrt x
  have hs : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.2 hx
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    exact Real.sqrt_le_one.mpr hx1
  have hs_sq : s ^ 2 = x := by
    dsimp only [s]
    exact Real.sq_sqrt hx.le
  have hlog := Real.one_sub_inv_le_log_of_pos hs
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 2 * x by positivity)
  have hlog_sqrt : 2 * Real.log s = Real.log x := by
    dsimp only [s]
    rw [Real.log_sqrt hx.le]
    ring
  have hgap : (1 - s) ^ 2 ≤ x * Real.log x - x + 1 := by
    have hid : 2 * x * (1 - s⁻¹) - x + 1 = (1 - s) ^ 2 := by
      rw [← hs_sq]
      field_simp [hs.ne']
      ring
    rw [← hlog_sqrt]
    nlinarith
  have hfactor : x - 1 = (s - 1) * (s + 1) := by
    rw [← hs_sq]
    ring
  have hsum_sq : (s + 1) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (by positivity : 0 ≤ 3 + s)]
  have hquarter : (x - 1) ^ 2 / 4 ≤ (1 - s) ^ 2 := by
    rw [hfactor, mul_pow]
    have hmul := mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg (s - 1))
    nlinarith
  exact hquarter.trans hgap

/-- **Derivative-free two-sided scalar KL bound.**  For probability coordinates `p,q`, with a
positive reference coordinate `q`, the scalar relative-entropy gap dominates `(p-q)²/4`.

Proof sketch: positive excess uses the stronger denominator-`p+q` estimate.  For a deficit,
normalize by `q`, use the square-root bound above, and scale back; `q ≤ 1` loses at most the stated
universal factor. -/
theorem quarter_sq_sub_le_mul_log_div_add_sub_elementary
    {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    (p - q) ^ 2 / 4 ≤ p * Real.log (p / q) + q - p := by
  rcases le_total q p with hqp | hpq
  · have hstrong := sq_sub_div_add_le_mul_log_div_add_sub hq hqp
    have hpq_pos : 0 < p + q := add_pos_of_nonneg_of_pos hp hq
    have hpq_le : p + q ≤ 4 := by linarith
    have hweak : (p - q) ^ 2 / 4 ≤ (p - q) ^ 2 / (p + q) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hpq_pos]
      exact mul_le_mul_of_nonneg_left hpq_le (sq_nonneg (p - q))
    exact hweak.trans hstrong
  · rcases hp.eq_or_lt with rfl | hp0
    · simp only [zero_sub, zero_div, zero_mul, sub_zero]
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hq1)]
    · let x : ℝ := p / q
      have hx : 0 < x := div_pos hp0 hq
      have hx1 : x ≤ 1 := (div_le_one hq).2 hpq
      have hnormalized :=
        quarter_sq_sub_one_le_relativeEntropyGap_of_le_one hx hx1
      have hscaled := mul_le_mul_of_nonneg_left hnormalized hq.le
      have hstrong : (p - q) ^ 2 / (4 * q) ≤
          p * Real.log (p / q) + q - p := by
        calc
          (p - q) ^ 2 / (4 * q) = q * ((x - 1) ^ 2 / 4) := by
            dsimp only [x]
            field_simp [hq.ne']
          _ ≤ q * (x * Real.log x - x + 1) := hscaled
          _ = p * Real.log (p / q) + q - p := by
            dsimp only [x]
            field_simp [hq.ne']
            ring
      have hweak : (p - q) ^ 2 / 4 ≤ (p - q) ^ 2 / (4 * q) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
          (mul_pos (by norm_num) hq)]
        nlinarith [mul_nonneg (sq_nonneg (p - q)) (sub_nonneg.mpr hq1)]
      exact hweak.trans hstrong

/-- Every coordinate of a finite probability vector has mass at most one. -/
private theorem weight_le_one (p : ProbabilityVector ι) (i : ι) : p.weight i ≤ 1 := by
  classical
  rw [← p.total]
  exact Finset.single_le_sum (fun j _ ↦ p.nonneg j) (Finset.mem_univ i)

/-- **Derivative-free two-sided coordinatewise KL bound.**  Against a full-support finite
reference law, every coordinate discrepancy satisfies
`(pᵢ-qᵢ)²/4 ≤ KL(p‖q)`.

Proof sketch: apply the scalar quarter-square bound at the selected coordinate, add the
nonnegative scalar gaps at all other coordinates, and cancel their linear terms using the two
probability normalizations. -/
theorem quarter_sq_sub_weight_le_klDiv_elementary
    (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i) (i : ι) :
    (p.weight i - q.weight i) ^ 2 / 4 ≤ p.klDiv q := by
  classical
  let gap : ι → ℝ := fun j ↦
    p.weight j * Real.log (p.weight j / q.weight j) + q.weight j - p.weight j
  have hgap_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ gap j := by
    intro j _
    exact zero_le_mul_log_div_add_sub (p.nonneg j) (hq j)
  have hselected : (p.weight i - q.weight i) ^ 2 / 4 ≤ gap i :=
    quarter_sq_sub_le_mul_log_div_add_sub_elementary
      (p.nonneg i) (weight_le_one p i) (hq i) (weight_le_one q i)
  calc
    (p.weight i - q.weight i) ^ 2 / 4 ≤ gap i := hselected
    _ ≤ ∑ j, gap j :=
      Finset.single_le_sum hgap_nonneg (Finset.mem_univ i)
    _ = p.klDiv q := by
      unfold gap klDiv
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total]
      ring

/-- Finite Gibbs inequality for nonnegative vectors of equal mass and a positive reference.

Proof sketch: add the nonnegative scalar relative-entropy gaps.  Their linear terms cancel because
the two vectors have equal total mass. -/
theorem sum_mul_log_div_nonneg
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hmass : ∑ i, p i = ∑ i, q i) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have hsum : 0 ≤ ∑ i, (p i * Real.log (p i / q i) + q i - p i) :=
    Finset.sum_nonneg fun i _ ↦ zero_le_mul_log_div_add_sub (hp i) (hq i)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hmass] at hsum
  linarith

/-- Gibbs' inequality for finite probability vectors with full-support reference. -/
theorem klDiv_nonneg (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i) :
    0 ≤ p.klDiv q := by
  exact sum_mul_log_div_nonneg p.weight q.weight p.nonneg hq (p.total.trans q.total.symm)

end ProbabilityVector

end AlgebraicComplexity
