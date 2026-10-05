/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeibler
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational lower bounds for finite KL divergence

The coordinatewise bound proved here is

`p log (p / q) + q - p ≥ (p - q)² / (2 max p q)`.

After summing probability vectors, the linear terms cancel.  The resulting lower bound is much
stronger than first collapsing the discrepancy to an `L¹` norm, and all distribution-dependent
operations are rational.  Only the final conversion from nats to bits involves `log 2`.

The second half of the file proves the **binary Pinsker inequality** with its sharp
natural-logarithm constant,

`KL((p, 1 - p) ‖ (r, 1 - r)) ≥ 2 (p - r)²`,

and propagates it to an arbitrary finite alphabet through the grouping inequality
`klDiv_pushforward_le`: for every event `A`, `KL(p ‖ q) ≥ 2 (p A - q A)²`, hence
`KL(p ‖ q) ≥ ‖p - q‖₁² / 2`.  The coordinatewise bound above is weaker than Pinsker near equality
(it gives `2 d² / (1 + |d|)` for two-point laws), so the two are complementary: the rational
coordinatewise bound is what certificates evaluate exactly, while Pinsker supplies the sharp
constant `2` in the exponent of AVW Lemma 5.1.
-/

open scoped BigOperators
open Set

namespace AlgebraicComplexity

namespace ProbabilityVector

universe u

variable {ι : Type u} [Fintype ι]

/-- Coordinatewise quadratic lower bound on KL divergence, in nats.  The `0 / 0 = 0`
convention of the real field makes coordinates where both laws vanish harmless. -/
noncomputable def quadraticKlLower (p q : ProbabilityVector ι) : ℝ :=
  ∑ i, (p.weight i - q.weight i) ^ 2 / (2 * max (p.weight i) (q.weight i))

/-- Rational discrepancy before the universal factor `1 / 2`. -/
noncomputable def maxNormalizedSquare (p q : ProbabilityVector ι) : ℝ :=
  ∑ i, (p.weight i - q.weight i) ^ 2 / max (p.weight i) (q.weight i)

/-- Coordinatewise quadratic lower bound measured in bits. -/
noncomputable def quadraticKlLowerBits (p q : ProbabilityVector ι) : ℝ :=
  p.quadraticKlLower q / Real.log 2

theorem quadraticKlLower_eq_half_maxNormalizedSquare (p q : ProbabilityVector ι) :
    p.quadraticKlLower q = p.maxNormalizedSquare q / 2 := by
  unfold quadraticKlLower maxNormalizedSquare
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem maxNormalizedSquare_nonneg (p q : ProbabilityVector ι) :
    0 ≤ p.maxNormalizedSquare q := by
  unfold maxNormalizedSquare
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) ((p.nonneg i).trans (le_max_left _ _))

theorem quadraticKlLower_nonneg (p q : ProbabilityVector ι) :
    0 ≤ p.quadraticKlLower q := by
  unfold quadraticKlLower
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
    ((p.nonneg i).trans (le_max_left _ _)))

/-- A directed rational lower bound on `1 / log 2` turns the distribution-dependent discrepancy
into a certified base-two KL lower bound. -/
theorem mul_quadraticKlLower_le_quadraticKlLowerBits
    (p q : ProbabilityVector ι) {inverseLogTwoLower : ℝ}
    (hlog : inverseLogTwoLower ≤ (Real.log 2)⁻¹) :
    inverseLogTwoLower * p.quadraticKlLower q ≤ p.quadraticKlLowerBits q := by
  rw [quadraticKlLowerBits, div_eq_mul_inv]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hlog (quadraticKlLower_nonneg p q))

/-- Weighted finite aggregation of rational quadratic certificates. -/
theorem sum_weight_mul_inverseLogTwoLower_half_maxNormalizedSquare_le
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (p q : κ → ProbabilityVector ι)
    (hweight : ∀ k, 0 ≤ weight k) {inverseLogTwoLower : ℝ}
    (hlog : inverseLogTwoLower ≤ (Real.log 2)⁻¹) :
    (∑ k, weight k *
      (inverseLogTwoLower * ((p k).maxNormalizedSquare (q k) / 2))) ≤
      ∑ k, weight k * (p k).quadraticKlLowerBits (q k) := by
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hweight k)
  rw [← quadraticKlLower_eq_half_maxNormalizedSquare]
  exact mul_quadraticKlLower_le_quadraticKlLowerBits (p k) (q k) hlog

private theorem relativeEntropyGap_quadratic_of_le_one
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (x - 1) ^ 2 / 2 ≤ x * Real.log x - x + 1 := by
  let f : ℝ → ℝ := fun t ↦ t * Real.log t - t + 1 - (t - 1) ^ 2 / 2
  have hfder : ∀ t ∈ Icc x 1, HasDerivAt f (Real.log t - (t - 1)) t := by
    intro t ht
    have htpos : 0 < t := hx.trans_le ht.1
    have hmain := (((hasDerivAt_id t).mul (Real.hasDerivAt_log htpos.ne')).sub
      (hasDerivAt_id t)).add_const 1 |>.sub
        (((hasDerivAt_id t).sub_const 1).pow 2 |>.div_const 2)
    have hraw : HasDerivAt f
        (1 * Real.log t + t * t⁻¹ - 1 - (2 : ℝ) * (t - 1) ^ (2 - 1) * 1 / 2) t :=
      hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
        dsimp [f])
    convert hraw using 1
    field_simp [htpos.ne']
    ring
  have hanti : AntitoneOn f (Icc x 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
    · intro t ht
      exact (hfder t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hfder t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonpos.mpr (Real.log_le_sub_one_of_pos
        (hx.trans_le (interior_subset ht).1))
  have h := hanti (by exact ⟨le_rfl, hx1⟩) (by exact ⟨hx1, le_rfl⟩) hx1
  dsimp [f] at h
  norm_num at h
  linarith

private theorem relativeEntropyGap_quadratic_of_one_le
    {x : ℝ} (hx : 0 < x) (h1x : 1 ≤ x) :
    (x - 1) ^ 2 / (2 * x) ≤ x * Real.log x - x + 1 := by
  let g : ℝ → ℝ := fun t ↦ t * Real.log t - 3 * t / 2 + 2 - t⁻¹ / 2
  have hgder : ∀ t ∈ Icc 1 x,
      HasDerivAt g (Real.log t - 1 / 2 + 1 / (2 * t ^ 2)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hmain := (((hasDerivAt_id t).mul (Real.hasDerivAt_log htpos.ne')).sub
      ((hasDerivAt_id t).const_mul 3 |>.div_const 2)).add_const 2 |>.sub
        ((hasDerivAt_id t).inv htpos.ne' |>.div_const 2)
    have hraw : HasDerivAt g
        (1 * Real.log t + t * t⁻¹ - 3 * 1 / 2 - (-1 / t ^ 2) / 2) t :=
      hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
        dsimp [g])
    convert hraw using 1
    field_simp [htpos.ne']
    ring
  have hmono : MonotoneOn g (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
    · intro t ht
      exact (hgder t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgder t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (interior_subset ht).1
      have hloginv := Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
      rw [Real.log_inv] at hloginv
      have hid :
          (1 - t⁻¹) - 1 / 2 + 1 / (2 * t ^ 2) =
            (t - 1) ^ 2 / (2 * t ^ 2) := by
        field_simp [htpos.ne']
        ring
      have hbase : 0 ≤ (1 - t⁻¹) - 1 / 2 + 1 / (2 * t ^ 2) := by
        rw [hid]
        positivity
      linarith
  have h := hmono (by exact ⟨le_rfl, h1x⟩) (by exact ⟨h1x, le_rfl⟩) h1x
  dsimp [g] at h
  norm_num at h
  have hid :
      x * Real.log x - x + 1 - (x - 1) ^ 2 / (2 * x) =
        x * Real.log x - 3 * x / 2 + 2 - x⁻¹ / 2 := by
    field_simp [hx.ne']
    ring
  rw [← sub_nonneg, hid]
  linarith

/-- Normalized scalar form of the coordinatewise quadratic KL bound. -/
theorem relativeEntropyGap_quadratic {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 / (2 * max x 1) ≤ x * Real.log x - x + 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  rcases le_total x 1 with hx1 | h1x
  · rw [max_eq_right hx1]
    simpa using relativeEntropyGap_quadratic_of_le_one hx hx1
  · rw [max_eq_left h1x]
    exact relativeEntropyGap_quadratic_of_one_le hx h1x

/-- Unnormalized scalar form used coordinate by coordinate for two finite laws. -/
theorem scalar_quadratic_le_mul_log_div_add_sub
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (p - q) ^ 2 / (2 * max p q) ≤ p * Real.log (p / q) + q - p := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [max_eq_right hq.le]
    simp
    rw [show q ^ 2 / (2 * q) = q / 2 by field_simp [hq.ne']]
    linarith
  rcases le_total p q with hpq | hqp
  · have hx : 0 < p / q := div_pos hp hq
    have hx1 : p / q ≤ 1 := (div_le_one hq).2 hpq
    have h := relativeEntropyGap_quadratic_of_le_one hx hx1
    have hscaled := mul_le_mul_of_nonneg_left h hq.le
    rw [max_eq_right hpq]
    calc
      (p - q) ^ 2 / (2 * q) = q * ((p / q - 1) ^ 2 / 2) := by
        field_simp [hq.ne']
      _ ≤ q * (p / q * Real.log (p / q) - p / q + 1) := hscaled
      _ = p * Real.log (p / q) + q - p := by
        field_simp [hq.ne']
        ring
  · have hx : 0 < p / q := div_pos hp hq
    have h1x : 1 ≤ p / q := (le_div_iff₀ hq).2 (by simpa using hqp)
    have h := relativeEntropyGap_quadratic_of_one_le hx h1x
    have hscaled := mul_le_mul_of_nonneg_left h hq.le
    rw [max_eq_left hqp]
    calc
      (p - q) ^ 2 / (2 * p) = q * ((p / q - 1) ^ 2 / (2 * (p / q))) := by
        field_simp [hq.ne', hp.ne']
      _ ≤ q * (p / q * Real.log (p / q) - p / q + 1) := hscaled
      _ = p * Real.log (p / q) + q - p := by
        field_simp [hq.ne']
        ring

/-- The coordinatewise rational expression lower-bounds KL divergence in nats. -/
theorem quadraticKlLower_le_klDiv
    (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i) :
    p.quadraticKlLower q ≤ p.klDiv q := by
  have hsum :
      (∑ i, (p.weight i - q.weight i) ^ 2 /
        (2 * max (p.weight i) (q.weight i))) ≤
      ∑ i, (p.weight i * Real.log (p.weight i / q.weight i) +
        q.weight i - p.weight i) :=
    Finset.sum_le_sum fun i _ ↦
      scalar_quadratic_le_mul_log_div_add_sub (p.nonneg i) (hq i)
  unfold quadraticKlLower klDiv
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total] at hsum
  simpa using hsum

/-- The coordinatewise rational expression lower-bounds KL divergence in bits. -/
theorem quadraticKlLowerBits_le_klDivBits
    (p q : ProbabilityVector ι) (hq : ∀ i, 0 < q.weight i) :
    p.quadraticKlLowerBits q ≤ p.klDivBits q := by
  unfold quadraticKlLowerBits klDivBits
  exact div_le_div_of_nonneg_right (quadraticKlLower_le_klDiv p q hq)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-! ### Binary Pinsker inequality

The bounds above lose a factor `1 / (1 + |d|)` against the sharp Pinsker constant.  This section
recovers the sharp constant `2` for the two-point case and for every single event, which is what
the binomial-tail exponent of AVW Lemma 5.1 actually needs.
-/

/-- `2 (1 - s)² ≤ -log s` for `0 < s ≤ 1`: the boundary case `p ∈ {0, 1}` of binary Pinsker.

The function `t ↦ -log t - 2 (t - 1)²` vanishes at `t = 1` and has derivative `-(2t - 1)² / t ≤ 0`
on `(0, 1]`, so it is antitone there. -/
private theorem two_mul_sq_one_sub_le_neg_log {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    2 * (1 - s) ^ 2 ≤ -Real.log s := by
  let h : ℝ → ℝ := fun t ↦ -Real.log t - 2 * (t - 1) ^ 2
  have hder : ∀ t ∈ Icc s 1, HasDerivAt h (-((2 * t - 1) ^ 2 / t)) t := by
    intro t ht
    have htpos : 0 < t := hs0.trans_le ht.1
    have hmain := ((Real.hasDerivAt_log htpos.ne').neg).sub
      ((((hasDerivAt_id t).sub_const 1).pow 2).const_mul 2)
    have hraw : HasDerivAt h
        (-t⁻¹ - 2 * ((2 : ℝ) * (t - 1) ^ (2 - 1) * 1)) t :=
      hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by dsimp [h])
    convert hraw using 1
    field_simp
    ring
  have hanti : AntitoneOn h (Icc s 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s 1)
    · intro t ht
      exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hder t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have htpos : 0 < t := hs0.trans_le (interior_subset ht).1
      exact neg_nonpos.mpr (by positivity)
  have hval := hanti (by exact ⟨le_rfl, hs1⟩) (by exact ⟨hs1, le_rfl⟩) hs1
  dsimp [h] at hval
  norm_num at hval
  linarith

/-- Interior case of binary Pinsker, stated with logarithm differences so that no division by a
possibly vanishing weight occurs.

The proof varies the *reference* point `r`, not the observed point `p`: for fixed `p ∈ (0, 1)` the
function
`F(s) = p (log p - log s) + (1 - p) (log (1 - p) - log (1 - s)) - 2 (p - s)²`
satisfies `F p = 0` and has the elementary rational derivative
`F'(s) = (s - p)(2s - 1)² / (s (1 - s))`,
whose sign is the sign of `s - p`.  Hence `F` decreases up to `p` and increases after it, so
`F r ≥ 0` for every `r ∈ (0, 1)`.  The usual proof differentiates in `p` and needs the second
derivative `1 / (p (1 - p)) ≥ 4`; differentiating in `r` keeps everything first order and
logarithm free. -/
private theorem two_mul_sq_sub_le_binaryLogDiff_of_pos {p r : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (p - r) ^ 2 ≤
      p * (Real.log p - Real.log r) +
        (1 - p) * (Real.log (1 - p) - Real.log (1 - r)) := by
  let F : ℝ → ℝ := fun s ↦
    p * (Real.log p - Real.log s) + (1 - p) * (Real.log (1 - p) - Real.log (1 - s)) -
      2 * (p - s) ^ 2
  have hder : ∀ s : ℝ, 0 < s → s < 1 →
      HasDerivAt F ((s - p) * (2 * s - 1) ^ 2 / (s * (1 - s))) s := by
    intro s hs0 hs1
    have hs1' : (0 : ℝ) < 1 - s := by linarith
    have hmain :=
      ((((Real.hasDerivAt_log hs0.ne').const_sub (Real.log p)).const_mul p).add
        (((((hasDerivAt_id s).const_sub (1 : ℝ)).log hs1'.ne').const_sub
            (Real.log (1 - p))).const_mul (1 - p))).sub
        ((((hasDerivAt_const s p).sub (hasDerivAt_id s)).pow 2).const_mul 2)
    have hraw : HasDerivAt F
        (p * -s⁻¹ + (1 - p) * -(-1 / (1 - s)) -
          2 * ((2 : ℝ) * (p - s) ^ (2 - 1) * (0 - 1))) s :=
      hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by dsimp [F])
    convert hraw using 1
    field_simp
    ring
  have hFp : F p = 0 := by simp [F]
  rcases le_total r p with hrp | hpr
  · have hsub : Icc r p ⊆ Ioo 0 1 := fun t ht ↦
      ⟨lt_of_lt_of_le hr0 ht.1, lt_of_le_of_lt ht.2 hp1⟩
    have hanti : AntitoneOn F (Icc r p) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r p)
      · intro t ht
        exact (hder t (hsub ht).1 (hsub ht).2).continuousAt.continuousWithinAt
      · intro t ht
        exact (hder t (hsub (interior_subset ht)).1
          (hsub (interior_subset ht)).2).hasDerivWithinAt
      · intro t ht
        have htmem := interior_subset ht
        have ht0 : 0 < t := (hsub htmem).1
        have ht1 : t < 1 := (hsub htmem).2
        have htp : t ≤ p := htmem.2
        have hnum : (t - p) * (2 * t - 1) ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
        exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    have hval := hanti (by exact ⟨le_rfl, hrp⟩) (by exact ⟨hrp, le_rfl⟩) hrp
    rw [hFp] at hval
    dsimp [F] at hval
    linarith
  · have hsub : Icc p r ⊆ Ioo 0 1 := fun t ht ↦
      ⟨lt_of_lt_of_le hp0 ht.1, lt_of_le_of_lt ht.2 hr1⟩
    have hmono : MonotoneOn F (Icc p r) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p r)
      · intro t ht
        exact (hder t (hsub ht).1 (hsub ht).2).continuousAt.continuousWithinAt
      · intro t ht
        exact (hder t (hsub (interior_subset ht)).1
          (hsub (interior_subset ht)).2).hasDerivWithinAt
      · intro t ht
        have htmem := interior_subset ht
        have ht0 : 0 < t := (hsub htmem).1
        have ht1 : t < 1 := (hsub htmem).2
        have hpt : p ≤ t := htmem.1
        have hnum : 0 ≤ (t - p) * (2 * t - 1) ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        exact div_nonneg hnum (by positivity)
    have hval := hmono (by exact ⟨le_rfl, hpr⟩) (by exact ⟨hpr, le_rfl⟩) hpr
    rw [hFp] at hval
    dsimp [F] at hval
    linarith

/-- **Binary Pinsker inequality, scalar form, in nats.**  For `0 ≤ p ≤ 1` and `0 < r < 1`,

`p log (p / r) + (1 - p) log ((1 - p) / (1 - r)) ≥ 2 (p - r)²`.

The left-hand side is the Kullback--Leibler divergence of the two-point law `(p, 1 - p)` from
`(r, 1 - r)` measured in nats, and `|p - r|` is their total-variation distance, so the constant
`2` is the sharp natural-logarithm Pinsker constant `2 d²`.  The `0 log 0 = 0` convention of
`Real.log` makes the endpoints `p = 0` and `p = 1` legal.

This sharpens `scalar_quadratic_le_mul_log_div_add_sub`, which yields only `2 d² / (1 + |d|)`
after summation. -/
theorem two_mul_sq_sub_le_binaryKlDiv {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (p - r) ^ 2 ≤
      p * Real.log (p / r) + (1 - p) * Real.log ((1 - p) / (1 - r)) := by
  have hlogdiff :
      2 * (p - r) ^ 2 ≤
        p * (Real.log p - Real.log r) +
          (1 - p) * (Real.log (1 - p) - Real.log (1 - r)) := by
    rcases hp0.eq_or_lt with rfl | hp0'
    · have hkey := two_mul_sq_one_sub_le_neg_log (s := 1 - r) (by linarith) (by linarith)
      have hrw : (1 : ℝ) - (1 - r) = r := by ring
      rw [hrw] at hkey
      simp only [zero_mul, zero_add, sub_zero, Real.log_one, one_mul, zero_sub]
      nlinarith [hkey]
    · rcases hp1.eq_or_lt with rfl | hp1'
      · have hkey := two_mul_sq_one_sub_le_neg_log (s := r) hr0 hr1.le
        simp only [Real.log_one, sub_self, zero_mul, add_zero, one_mul, zero_sub]
        nlinarith [hkey]
      · exact two_mul_sq_sub_le_binaryLogDiff_of_pos hp0' hp1' hr0 hr1
  have hfirst : p * Real.log (p / r) = p * (Real.log p - Real.log r) := by
    rcases hp0.eq_or_lt with rfl | hp0'
    · simp
    · rw [Real.log_div hp0'.ne' hr0.ne']
  have hsecond : (1 - p) * Real.log ((1 - p) / (1 - r)) =
      (1 - p) * (Real.log (1 - p) - Real.log (1 - r)) := by
    rcases hp1.eq_or_lt with rfl | hp1'
    · simp
    · rw [Real.log_div (sub_pos.mpr hp1').ne' (sub_pos.mpr hr1).ne']
  rw [hfirst, hsecond]
  exact hlogdiff

/-- **Binary Pinsker for probability vectors on `Bool`.**  `KL(u ‖ v) ≥ 2 (u true - v true)²`
in nats, for a full-support reference `v`. -/
theorem two_mul_sq_sub_weight_le_klDiv_bool (u v : ProbabilityVector Bool)
    (hv : ∀ b, 0 < v.weight b) :
    2 * (u.weight true - v.weight true) ^ 2 ≤ u.klDiv v := by
  have hu : u.weight true + u.weight false = 1 := by
    have h := u.total
    rwa [Fintype.sum_bool] at h
  have hvsum : v.weight true + v.weight false = 1 := by
    have h := v.total
    rwa [Fintype.sum_bool] at h
  have huf : u.weight false = 1 - u.weight true := by linarith
  have hvf : v.weight false = 1 - v.weight true := by linarith
  have hp0 : 0 ≤ u.weight true := u.nonneg true
  have hp1 : u.weight true ≤ 1 := by
    have := u.nonneg false
    linarith
  have hr0 : 0 < v.weight true := hv true
  have hr1 : v.weight true < 1 := by
    have := hv false
    linarith
  unfold klDiv
  rw [Fintype.sum_bool, huf, hvf]
  exact two_mul_sq_sub_le_binaryKlDiv hp0 hp1 hr0 hr1

/-- **Pinsker's inequality for a single event.**  For any finite event `A`,

`KL(p ‖ q) ≥ 2 (p A - q A)²`  (in nats).

This is the general finite-alphabet form obtained from the two-point case by the grouping (data
processing) inequality `klDiv_pushforward_le` applied to the two-block partition `{A, Aᶜ}`; the
degenerate partitions `A = ∅` and `A = univ` contribute a vanishing left-hand side and are handled
by `klDiv_nonneg`. -/
theorem two_mul_sq_sub_sum_le_klDiv (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) (A : Finset ι) :
    2 * ((∑ i ∈ A, p.weight i) - ∑ i ∈ A, q.weight i) ^ 2 ≤ p.klDiv q := by
  classical
  by_cases hfull : A = Finset.univ
  · subst hfull
    rw [p.total, q.total]
    simpa using klDiv_nonneg p q hq
  by_cases hempty : A = (∅ : Finset ι)
  · subst hempty
    simpa using klDiv_nonneg p q hq
  obtain ⟨i₁, hi₁⟩ :=
    not_forall.mp fun h ↦ hfull (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  set f : ι → Bool := fun i ↦ decide (i ∈ A) with hf
  have hsurj : Function.Surjective f := by
    intro b
    cases b with
    | true => exact ⟨i₀, by simp [hf, hi₀]⟩
    | false => exact ⟨i₁, by simp [hf, hi₁]⟩
  have hweight : ∀ m : ProbabilityVector ι,
      (m.pushforward f).weight true = ∑ i ∈ A, m.weight i := by
    intro m
    simp [hf, pushforward_weight, Finset.sum_ite_mem]
  have hbool := two_mul_sq_sub_weight_le_klDiv_bool (p.pushforward f) (q.pushforward f)
    (pushforward_weight_pos_of_surjective f q hq hsurj)
  rw [hweight p, hweight q] at hbool
  exact hbool.trans (klDiv_pushforward_le f p q hq hsurj)

/-- **Pinsker's inequality for a single coordinate.**  `KL(p ‖ q) ≥ 2 (pᵢ - qᵢ)²` in nats.

This is the exact constant needed to sharpen the binomial-tail exponent of Alman--Vassilevska
Williams, *Limits on All Known (and Some Unknown) Approaches to Matrix Multiplication*,
arXiv:1810.08671v1, **Lemma 5.1**.  Taking `p` to be the two-level (tilted) word type with mass
`t` on the marked letter and `q` the uniform law on an alphabet of size `Q` gives
`KL(tilt t ‖ uniform) ≥ 2 (t - 1/Q)²`, that is, the sharp exponent `2ε²`, in place of the
`2ε² / (1 + ε)` that `quadraticKlLower_le_klDiv` gives.  `Combinatorics/BinomialTail.lean` now
defines `tailExponent ε = 2ε²` and proves `tailExponent_le_klDiv_tiltVector` from this lemma, so
the `δ`-form of Lemma 5.1 holds there with AVW's printed radius `ε = sqrt(δ · log Q)`. -/
theorem two_mul_sq_sub_weight_le_klDiv (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) (i : ι) :
    2 * (p.weight i - q.weight i) ^ 2 ≤ p.klDiv q := by
  classical
  simpa using two_mul_sq_sub_sum_le_klDiv p q hq {i}

/-- **Pinsker's inequality on a finite alphabet.**  `‖p - q‖₁² ≤ 2 KL(p ‖ q)` in nats,
equivalently `KL(p ‖ q) ≥ 2 · TV(p, q)²` for the total-variation distance `TV = ‖p - q‖₁ / 2`.

The maximizing event is `A = {i | qᵢ ≤ pᵢ}`, for which `‖p - q‖₁ = 2 (p A - q A)` because the two
laws have equal total mass; `two_mul_sq_sub_sum_le_klDiv` then gives the claim. -/
theorem sq_sum_abs_sub_le_two_mul_klDiv (p q : ProbabilityVector ι)
    (hq : ∀ i, 0 < q.weight i) :
    (∑ i, |p.weight i - q.weight i|) ^ 2 ≤ 2 * p.klDiv q := by
  classical
  set A : Finset ι := Finset.univ.filter fun i ↦ q.weight i ≤ p.weight i with hA
  set S : ℝ := (∑ i ∈ A, p.weight i) - ∑ i ∈ A, q.weight i with hS
  have hbal : ∑ i, (p.weight i - q.weight i) = 0 := by
    rw [Finset.sum_sub_distrib, p.total, q.total, sub_self]
  have hsplitAbs :
      (∑ i ∈ A, |p.weight i - q.weight i|) +
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ q.weight i ≤ p.weight i),
          |p.weight i - q.weight i| =
        ∑ i, |p.weight i - q.weight i| :=
    Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have hsplitDiff :
      (∑ i ∈ A, (p.weight i - q.weight i)) +
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ q.weight i ≤ p.weight i),
          (p.weight i - q.weight i) =
        ∑ i, (p.weight i - q.weight i) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have habsA : (∑ i ∈ A, |p.weight i - q.weight i|) =
      ∑ i ∈ A, (p.weight i - q.weight i) :=
    Finset.sum_congr rfl fun i hi ↦
      abs_of_nonneg (by
        have := (Finset.mem_filter.mp hi).2
        linarith)
  have habsB : (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ q.weight i ≤ p.weight i),
        |p.weight i - q.weight i|) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ q.weight i ≤ p.weight i),
        -(p.weight i - q.weight i) :=
    Finset.sum_congr rfl fun i hi ↦
      abs_of_nonpos (by
        have := not_le.mp (Finset.mem_filter.mp hi).2
        linarith)
  rw [Finset.sum_neg_distrib] at habsB
  have hsumS : ∑ i ∈ A, (p.weight i - q.weight i) = S := by
    rw [hS, Finset.sum_sub_distrib]
  have hTV : ∑ i, |p.weight i - q.weight i| = 2 * S := by
    rw [← hsplitAbs, habsA, habsB, hsumS]
    rw [hsumS] at hsplitDiff
    rw [hbal] at hsplitDiff
    linarith
  have hkey := two_mul_sq_sub_sum_le_klDiv p q hq A
  rw [← hS] at hkey
  rw [hTV]
  nlinarith [hkey]

end ProbabilityVector

end AlgebraicComplexity
