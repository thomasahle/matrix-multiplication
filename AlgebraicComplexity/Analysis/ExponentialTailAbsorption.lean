/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential

/-!
# Absorbing subexponential losses into a strict exponential tail

Method-of-types estimates commonly bound a bad family by a subexponential loss times
`exp (-k * rate)`.  This file records the reusable analytic conclusion: every fixed real
prefactor is eventually absorbed when `rate` is positive.

The theorem is independent of type classes, entropy, tensor constructions, and repair schemes.
Those clients only have to supply the finite counting inequality and a positive rate.
-/

namespace AlgebraicComplexity.Growth

namespace Subexponential

/-- A strict exponential decay eventually absorbs both a subexponential sequence and a fixed
real prefactor.

Proof sketch: put `delta = exp (rate / 2)`.  Subexponentiality gives
`loss k <= delta ^ k` eventually, and a sufficiently large power of `delta` also dominates the
fixed prefactor.  Their product is at most `exp (k * rate)`, which cancels the displayed negative
exponential exactly. -/
theorem eventually_const_mul_loss_mul_exp_neg_natCast_le_one
    {loss : ℕ → ℝ} (hloss : Subexponential loss)
    {constant rate : ℝ} (hrate : 0 < rate) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      constant * loss k * Real.exp (-((k : ℝ) * rate)) ≤ 1 := by
  let delta : ℝ := Real.exp (rate / 2)
  have hdelta : 1 < delta := by
    dsimp only [delta]
    exact Real.one_lt_exp_iff.mpr (half_pos hrate)
  obtain ⟨lossCutoff, hlossBound⟩ := hloss.eventually_le_pow hdelta
  obtain ⟨constantCutoff, hconstantBound⟩ :
      ∃ constantCutoff : ℕ, constant < delta ^ constantCutoff :=
    pow_unbounded_of_one_lt constant hdelta
  refine ⟨max lossCutoff constantCutoff, ?_⟩
  intro k hk
  have hlossCutoff : lossCutoff ≤ k := (Nat.le_max_left _ _).trans hk
  have hconstantCutoff : constantCutoff ≤ k := (Nat.le_max_right _ _).trans hk
  have hlossLe : loss k ≤ delta ^ k := hlossBound k hlossCutoff
  have hconstantLe : constant ≤ delta ^ k :=
    hconstantBound.le.trans (pow_le_pow_right₀ hdelta.le hconstantCutoff)
  have hdeltaNonneg : 0 ≤ delta := (zero_lt_one.trans hdelta).le
  have hproduct : constant * loss k ≤ delta ^ k * delta ^ k :=
    mul_le_mul hconstantLe hlossLe (hloss.nonneg k) (pow_nonneg hdeltaNonneg k)
  have hdeltaPow : delta ^ k = Real.exp ((k : ℝ) * (rate / 2)) := by
    dsimp only [delta]
    rw [Real.exp_nat_mul]
  have hcancel :
      delta ^ k * delta ^ k * Real.exp (-((k : ℝ) * rate)) = 1 := by
    rw [hdeltaPow, ← Real.exp_add, ← Real.exp_add]
    have hexponent :
        (k : ℝ) * (rate / 2) + (k : ℝ) * (rate / 2) +
            -((k : ℝ) * rate) = 0 := by
      ring
    rw [hexponent, Real.exp_zero]
  calc
    constant * loss k * Real.exp (-((k : ℝ) * rate)) ≤
        (delta ^ k * delta ^ k) * Real.exp (-((k : ℝ) * rate)) :=
      mul_le_mul_of_nonneg_right hproduct (Real.exp_nonneg _)
    _ = 1 := hcancel

/-- Division-free comparison of a bad family with a target family sharing the same leading
exponential rate.

The bad count may lose the strict rate `rate`, while both estimates carry independent
subexponential losses.  After a uniform cutoff, every fixed natural repair budget times the bad
count is bounded by the target count.  The pointwise formulation lets a client choose different
finite families at each `k`; only the two loss sequences and the strict deficit rate must be
uniform.  The common leading entropy may itself vary between pointwise applications because it
cancels before the uniform tail estimate is used. -/
theorem eventually_budget_mul_bad_le_target_of_common_exponential_bounds
    {badLoss targetLoss : ℕ → ℝ}
    (hbadLoss : Subexponential badLoss)
    (htargetLoss : Subexponential targetLoss)
    {rate : ℝ} (hrate : 0 < rate) (budget : ℕ) :
    ∃ cutoff : ℕ, ∀ k bad target : ℕ, ∀ entropy : ℝ, cutoff ≤ k →
      (bad : ℝ) ≤ badLoss k * Real.exp ((k : ℝ) * (entropy - rate)) →
      Real.exp ((k : ℝ) * entropy) ≤ targetLoss k * (target : ℝ) →
      budget * bad ≤ target := by
  let combinedLoss : ℕ → ℝ := fun k ↦ badLoss k * targetLoss k
  have hcombinedLoss : Subexponential combinedLoss := hbadLoss.mul htargetLoss
  obtain ⟨cutoff, hcutoff⟩ :=
    hcombinedLoss.eventually_const_mul_loss_mul_exp_neg_natCast_le_one
      (constant := (budget : ℝ)) hrate
  refine ⟨cutoff, ?_⟩
  intro k bad target entropy hk hbad htarget
  have hexp :
      Real.exp ((k : ℝ) * (entropy - rate)) =
        Real.exp ((k : ℝ) * entropy) * Real.exp (-((k : ℝ) * rate)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreplaceTarget :
      ((budget : ℝ) * badLoss k) * Real.exp ((k : ℝ) * entropy) *
          Real.exp (-((k : ℝ) * rate)) ≤
        ((budget : ℝ) * badLoss k) * (targetLoss k * (target : ℝ)) *
          Real.exp (-((k : ℝ) * rate)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left htarget
      (mul_nonneg (Nat.cast_nonneg budget) (hbadLoss.nonneg k))
  have hcoefficient :
      (budget : ℝ) * combinedLoss k * Real.exp (-((k : ℝ) * rate)) ≤ 1 :=
    hcutoff k hk
  have hreal : ((budget * bad : ℕ) : ℝ) ≤ (target : ℝ) := by
    rw [Nat.cast_mul]
    calc
      (budget : ℝ) * (bad : ℝ) ≤
          (budget : ℝ) *
            (badLoss k * Real.exp ((k : ℝ) * (entropy - rate))) :=
        mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg budget)
      _ = ((budget : ℝ) * badLoss k) * Real.exp ((k : ℝ) * entropy) *
          Real.exp (-((k : ℝ) * rate)) := by rw [hexp]; ring
      _ ≤ ((budget : ℝ) * badLoss k) * (targetLoss k * (target : ℝ)) *
          Real.exp (-((k : ℝ) * rate)) := hreplaceTarget
      _ = ((budget : ℝ) * combinedLoss k *
          Real.exp (-((k : ℝ) * rate))) * (target : ℝ) := by
        dsimp only [combinedLoss]
        ring
      _ ≤ 1 * (target : ℝ) :=
        mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg target)
      _ = (target : ℝ) := one_mul _
  exact_mod_cast hreal

end Subexponential

end AlgebraicComplexity.Growth
