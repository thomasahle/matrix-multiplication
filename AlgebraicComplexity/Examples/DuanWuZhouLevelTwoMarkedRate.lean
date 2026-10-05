/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarginalAmbientFiberCount

/-!
# The marked-count rate `hrate`, at the marginal-typical family

Layer 4 (`AlgebraicComplexity/Examples/`).  With the ambient question settled in favour of
`dwz63TargetTypicalWords`, both parameters the integration leaves free can now be chosen:

* `degree := dwz63TargetSharpDegree K n t`, certified by
  `dwz63MarginalAmbientFiberBound_XY`;
* `lossHash N := 125136 * dwz63SharpBehrendLoss (dwz63TargetSharpDegree K n t)`.

`dwz63_hrate_at_dwz63TargetTypicalWords` is then the integration's `hrate` at those choices, for
`marked := dwz63TargetTypicalWords K n t`.

## Where the cancellation happens

`dwz63SharpModulusLoss d = 4 · (2 · (15625 + 8 d + 1)) = 125008 + 64 d`, and at
`d = dwz63SharpDegree N_triple N_X` one has `N_X · d ≤ 2 N_triple` --- because `N_X · (N_triple/N_X)`
never exceeds `N_triple` and `N_X ≤ N_triple`.  So

`N_X · dwz63SharpRetentionLoss d = (125008 N_X + 64 (N_X · d)) · Behrend
   ≤ (125008 + 128) N_triple · Behrend`,

which is `dwz63_xCount_mul_retentionLoss_le`.  The marked count and the sharp degree cancel
exactly as `[DuanWuZhou2022]` §6.3 intends, and `N_X` survives only through the loss-free branch
bound `dwz63_hashingBranch_pow_le_dwz63XTypicalCount`.

`N_X ≤ N_triple` is itself read off the fiber identity of
`Examples/DuanWuZhouLevelTwoMarginalAmbientFiberCount.lean`: a typical word lies in its own leg
fiber, so that fiber has at least one element and `N_triple = #fiber · N_X ≥ N_X`.

## What is left

Only `Growth.Subexponential lossHash`.  The Behrend factor is `exp (4 √(log (M d / 2)))` with
`M d ≤ 2 (15625 + 8 d + 1)` and `d ≤ N_triple + 1 ≤ 11390625 ^ (n+1) + 1`, so its logarithm is
linear in `n` and the whole factor is `exp (O (√n))`.  That is an analysis-lane statement about
`dwz63SharpBehrendLoss` composed with the client's own degree sequence, and it is the single
remaining input to `omega_lt_2374631_of_openEstimatesMarked` from this lane.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_X ≤ N_triple`.**  A typical word lies in its own leg fiber, so the fiber identity
`#fiber · N_X = N_triple` has `#fiber ≥ 1`. -/
theorem dwz63XTypicalCount_le_dwz63JointTypicalCount (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63XTypicalCount n t ≤ dwz63JointTypicalCount K n t := by
  classical
  have hpos : 0 < dwz63JointTypicalCount K n t := dwz63JointTypicalCount_pos K hn
  obtain ⟨q, hq⟩ : (dwz63TargetTypicalWords K n t).Nonempty :=
    Finset.card_pos.mp hpos
  have hcount := card_dwz63LegFiberWords_mul K n t .X (dwz63LegWord K n .X q)
    fun o ↦ multiplicity_dwz63SymSixDigit_dwz63LegWord K n t .X o hq
  rw [dwz63LegTypicalCount_X] at hcount
  have hfpos : 0 < (dwz63LegFiberWords K n t .X (dwz63LegWord K n .X q)).card :=
    Finset.card_pos.mpr ⟨q, mem_dwz63LegFiberWords.mpr ⟨hq, rfl⟩⟩
  calc dwz63XTypicalCount n t
      ≤ (dwz63LegFiberWords K n t .X (dwz63LegWord K n .X q)).card *
          dwz63XTypicalCount n t := Nat.le_mul_of_pos_left _ hfpos
    _ = dwz63JointTypicalCount K n t := hcount

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_X · degree ≤ 2 N_triple`** at the sharp degree. -/
theorem dwz63XTypicalCount_mul_sharpDegree_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63XTypicalCount n t * dwz63TargetSharpDegree K n t ≤
      2 * dwz63JointTypicalCount K n t := by
  have hXJ := dwz63XTypicalCount_le_dwz63JointTypicalCount K hn
  have hdiv : dwz63JointTypicalCount K n t / dwz63XTypicalCount n t *
      dwz63XTypicalCount n t ≤ dwz63JointTypicalCount K n t :=
    Nat.div_mul_le_self _ _
  unfold dwz63TargetSharpDegree dwz63SharpDegree
  calc dwz63XTypicalCount n t *
        (dwz63JointTypicalCount K n t / dwz63XTypicalCount n t + 1)
      = dwz63JointTypicalCount K n t / dwz63XTypicalCount n t * dwz63XTypicalCount n t +
          dwz63XTypicalCount n t := by ring
    _ ≤ dwz63JointTypicalCount K n t + dwz63JointTypicalCount K n t :=
        Nat.add_le_add hdiv hXJ
    _ = 2 * dwz63JointTypicalCount K n t := by ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The cancellation.**  `N_X` times the retention loss at the sharp degree is at most a
Behrend-only multiple of `N_triple`. -/
theorem dwz63_xCount_mul_retentionLoss_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    ((dwz63XTypicalCount n t : ℕ) : ℝ) *
        dwz63SharpRetentionLoss (dwz63TargetSharpDegree K n t) ≤
      (125136 * dwz63SharpBehrendLoss (dwz63TargetSharpDegree K n t)) *
        ((dwz63JointTypicalCount K n t : ℕ) : ℝ) := by
  have hB : (0 : ℝ) < dwz63SharpBehrendLoss (dwz63TargetSharpDegree K n t) :=
    dwz63SharpBehrendLoss_pos _
  have hXnn : (0 : ℝ) ≤ ((dwz63XTypicalCount n t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : ((dwz63XTypicalCount n t : ℕ) : ℝ) ≤ ((dwz63JointTypicalCount K n t : ℕ) : ℝ) := by
    exact_mod_cast dwz63XTypicalCount_le_dwz63JointTypicalCount K hn
  have hXd : ((dwz63XTypicalCount n t : ℕ) : ℝ) *
      ((dwz63TargetSharpDegree K n t : ℕ) : ℝ) ≤
      2 * ((dwz63JointTypicalCount K n t : ℕ) : ℝ) := by
    exact_mod_cast dwz63XTypicalCount_mul_sharpDegree_le K hn
  unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss
  nlinarith [hB, hX, hXd, hXnn]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The integration's `hrate`, at `marked := dwz63TargetTypicalWords K n t`,
`degree := dwz63TargetSharpDegree K n t` and
`lossHash := 125136 * dwz63SharpBehrendLoss degree`.**

The hashing branch is carried by the loss-free `dwz63_hashingBranch_pow_le_dwz63XTypicalCount`;
the retention loss and the marked count cancel by `dwz63_xCount_mul_retentionLoss_le`. -/
theorem dwz63_hrate_at_dwz63TargetTypicalWords (K : Type u) [CommRing K] :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → ∀ n : ℕ, n + 1 = 100000000 * t →
      dwz63HashingBranch ^ (6 * (n + 1)) *
          dwz63SharpRetentionLoss (dwz63TargetSharpDegree K n t) ≤
        (125136 * dwz63SharpBehrendLoss (dwz63TargetSharpDegree K n t)) *
          (((dwz63TargetTypicalWords K n t).card : ℕ) : ℝ) := by
  obtain ⟨cutoff, hcut⟩ := dwz63_hashingBranch_pow_le_dwz63XTypicalCount
  refine ⟨cutoff, fun t ht n hn ↦ ?_⟩
  exact dwz63_hrate_of_retentionLoss_le (hcut t ht n hn)
    (dwz63_xCount_mul_retentionLoss_le K hn)

end AlgebraicComplexity.Examples
