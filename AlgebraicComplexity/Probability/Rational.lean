/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.RationalCore
import AlgebraicComplexity.Probability.KullbackLeiblerBounds
import Mathlib.Tactic.NormNum

/-!
# Exact rational probability data

Certificate generators should emit rational tables and let Lean perform the final exact
comparison.  This module provides a small bridge from executable rational tables to the real
`ProbabilityVector` API used by the information-theoretic theorems.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace RationalProbabilityData

variable {ι : Type u} [Fintype ι]

/-- Executable rational counterpart of `ProbabilityVector.maxNormalizedSquare`. -/
def maxNormalizedSquare (p q : RationalProbabilityData ι) : ℚ :=
  ∑ i, (p.weight i - q.weight i) ^ 2 / max (p.weight i) (q.weight i)

/-- Casting the raw rational max-normalized-square expression to the reals commutes with its
finite sum.  No simplex hypothesis is needed; this lemma is useful at a certificate/reconstruction
boundary where validity comes from an independently constructed probability model. -/
theorem cast_maxNormalizedSquare (p q : RationalProbabilityData ι) :
    (∑ i, ((p.weight i : ℝ) - (q.weight i : ℝ)) ^ 2 /
        max (p.weight i : ℝ) (q.weight i : ℝ)) =
      (p.maxNormalizedSquare q : ℝ) := by
  unfold maxNormalizedSquare
  calc
    (∑ i, ((p.weight i : ℝ) - (q.weight i : ℝ)) ^ 2 /
        max (p.weight i : ℝ) (q.weight i : ℝ)) =
        ∑ i, (((p.weight i - q.weight i) ^ 2 /
          max (p.weight i) (q.weight i) : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      norm_cast
    _ = (∑ i, (p.weight i - q.weight i) ^ 2 /
        max (p.weight i) (q.weight i) : ℚ) := by norm_cast

theorem toReal_maxNormalizedSquare
    (p q : RationalProbabilityData ι) (hp : p.IsProbability) (hq : q.IsProbability) :
    (p.toReal hp).maxNormalizedSquare (q.toReal hq) =
      (p.maxNormalizedSquare q : ℝ) := by
  unfold ProbabilityVector.maxNormalizedSquare
  exact cast_maxNormalizedSquare p q

/-- Exact weighted rational discrepancy for a finite family of parent laws. -/
def weightedMaxNormalizedSquare
    {κ : Type v} [Fintype κ]
    (weight : κ → ℚ)
    (parent decoupled : κ → RationalProbabilityData ι) : ℚ :=
  ∑ k, weight k * (parent k).maxNormalizedSquare (decoupled k)

/-- Raw rational weighted discrepancies commute with casting, independently of simplex
validity. -/
theorem cast_weightedMaxNormalizedSquare
    {κ : Type v} [Fintype κ]
    (weight : κ → ℚ)
    (parent decoupled : κ → RationalProbabilityData ι) :
    (∑ k, (weight k : ℝ) *
      (∑ i, (((parent k).weight i : ℝ) - ((decoupled k).weight i : ℝ)) ^ 2 /
        max ((parent k).weight i : ℝ) ((decoupled k).weight i : ℝ))) =
      (weightedMaxNormalizedSquare weight parent decoupled : ℝ) := by
  unfold weightedMaxNormalizedSquare
  calc
    (∑ k, (weight k : ℝ) *
        (∑ i, (((parent k).weight i : ℝ) - ((decoupled k).weight i : ℝ)) ^ 2 /
          max ((parent k).weight i : ℝ) ((decoupled k).weight i : ℝ))) =
        ∑ k, ((weight k * (parent k).maxNormalizedSquare (decoupled k) : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [cast_maxNormalizedSquare]
      norm_cast
    _ = (∑ k, weight k * (parent k).maxNormalizedSquare (decoupled k) : ℚ) := by
      norm_cast

theorem toReal_weightedMaxNormalizedSquare
    {κ : Type v} [Fintype κ]
    (weight : κ → ℚ)
    (parent decoupled : κ → RationalProbabilityData ι)
    (hparent : ∀ k, (parent k).IsProbability)
    (hdecoupled : ∀ k, (decoupled k).IsProbability) :
    (∑ k, (weight k : ℝ) *
      ((parent k).toReal (hparent k)).maxNormalizedSquare
        ((decoupled k).toReal (hdecoupled k))) =
      (weightedMaxNormalizedSquare weight parent decoupled : ℝ) := by
  simp only [toReal_maxNormalizedSquare, weightedMaxNormalizedSquare]
  push_cast
  rfl

end RationalProbabilityData

end AlgebraicComplexity
