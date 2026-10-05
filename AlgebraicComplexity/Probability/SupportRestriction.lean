/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeiblerBounds
import AlgebraicComplexity.Probability.SupportRestrictionDataProcessing

/-!
# Restricting finite probability laws to a positive reference support

Certificate distributions commonly contain structural zeroes.  Information-projection theorems
are most naturally applied on the subtype where the reference law is positive.  This file gives
that passage a reusable exact API.

If `p` is absolutely continuous with respect to `q`, then `restrictToPositiveSupport p q` is the
same law with all common zero coordinates removed.  Restriction preserves entropy, expectations,
deterministic pushforwards, conditional entropy, and the coordinatewise quadratic KL lower bound.
No renormalization occurs: absolute continuity and normalization imply that the positive support
already carries all of `p`'s mass.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-! Definitions and entropy/KL preservation laws come from
`Probability/SupportRestrictionCore.lean`; pushforward and sparse data processing come from
`Probability/SupportRestrictionDataProcessing.lean`. -/

/-- Restriction preserves conditional entropy for every deterministic statistic. -/
theorem restrictToPositiveSupport_conditionalEntropy
    {J : Type v} [Fintype J] [DecidableEq J]
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) (f : I → J) :
    (restrictToPositiveSupport p q h).conditionalEntropy (f ∘ Subtype.val) =
      p.conditionalEntropy f := by
  unfold conditionalEntropy
  rw [restrictToPositiveSupport_entropy p q h,
    restrictToPositiveSupport_pushforward p q h f]

/-- Restriction preserves conditional entropy in bits. -/
theorem restrictToPositiveSupport_conditionalEntropyBits
    {J : Type v} [Fintype J] [DecidableEq J]
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) (f : I → J) :
    (restrictToPositiveSupport p q h).conditionalEntropyBits (f ∘ Subtype.val) =
      p.conditionalEntropyBits f := by
  unfold conditionalEntropyBits
  rw [restrictToPositiveSupport_conditionalEntropy p q h f]

/-- Restricting a reference law to its own support preserves conditional entropy. -/
theorem positiveSupportRestriction_conditionalEntropy
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    q.positiveSupportRestriction.conditionalEntropy (f ∘ Subtype.val) =
      q.conditionalEntropy f := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_conditionalEntropy q q (isAbsolutelyContinuous_refl q) f

/-- Restricting a reference law to its own support preserves conditional entropy in bits. -/
theorem positiveSupportRestriction_conditionalEntropyBits
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    q.positiveSupportRestriction.conditionalEntropyBits (f ∘ Subtype.val) =
      q.conditionalEntropyBits f := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_conditionalEntropyBits q q
      (isAbsolutelyContinuous_refl q) f

/-- Removing common structural zeroes preserves the coordinatewise quadratic KL lower bound. -/
theorem restrictToPositiveSupport_quadraticKlLower
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).quadraticKlLower
        q.positiveSupportRestriction = p.quadraticKlLower q := by
  unfold quadraticKlLower
  simp only [restrictToPositiveSupport_weight, positiveSupportRestriction_weight]
  rw [sum_positiveSupport_eq q (fun i ↦
    (p.weight i - q.weight i) ^ 2 / (2 * max (p.weight i) (q.weight i)))]
  intro i hqi
  have hpi : p.weight i = 0 := h i hqi
  simp [hpi, hqi]

/-- Removing common structural zeroes preserves the quadratic correction in bits. -/
theorem restrictToPositiveSupport_quadraticKlLowerBits
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).quadraticKlLowerBits
        q.positiveSupportRestriction = p.quadraticKlLowerBits q := by
  unfold quadraticKlLowerBits
  rw [restrictToPositiveSupport_quadraticKlLower p q h]

/-- The quadratic lower bound remains valid for a sparse reference whenever the first law is
absolutely continuous with respect to it. -/
theorem quadraticKlLower_le_klDiv_of_absoluteContinuity
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    p.quadraticKlLower q ≤ p.klDiv q := by
  have hrestricted := quadraticKlLower_le_klDiv
    (restrictToPositiveSupport p q h) q.positiveSupportRestriction
      q.positiveSupportRestriction_pos
  rw [restrictToPositiveSupport_quadraticKlLower p q h,
    restrictToPositiveSupport_klDiv p q h] at hrestricted
  exact hrestricted

/-- Sparse-reference quadratic lower bound in bits. -/
theorem quadraticKlLowerBits_le_klDivBits_of_absoluteContinuity
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    p.quadraticKlLowerBits q ≤ p.klDivBits q := by
  unfold quadraticKlLowerBits klDivBits
  exact div_le_div_of_nonneg_right
    (quadraticKlLower_le_klDiv_of_absoluteContinuity p q h)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

end ProbabilityVector

end AlgebraicComplexity
