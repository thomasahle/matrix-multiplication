/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CopyGrowth

/-!
# Exponential families eventually dominate subexponential integral denominators

Finite extraction counts often have the form `familyCard / denominator`.  Positivity of that
quotient must be established before a Euclidean remainder can be absorbed into a multiplicative
loss.  This file packages the reusable bootstrap: if `familyCard` has exponential growth up to a
subexponential loss and `denominator` is subexponential, then eventually
`denominator ≤ familyCard`.

The conclusion is an exact inequality of natural numbers.  No division, logarithm, or limiting
statement remains in it.
-/

namespace AlgebraicComplexity.Growth

/-- An exponentially growing natural-valued family eventually contains every subexponential
natural-valued denominator.

The proof inserts the intermediate base `(base + 1) / 2`.  It is strictly between `1` and `base`.
The ambient loss can therefore be removed at that smaller base, while the denominator is
eventually bounded by the same exponential. -/
theorem Subexponential.exists_forall_natCast_denominator_le_count_of_pow_le_mul
    {base : ℝ} {ambientLoss : ℕ → ℝ} {denominator count : ℕ → ℕ}
    (hbase : 1 < base)
    (hambient : Subexponential ambientLoss)
    (hdenominator : Subexponential (fun r ↦ (denominator r : ℝ)))
    (hfamily : ∀ r, base ^ r ≤ ambientLoss r * (count r : ℝ)) :
    ∃ cutoff : ℕ, ∀ r, cutoff ≤ r → denominator r ≤ count r := by
  let lowerBase : ℝ := (base + 1) / 2
  have hlowerOne : 1 < lowerBase := by
    dsimp [lowerBase]
    linarith
  have hlowerPos : 0 < lowerBase := zero_lt_one.trans hlowerOne
  have hlowerBase : lowerBase < base := by
    dsimp [lowerBase]
    linarith
  obtain ⟨countCutoff, hcount⟩ :=
    hambient.exists_forall_pow_le_natCast_of_pow_le_mul hlowerPos hlowerBase
  obtain ⟨denominatorCutoff, hdenominatorBound⟩ :=
    hdenominator.eventually_le_pow hlowerOne
  refine ⟨max countCutoff denominatorCutoff, fun r hr ↦ ?_⟩
  have hcountCutoff : countCutoff ≤ r := (Nat.le_max_left _ _).trans hr
  have hdenominatorCutoff : denominatorCutoff ≤ r :=
    (Nat.le_max_right _ _).trans hr
  have hreal : (denominator r : ℝ) ≤ (count r : ℝ) :=
    (hdenominatorBound r hdenominatorCutoff).trans
      (hcount r (count r) hcountCutoff (hfamily r))
  exact_mod_cast hreal

end AlgebraicComplexity.Growth
