/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

set_option autoImplicit false

/-!
# Uniform tails over finite families

An eventual statement for each member of a finite family has one common natural-number cutoff.
This is the elementary finite-maximum step used when finitely many type-counting or concentration
estimates must hold at the same repetition.
-/

namespace AlgebraicComplexity

/-- Finitely many tails of natural-number sequences have one common cutoff.

The statement deliberately uses explicit cutoffs rather than filter notation so finite counting
clients can consume it without translating their hypotheses.  The proof is the finite-intersection
property of a filter, specialized to `Filter.atTop` on `ℕ`. -/
theorem exists_uniform_natCutoff_of_finite
    {ι : Sort*} [Finite ι] {P : ι → ℕ → Prop}
    (h : ∀ i, ∃ cutoff : ℕ, ∀ k, cutoff ≤ k → P i k) :
    ∃ cutoff : ℕ, ∀ k, cutoff ≤ k → ∀ i, P i k := by
  have hi : ∀ i, ∀ᶠ k : ℕ in Filter.atTop, P i k := fun i ↦
    Filter.eventually_atTop.2 (h i)
  exact Filter.eventually_atTop.1 (Filter.eventually_all.2 hi)

end AlgebraicComplexity
