/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Mass identities for labelled complementary occurrences

The two labelled occurrences over every state each carry its full integral mass.  This file
proves that their total mass is twice the original profile mass.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryOccurrence

universe u

variable {State : Type u} [Fintype State]

/-- Sum a natural-valued function over the two labelled sides. -/
theorem sum_side (f : ComplementarySide → ℕ) :
    (∑ side, f side) = f .left + f .right := by
  change (∑ side ∈ ({.left, .right} : Finset ComplementarySide), f side) = _
  simp

/-- The tagged occurrence profile has twice the mass of the ordered-state profile, including at
self-complementary states. -/
theorem sum_integralMass (profile : State → ℕ) :
    (∑ occurrence : ComplementaryOccurrence State, occurrence.integralMass profile) =
      2 * ∑ state, profile state := by
  classical
  unfold integralMass orderedState
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [sum_side]
  rw [Finset.sum_add_distrib]
  simp [Nat.succ_mul]

end ComplementaryOccurrence
end AlgebraicComplexity
