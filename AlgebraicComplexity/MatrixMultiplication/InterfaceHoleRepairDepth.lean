/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

/-!
# The logarithmic depth of a three-leg interface repair

This definition is kept separate from the semantic hole-repair construction so finite counting
clients can state and bound the repair depth without importing tensor relabellings or repair trees.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor

universe u

variable {A : Leg → Type u}

/-- Sum of the three ceiling-log sizes used as the well-founded repair measure. -/
def logarithmicRepairDepth (base : ℕ) (target : ∀ c, Finset (A c)) : ℕ :=
  Finset.univ.sum fun c ↦ Nat.clog base (target c).card

/-- Expand the repair depth into its three named legs. -/
theorem logarithmicRepairDepth_eq_three (base : ℕ) (target : ∀ c, Finset (A c)) :
    logarithmicRepairDepth base target =
      Nat.clog base (target .X).card +
        Nat.clog base (target .Y).card +
        Nat.clog base (target .Z).card := by
  unfold logarithmicRepairDepth
  rw [show (Finset.univ : Finset Leg) = {.X, .Y, .Z} by
    ext c
    cases c <;> simp]
  simp [Nat.add_assoc]

end AlgebraicComplexity.HoleRepair
