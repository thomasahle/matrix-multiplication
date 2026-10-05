/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Turning weak feasibility into a strict exponent bound

Every endpoint module in this development ends the same way.  A construction produces a
*feasibility* statement of the shape

`∀ Ω, budget ≤ retained + Ω * matrix → omega ≤ Ω`,

i.e. "any exponent that makes the asymptotic-sum budget fit is an upper bound for `omega`", and a
separate purely rational computation produces the *slack*

`budget < retained + target * matrix`.

`strict_of_feasibility_with_slack` is the one-line bridge: instantiate the feasibility at the exact
break-even exponent `Ω = (budget - retained) / matrix` and read the slack as `Ω < target`.

The lemma is pure ordered-field arithmetic — no tensor, certificate, or paper constant occurs in
it.  It lives in its own Mathlib-only leaf because it was previously restated verbatim in every
endpoint module that needed it; those restatements are now imports of this one.
-/

namespace MatrixMultiplication.FeasibilitySlack

/-- **Positive slack plus a positive matrix exponent turns weak feasibility into a strict exponent
bound.**

If every exponent `Ω` satisfying the budget inequality `budget ≤ retained + Ω * matrix` dominates
`omega`, and `target` clears the budget with strict slack, then `omega < target`.

The witness is the break-even exponent `(budget - retained) / matrix`: it satisfies the budget
inequality with equality, and the strict slack says exactly that it lies below `target`. -/
theorem strict_of_feasibility_with_slack
    {omega budget retained matrix target : ℝ}
    (hmatrix : 0 < matrix)
    (hslack : budget < retained + target * matrix)
    (feasibility : ∀ Ω, budget ≤ retained + Ω * matrix → omega ≤ Ω) :
    omega < target := by
  let Ω := (budget - retained) / matrix
  have hΩ : Ω < target := by
    apply (div_lt_iff₀ hmatrix).2
    linarith
  have hfeasible : budget ≤ retained + Ω * matrix := by
    have hmatrixNe : matrix ≠ 0 := hmatrix.ne'
    dsimp [Ω]
    rw [div_mul_cancel₀ (budget - retained) hmatrixNe]
    linarith
  exact (feasibility Ω hfeasible).trans_lt hΩ

end MatrixMultiplication.FeasibilitySlack
