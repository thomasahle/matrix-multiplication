/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Cell identities for labelled complementary occurrences

This file identifies the pushed tagged-occurrence profile with the evaluator formula obtained by
adding the two complementary masses.  Its fixed-point corollary makes explicit that a
self-complementary state contributes twice.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

section CellProfiles

variable {State : Type u} [Fintype State]
variable {Cell : Type v} [DecidableEq Cell]

private theorem sum_side_for_cell (f : ComplementarySide → ℕ) :
    (∑ side, f side) = f .left + f .right := by
  change (∑ side ∈ ({.left, .right} : Finset ComplementarySide), f side) = _
  simp

/-- Pushing explicitly labelled occurrences gives exactly the evaluator's integral cell profile.

Proof sketch: split the occurrence sum into its left and right parts, reindex the right part by
the complement equivalence, and recombine the two sums cellwise. -/
theorem complementaryOccurrenceCellProfile_eq_evaluator
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) :
    complementaryOccurrenceCellProfile profile complement cellOf =
      evaluatorComplementaryCellProfile profile complement cellOf := by
  classical
  funext cell
  unfold complementaryOccurrenceCellProfile evaluatorComplementaryCellProfile
  rw [WordType.mappedType_eq_sum_ite, ← Finset.univ_product_univ, Finset.sum_product]
  have hreindex :
      (∑ u, if cellOf (complement u) = cell then profile u else 0) =
        ∑ child, if cellOf child = cell then profile (complement.symm child) else 0 := by
    simpa using
      (Equiv.sum_comp complement
        (fun child ↦ if cellOf child = cell then profile (complement.symm child) else 0))
  simp_rw [sum_side_for_cell]
  change
    (∑ u, ((if cellOf u = cell then profile u else 0) +
      (if cellOf (complement u) = cell then profile u else 0))) = _
  rw [Finset.sum_add_distrib, hreindex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro child _
  by_cases hcell : cellOf child = cell <;> simp [hcell]

/-- For a self-inverse complement, the cell profile is the literal sum of
`profile(u) + profile(complement u)`. -/
theorem complementaryOccurrenceCellProfile_eq_selfInverse_sum
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (hselfInverse : complement.symm = complement)
    (cellOf : State → Cell) (cell : Cell) :
    complementaryOccurrenceCellProfile profile complement cellOf cell =
      ∑ child, if cellOf child = cell then
        profile child + profile (complement child) else 0 := by
  rw [complementaryOccurrenceCellProfile_eq_evaluator]
  simp [evaluatorComplementaryCellProfile, hselfInverse]

omit [Fintype State] in
/-- A fixed point of complementation contributes two labelled integral occurrences. -/
theorem selfComplementary_integralOccurrenceWeight
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (hselfInverse : complement.symm = complement)
    (u : State) (hfixed : complement u = u) :
    profile u + profile (complement.symm u) = 2 * profile u := by
  rw [hselfInverse, hfixed]
  simp [Nat.succ_mul]

end CellProfiles

end AlgebraicComplexity
