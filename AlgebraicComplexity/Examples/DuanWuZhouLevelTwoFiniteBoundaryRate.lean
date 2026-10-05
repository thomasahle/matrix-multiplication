/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteBoundaryProfile
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRegional

/-!
# The admitted full022 profile has its native cofinal boundary weight

This literal composition of the shared fine-cell rate engine formalizes
[duan2023faster], `papers/sources/2210.10173/component_value.tex:468-475`
(the restricted-splitting argument after `thm:zero-i`) and
`prelim.tex:337-367` (`def:restricted_splitting`). The paper counts complete
physical-Z blocks and their within-block dimensions before taking the rate.
The existing `dwz63_exists_fineCellWeight_logVal` engine implements that step;
its two published row instances are applied here to the finite decoder's cell.

The client is literal because it identifies the admitted full022 profile with
the published native nine-pair table. Both endpoint classes and both physical
zero frames remain. A common positive cutoff permits arbitrarily large integral
periods, and every admitted period has an inhabited native source. The rate pays
an arbitrary positive deficit; no exact finite entropy rate, full producing-DAG
Checks, extraction, repair or new exponent bound is asserted.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor

/-- Both admitted full022 zero frames have the published native weight, less
a positive deficit, above one common positive integral cutoff. -/
theorem dwz63Row022Boundary_exists_weight (K : Type*) [CommRing K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, N ≤ j → ∀ zero : Fin 2, ∀ n : ℕ,
      n + 1 = 200000000 * j →
      HasTauWeight K
        (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
          2 dwz63Row022Profile j n).realize dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal022 - ε))) := by
  obtain ⟨NX, hX⟩ := dwz63_exists_fineCellWeight_two K ε hε
  obtain ⟨NY, hY⟩ := dwz63_exists_fineCellWeight_nine K ε hε
  refine ⟨max 1 (max NX NY), le_max_left _ _, ?_⟩
  intro j hj zero n hn
  have hXj : NX ≤ j := (le_max_left NX NY).trans ((le_max_right _ _).trans hj)
  have hYj : NY ≤ j := (le_max_right NX NY).trans ((le_max_right _ _).trans hj)
  simp only [cwBoundaryProfileCell, dwz63Row022Boundary_counts]
  fin_cases zero
  · exact hX j hXj n hn
  · simp only [Nat.one_ne_zero, ite_false, dwz63AlphaTilde_two_eq_nine]
    exact hY j hYj n hn

/-- The canonical positive-period schedule gives an inhabited actual full022
source and its native weight in both frames at every sufficiently large period. -/
theorem dwz63Row022Boundary_exists_cofinalWeight (K : Type*) [CommRing K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, N ≤ j → ∀ zero : Fin 2,
      (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
        2 dwz63Row022Profile j (200000000 * j - 1)).support.Nonempty ∧
      HasTauWeight K
        (cwBoundaryProfileCell K 6 (if zero.val = 0 then Leg.X else Leg.Y)
          2 dwz63Row022Profile j (200000000 * j - 1)).realize dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal022 - ε))) := by
  obtain ⟨N, hN, hweight⟩ := dwz63Row022Boundary_exists_weight K ε hε
  refine ⟨N, hN, fun j hj zero ↦ ?_⟩
  have hjpos : 0 < j := lt_of_lt_of_le (by decide : 0 < 1) (hN.trans hj)
  refine ⟨(dwz63Row022Boundary_nonempty K zero j hjpos).1,
    hweight j hj zero (200000000 * j - 1) ?_⟩
  have hpos : 0 < 200000000 * j := Nat.mul_pos (by decide) hjpos
  omega

end AlgebraicComplexity.Examples
