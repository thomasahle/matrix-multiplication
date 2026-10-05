/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralPeriodSchedule
import Mathlib.Tactic.NormNum

/-!
# The DWZ second-power instance of the integral schedule

This instantiates [duan2023faster]'s integral-subsequence convention
(`papers/sources/2210.10173/prelim.tex:207,264`) at the section 6.3 data
(`global_value.tex:332-378`). It preserves the existing repetition unit and both
leaf divisibilities consumed by `DuanWuZhouLevelTwoAssemblyOrbitClosure`.

Only finite positive integer data are supplied to the shared schedule theorem.
The new schedule does not replace the existing seed, leaf or loss proofs, and
is not the complete finite-certificate checker or a new exponent theorem.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

/-- One common schedule satisfies the literal period equation, both leaf divisibilities,
positivity, cofinality and any scale cutoff required by the existing seeded endpoint. -/
theorem dwz63_finitePeriod_schedule (cutoff : Nat) :
    ∃ (len rep : Nat → Nat),
      (∀ j, len j + 1 = 20000000000000000 * rep j) ∧
      (∀ bound, ∃ j, bound ≤ len j + 1) ∧
      (∀ j, cutoff ≤ rep j) ∧
      (∀ j, 40000000000000 ∣ rep j ∧ 312500000000000000000 ∣ rep j) ∧
      (∀ j, 0 < rep j) := by
  obtain ⟨len, rep, hlen, hcofinal, hcutoff, hdiv, hpos⟩ :=
    WordType.exists_cofinal_integral_schedule 20000000000000000
      (40000000000000 * 312500000000000000000) cutoff
      (by norm_num) (Nat.mul_pos (by norm_num) (by norm_num))
  refine ⟨len, rep, hlen, hcofinal, hcutoff, ?_, hpos⟩
  intro j
  have hfirst : 40000000000000 ∣ 40000000000000 * 312500000000000000000 :=
    ⟨312500000000000000000, rfl⟩
  have hsecond : 312500000000000000000 ∣ 40000000000000 * 312500000000000000000 :=
    ⟨40000000000000, Nat.mul_comm _ _⟩
  exact ⟨Nat.dvd_trans hfirst (hdiv j), Nat.dvd_trans hsecond (hdiv j)⟩

end AlgebraicComplexity.Examples
