/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Nat.Basic

/-!
# A cofinal integral schedule above a finite cutoff

This formalizes the integral-subsequence convention in [duan2023faster],
`papers/sources/2210.10173/prelim.tex:207,264`, used when taking roots in
`global_value.tex:280-303`. A positive common period and positive repetition unit
give arbitrarily large admissible lengths, all beyond the same scale cutoff.

The schedule uses multiples of the common period, not a coprimality assumption.
Lengths use the existing positive-word convention: `len + 1` is the number of positions.
This arithmetic step supplies no type inhabitant, tensor extraction, seed or analytic bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.WordType

/-- Positive integral periods have a cofinal length family above any scale cutoff.
Proof sketch: take `rep j = common * (cutoff + j + 1)` and `len j = unit * rep j - 1`.
Positivity undoes the subtraction; each factor is at least one, giving both lower bounds. -/
theorem exists_cofinal_integral_schedule (unit common cutoff : Nat)
    (hunit : 0 < unit) (hcommon : 0 < common) :
    ∃ (len rep : Nat → Nat),
      (∀ j, len j + 1 = unit * rep j) ∧
      (∀ bound, ∃ j, bound ≤ len j + 1) ∧
      (∀ j, cutoff ≤ rep j) ∧
      (∀ j, common ∣ rep j) ∧
      (∀ j, 0 < rep j) := by
  let rep : Nat → Nat := fun j => common * (cutoff + j + 1)
  let len : Nat → Nat := fun j => unit * rep j - 1
  have hpos (j : Nat) : 0 < rep j := Nat.mul_pos hcommon (Nat.succ_pos _)
  have hlen (j : Nat) : len j + 1 = unit * rep j :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hunit (hpos j)))
  refine ⟨len, rep, hlen, ?_, ?_, ?_, hpos⟩
  · intro bound
    refine ⟨bound, ?_⟩
    rw [hlen]
    calc
      bound ≤ cutoff + bound + 1 :=
        Nat.le_trans (Nat.le_add_left bound cutoff) (Nat.le_succ _)
      _ ≤ rep bound := Nat.le_mul_of_pos_left _ hcommon
      _ ≤ unit * rep bound := Nat.le_mul_of_pos_left _ hunit
  · intro j
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right cutoff j) (Nat.le_succ _))
      (Nat.le_mul_of_pos_left _ hcommon)
  · intro j
    exact ⟨cutoff + j + 1, rfl⟩

end AlgebraicComplexity.WordType
