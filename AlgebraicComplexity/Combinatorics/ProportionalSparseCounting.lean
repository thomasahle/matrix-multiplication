/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Nat.Basic

/-!
# Proportional sparse-family counting

This module isolates the elementary arithmetic behind largest-type selection followed by a
three-coordinate sparse-family selection.  If a fixed type is covered by the sparse family and
an exceptional budget, and that budget occupies at most half of the fixed type, then the original
family is bounded by twice the type-selection loss times the sparse family.
-/

namespace AlgebraicComplexity

/-- A type-selection loss and a half-density cover compose with only one additional factor two. -/
theorem card_le_two_mul_loss_mul_sparse_of_cover
    (total typeLoss fixed sparse budget : ℕ)
    (htype : total ≤ typeLoss * fixed)
    (hcover : fixed ≤ sparse + budget)
    (hhalf : 2 * budget ≤ fixed) :
    total ≤ (2 * typeLoss) * sparse := by
  have htwiceBudget : budget + budget ≤ sparse + budget := by
    calc
      budget + budget = 2 * budget := (Nat.two_mul budget).symm
      _ ≤ fixed := hhalf
      _ ≤ sparse + budget := hcover
  have hbudget : budget ≤ sparse :=
    Nat.add_le_add_iff_right.mp htwiceBudget
  have hfixed : fixed ≤ 2 * sparse := by
    calc
      fixed ≤ sparse + budget := hcover
      _ ≤ sparse + sparse := Nat.add_le_add_left hbudget sparse
      _ = 2 * sparse := (Nat.two_mul sparse).symm
  calc
    total ≤ typeLoss * fixed := htype
    _ ≤ typeLoss * (2 * sparse) := Nat.mul_le_mul_left typeLoss hfixed
    _ = (typeLoss * 2) * sparse := (Nat.mul_assoc typeLoss 2 sparse).symm
    _ = (2 * typeLoss) * sparse := by rw [Nat.mul_comm typeLoss 2]

/-! ## Exact fixed-type repair quotient -/

/-- The largest integral copy count forced by the candidate-independent supply of one fixed
type.  Each output is charged twice its repair budget: once for the chosen damaged copies and
once for the candidate-independent reserve. -/
def fixedTypeRepairOutputCount (fixedCard repairBudget : ℕ) : ℕ :=
  fixedCard / (2 * repairBudget)

/-- The fixed-type quotient satisfies the candidate-independent supply inequality exactly. -/
theorem two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed
    (fixedCard repairBudget : ℕ) :
    2 * fixedTypeRepairOutputCount fixedCard repairBudget * repairBudget ≤ fixedCard := by
  have hdivision := Nat.mul_div_le fixedCard (2 * repairBudget)
  simpa only [fixedTypeRepairOutputCount, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hdivision

/-- If at least half of a fixed type is simultaneously sparse, the same quotient also has enough
sparse repair plans.  This is distinct from the doubled fixed-type supply above. -/
theorem fixedTypeRepairOutputCount_mul_budget_le_sparse_of_half
    (fixedCard sparseCard repairBudget : ℕ)
    (hhalf : fixedCard ≤ 2 * sparseCard) :
    fixedTypeRepairOutputCount fixedCard repairBudget * repairBudget ≤ sparseCard := by
  have hscaled :
      2 * (fixedTypeRepairOutputCount fixedCard repairBudget * repairBudget) ≤
        2 * sparseCard := by
    calc
      2 * (fixedTypeRepairOutputCount fixedCard repairBudget * repairBudget) =
          2 * fixedTypeRepairOutputCount fixedCard repairBudget * repairBudget := by
        rw [Nat.mul_assoc]
      _ ≤ fixedCard :=
        two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed
          fixedCard repairBudget
      _ ≤ 2 * sparseCard := hhalf
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.succ_pos 1)

/-- Before positivity is known, type selection and Euclidean division give an exact `copies + 1`
remainder.  Keeping this strict bound avoids the usual circular floor argument. -/
theorem total_lt_two_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount_add_one
    (total typeLoss fixedCard repairBudget : ℕ)
    (htypeLoss : 0 < typeLoss) (hrepairBudget : 0 < repairBudget)
    (htype : total ≤ typeLoss * fixedCard) :
    total < 2 * typeLoss * repairBudget *
      (fixedTypeRepairOutputCount fixedCard repairBudget + 1) := by
  have hdenominator : 0 < 2 * repairBudget :=
    Nat.mul_pos (Nat.succ_pos 1) hrepairBudget
  have hremainder : fixedCard <
      (2 * repairBudget) *
        (fixedTypeRepairOutputCount fixedCard repairBudget + 1) := by
    simpa only [fixedTypeRepairOutputCount] using
      Nat.lt_mul_div_succ fixedCard hdenominator
  have hscaled := Nat.mul_lt_mul_of_pos_left hremainder htypeLoss
  exact lt_of_le_of_lt htype (by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled)

/-- The fixed-type quotient is positive once one complete doubled repair budget fits after the
type-selection loss. -/
theorem fixedTypeRepairOutputCount_pos_of_total_fits
    (total typeLoss fixedCard repairBudget : ℕ)
    (htypeLoss : 0 < typeLoss) (hrepairBudget : 0 < repairBudget)
    (htype : total ≤ typeLoss * fixedCard)
    (hfits : 2 * typeLoss * repairBudget ≤ total) :
    0 < fixedTypeRepairOutputCount fixedCard repairBudget := by
  have hscaled : typeLoss * (2 * repairBudget) ≤ typeLoss * fixedCard := by
    calc
      typeLoss * (2 * repairBudget) = 2 * typeLoss * repairBudget := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ total := hfits
      _ ≤ typeLoss * fixedCard := htype
  have hfixed : 2 * repairBudget ≤ fixedCard :=
    Nat.le_of_mul_le_mul_left hscaled htypeLoss
  unfold fixedTypeRepairOutputCount
  exact Nat.div_pos hfixed (Nat.mul_pos (Nat.succ_pos 1) hrepairBudget)

/-- After the explicit positivity bootstrap, the exact remainder loses only the expected further
factor two. -/
theorem total_le_four_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount
    (total typeLoss fixedCard repairBudget : ℕ)
    (htypeLoss : 0 < typeLoss) (hrepairBudget : 0 < repairBudget)
    (htype : total ≤ typeLoss * fixedCard)
    (hfits : 2 * typeLoss * repairBudget ≤ total) :
    total ≤ 4 * typeLoss * repairBudget *
      fixedTypeRepairOutputCount fixedCard repairBudget := by
  let copies := fixedTypeRepairOutputCount fixedCard repairBudget
  have hcopies : 0 < copies := by
    exact fixedTypeRepairOutputCount_pos_of_total_fits
      total typeLoss fixedCard repairBudget htypeLoss hrepairBudget htype hfits
  have hadd : copies + 1 ≤ 2 * copies := by
    calc
      copies + 1 ≤ copies + copies := Nat.add_le_add_left hcopies copies
      _ = 2 * copies := (Nat.two_mul copies).symm
  have hremainder :=
    total_lt_two_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount_add_one
      total typeLoss fixedCard repairBudget htypeLoss hrepairBudget htype
  calc
    total ≤ 2 * typeLoss * repairBudget * (copies + 1) := by
      simpa only [copies] using Nat.le_of_lt hremainder
    _ ≤ 2 * typeLoss * repairBudget * (2 * copies) :=
      Nat.mul_le_mul_left (2 * typeLoss * repairBudget) hadd
    _ = 4 * typeLoss * repairBudget * copies := by
      simp only [show (4 : ℕ) = 2 * 2 by rfl, Nat.mul_comm, Nat.mul_left_comm]

end AlgebraicComplexity
