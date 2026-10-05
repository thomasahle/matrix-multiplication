/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HoleRepair
import AlgebraicComplexity.MatrixMultiplication.InterfaceHoleRepairDepth
import AlgebraicComplexity.MatrixMultiplication.SparseRepairOutputCount

/-!
# Fixed-type output counts for repaired CW compatibility targets

This module is the finite arithmetic boundary between target-specific compatibility repair and a
literal number of intact outputs.  The quotient is taken from the selected fixed-type class,
after type selection and before sparse repair.  It deliberately imports no entropy or
type-asymptotic module.
The separate `CoppersmithWinogradCompatibilityTargetOutputCount` file proves that the explicit
finite loss is subexponential.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AlgebraicComplexity.Tensor

universe v

/-- One-leg logarithmic repair depth used by the finite output-count adapter. -/
def cwOutputInterfaceRepairDepth (r : ℕ) : ℕ :=
  Nat.clog (r + 2) (3 ^ r)

/-- Natural-valued uniform upper bound on one complete target repair tree. -/
def cwProportionalTargetRepairBudgetNat (width r : ℕ) : ℕ :=
  HoleRepair.sevenBranchBudget
    (3 * width * cwOutputInterfaceRepairDepth r)

/-- The natural repair-tree majorant always contains at least its root copy. -/
theorem cwProportionalTargetRepairBudgetNat_pos (width r : ℕ) :
    0 < cwProportionalTargetRepairBudgetNat width r := by
  have hone : 1 ≤ cwProportionalTargetRepairBudgetNat width r := by
    simpa [cwProportionalTargetRepairBudgetNat] using
      HoleRepair.sevenBranchBudget_monotone
        (show 0 ≤ 3 * width * cwOutputInterfaceRepairDepth r by omega)
  omega

/-- Literal integral output count formed from the selected fixed-type class.  The denominator
`2 * repairBudget` is exactly the candidate-independent supply charge. -/
def cwFixedTypeTargetRepairOutputCount
    (width r fixedTypeCard : ℕ) : ℕ :=
  fixedTypeRepairOutputCount fixedTypeCard
    (cwProportionalTargetRepairBudgetNat width r)

/-- At least one repaired output is requested once one doubled repair budget fits in the selected
fixed-type class. -/
theorem cwFixedTypeTargetRepairOutputCount_pos_of_fits
    (width r fixedTypeCard : ℕ)
    (hfits : 2 * cwProportionalTargetRepairBudgetNat width r ≤ fixedTypeCard) :
    0 < cwFixedTypeTargetRepairOutputCount width r fixedTypeCard := by
  unfold cwFixedTypeTargetRepairOutputCount fixedTypeRepairOutputCount
  exact Nat.div_pos hfits
    (Nat.mul_pos (Nat.succ_pos 1)
      (cwProportionalTargetRepairBudgetNat_pos width r))

/-- Scaling the exponent of `3^r` by a fixed width scales its ceiling-log repair depth by at
most the same width. -/
theorem cwOutput_clog_add_two_three_pow_mul_le (width r : ℕ) :
    Nat.clog (r + 2) (3 ^ (width * r)) ≤
      width * cwOutputInterfaceRepairDepth r := by
  let d := cwOutputInterfaceRepairDepth r
  have hbase : 1 < r + 2 := by omega
  have hsingle : 3 ^ r ≤ (r + 2) ^ d :=
    Nat.le_pow_clog hbase (3 ^ r)
  apply Nat.clog_le_of_le_pow
  calc
    3 ^ (width * r) = (3 ^ r) ^ width := by
      rw [Nat.mul_comm width r, pow_mul]
    _ ≤ ((r + 2) ^ d) ^ width :=
      Nat.pow_le_pow_left hsingle width
    _ = (r + 2) ^ (width * d) := by
      rw [Nat.mul_comm width d, pow_mul]

/-- Three target legs of size at most `3^(width*r)` fit in the uniform repair budget. -/
theorem cwOutput_logarithmicRepairDepth_le_three_mul_width
    {A : Leg → Type v} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c)) (width r : ℕ)
    (hcard : ∀ c, (target c).card ≤ 3 ^ (width * r)) :
    HoleRepair.logarithmicRepairDepth (r + 2) target ≤
      3 * width * cwOutputInterfaceRepairDepth r := by
  have hleg (c : Leg) :
      Nat.clog (r + 2) (target c).card ≤
        width * cwOutputInterfaceRepairDepth r :=
    (Nat.clog_mono_right (r + 2) (hcard c)).trans
      (cwOutput_clog_add_two_three_pow_mul_le width r)
  rw [HoleRepair.logarithmicRepairDepth_eq_three]
  calc
    _ ≤ width * cwOutputInterfaceRepairDepth r +
          width * cwOutputInterfaceRepairDepth r +
          width * cwOutputInterfaceRepairDepth r :=
      add_le_add (add_le_add (hleg .X) (hleg .Y)) (hleg .Z)
    _ = 3 * width * cwOutputInterfaceRepairDepth r := by
      rw [Nat.mul_assoc]
      omega

/-- The actual target repair tree is bounded by the explicit proportional majorant. -/
theorem cwSevenBranchTargetRepairBudget_le_proportional
    {A : Leg → Type*} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c)) (width r : ℕ)
    (hcard : ∀ c, (target c).card ≤ 3 ^ (width * r)) :
    HoleRepair.sevenBranchBudget
        (HoleRepair.logarithmicRepairDepth (r + 2) target) ≤
      cwProportionalTargetRepairBudgetNat width r := by
  exact HoleRepair.sevenBranchBudget_monotone
    (cwOutput_logarithmicRepairDepth_le_three_mul_width target width r hcard)

/-- The fixed-type quotient satisfies the doubled candidate-independent supply, even when the
actual target repair budget is smaller than the convenient proportional majorant. -/
theorem two_mul_cwFixedTypeTargetRepairOutputCount_mul_sevenBranchBudget_le_fixed
    (width r fixedTypeCard : ℕ)
    {A : Leg → Type*} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c))
    (hcard : ∀ c, (target c).card ≤ 3 ^ (width * r)) :
    2 * cwFixedTypeTargetRepairOutputCount width r fixedTypeCard *
        HoleRepair.sevenBranchBudget
          (HoleRepair.logarithmicRepairDepth (r + 2) target) ≤ fixedTypeCard := by
  let copies := cwFixedTypeTargetRepairOutputCount width r fixedTypeCard
  let actualRepairBudget := HoleRepair.sevenBranchBudget
    (HoleRepair.logarithmicRepairDepth (r + 2) target)
  have hbudget : actualRepairBudget ≤ cwProportionalTargetRepairBudgetNat width r :=
    cwSevenBranchTargetRepairBudget_le_proportional target width r hcard
  calc
    2 * copies * actualRepairBudget ≤
        2 * copies * cwProportionalTargetRepairBudgetNat width r :=
      Nat.mul_le_mul_left (2 * copies) hbudget
    _ ≤ fixedTypeCard := by
      simpa only [copies, cwFixedTypeTargetRepairOutputCount] using
        two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed fixedTypeCard
          (cwProportionalTargetRepairBudgetNat width r)

/-- If the simultaneously sparse subfamily contains at least half of the fixed type, the exact
fixed-type quotient also has enough sparse repair plans. -/
theorem cwFixedTypeTargetRepairOutputCount_mul_sevenBranchBudget_le_sparse_of_half
    (width r fixedTypeCard sparseCard : ℕ)
    {A : Leg → Type*} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c))
    (hhalf : fixedTypeCard ≤ 2 * sparseCard)
    (hcard : ∀ c, (target c).card ≤ 3 ^ (width * r)) :
    cwFixedTypeTargetRepairOutputCount width r fixedTypeCard *
        HoleRepair.sevenBranchBudget
          (HoleRepair.logarithmicRepairDepth (r + 2) target) ≤ sparseCard := by
  let copies := cwFixedTypeTargetRepairOutputCount width r fixedTypeCard
  let actualRepairBudget := HoleRepair.sevenBranchBudget
    (HoleRepair.logarithmicRepairDepth (r + 2) target)
  have hbudget : actualRepairBudget ≤ cwProportionalTargetRepairBudgetNat width r :=
    cwSevenBranchTargetRepairBudget_le_proportional target width r hcard
  calc
    copies * actualRepairBudget ≤
        copies * cwProportionalTargetRepairBudgetNat width r :=
      Nat.mul_le_mul_left copies hbudget
    _ ≤ sparseCard := by
      simpa only [copies, cwFixedTypeTargetRepairOutputCount] using
        fixedTypeRepairOutputCount_mul_budget_le_sparse_of_half fixedTypeCard sparseCard
          (cwProportionalTargetRepairBudgetNat width r) hhalf

end AlgebraicComplexity.Examples
