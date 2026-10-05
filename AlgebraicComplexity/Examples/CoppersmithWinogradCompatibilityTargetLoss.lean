/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetFiber
import AlgebraicComplexity.MatrixMultiplication.InterfaceRepairGrowth

/-!
# Subexponential losses for proportional CW compatibility targets

This module contains only the candidate-independent analytic losses used after selection of one
full tagged/oriented target type.  It deliberately omits compatibility repair semantics and
aggregate incidence counting, so numerical and asymptotic clients can import the loss laws alone.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Explicit majorant for the repair-tree budget of a proportional exact target. -/
noncomputable def cwTargetRepairBudgetLoss (width r : ℕ) : ℝ :=
  (HoleRepair.sevenBranchBudget
    (3 * width * HoleRepair.interfaceRepairDepth r) : ℕ)

/-- The proportional target repair budget is subexponential for every positive fixed width. -/
theorem cwTargetRepairBudgetLoss_subexponential
    (width : ℕ) (hwidth : 0 < width) :
    Growth.Subexponential (cwTargetRepairBudgetLoss width) := by
  have hpow : Growth.Subexponential
      (fun r ↦ HoleRepair.interfaceRepairLoss r ^ width) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Growth.Subexponential.fintype_prod
        (I := Fin width) (fun _i _r ↦ HoleRepair.interfaceRepairLoss _r)
        (fun _i ↦ HoleRepair.interfaceRepairLoss_subexponential)
  apply hpow.mono
  · intro r
    unfold cwTargetRepairBudgetLoss
    positivity
  · intro r
    have hbudget := HoleRepair.sevenBranchBudget_le_pow
      (3 * width * HoleRepair.interfaceRepairDepth r)
    have hexponent :
        3 * width * HoleRepair.interfaceRepairDepth r + 1 ≤
          (3 * HoleRepair.interfaceRepairDepth r + 1) * width := by
      nlinarith
    calc
      cwTargetRepairBudgetLoss width r ≤
          (7 : ℝ) ^ (3 * width * HoleRepair.interfaceRepairDepth r + 1) := by
        unfold cwTargetRepairBudgetLoss
        exact_mod_cast hbudget
      _ ≤ (7 : ℝ) ^
          ((3 * HoleRepair.interfaceRepairDepth r + 1) * width) :=
        pow_le_pow_right₀ (by norm_num) hexponent
      _ = HoleRepair.interfaceRepairLoss r ^ width := by
        unfold HoleRepair.interfaceRepairLoss
        rw [pow_mul]

/-- Type-selection loss for a proportional word family with `mass*r` samples. -/
noncomputable def cwProportionalFullCellTypeSelectionLoss
    (Part : Type v) [Fintype Part] (depth mass r : ℕ) : ℝ :=
  ((((mass * r + 1 : ℕ) : ℝ))) ^
    Fintype.card (CWOrientedCoarseCell Part depth)

/-- Fixed rational full-cell types incur only polynomial, hence subexponential, selection loss. -/
theorem cwProportionalFullCellTypeSelectionLoss_subexponential
    (Part : Type v) [Fintype Part] (depth mass : ℕ) :
    Growth.Subexponential
      (cwProportionalFullCellTypeSelectionLoss Part depth mass) := by
  let degree := Fintype.card (CWOrientedCoarseCell Part depth)
  have hmajor := (Growth.Subexponential.natCast_succ_pow degree).const_mul
    (show (0 : ℝ) ≤ (mass + 1 : ℝ) ^ degree by positivity)
  apply hmajor.mono
  · intro r
    unfold cwProportionalFullCellTypeSelectionLoss
    positivity
  · intro r
    unfold cwProportionalFullCellTypeSelectionLoss
    have hbase : (((mass * r + 1 : ℕ) : ℝ)) ≤
        (mass + 1 : ℝ) * (((r + 1 : ℕ) : ℝ)) := by
      push_cast
      nlinarith
    calc
      (((mass * r + 1 : ℕ) : ℝ)) ^ degree ≤
          ((mass + 1 : ℝ) * (((r + 1 : ℕ) : ℝ))) ^ degree := by
        exact pow_le_pow_left₀ (by positivity) hbase _
      _ = (mass + 1 : ℝ) ^ degree *
          (((r + 1 : ℕ) : ℝ)) ^ degree := by
        rw [mul_pow]

/-- Combined candidate-independent type, sparse-threshold, and repair-supply loss. -/
noncomputable def cwProportionalTargetRepairLoss
    (Part : Type v) [Fintype Part] (depth mass width r : ℕ) : ℝ :=
  2 * cwProportionalFullCellTypeSelectionLoss Part depth mass r *
    cwTargetRepairBudgetLoss width r

/-- The complete candidate-independent loss above the exact competitor-incidence estimate is
subexponential. -/
theorem cwProportionalTargetRepairLoss_subexponential
    (Part : Type v) [Fintype Part] (depth mass width : ℕ)
    (hwidth : 0 < width) :
    Growth.Subexponential
      (cwProportionalTargetRepairLoss Part depth mass width) := by
  unfold cwProportionalTargetRepairLoss
  exact ((cwProportionalFullCellTypeSelectionLoss_subexponential
    Part depth mass).const_mul (by norm_num)).mul
      (cwTargetRepairBudgetLoss_subexponential width hwidth)

end AlgebraicComplexity.Examples
