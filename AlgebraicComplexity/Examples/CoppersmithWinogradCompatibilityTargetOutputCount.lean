/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetLoss
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputCore

/-!
# Growth of fixed-type repaired CW compatibility outputs

The selected fixed-type class has cardinality `I`; one output is charged the doubled repair
budget, so the exact count is `I / (2 * R)`.  This file transports the strict Euclidean remainder
through the polynomial type-selection loss.  It retains `copies + 1` until an explicit positivity
threshold is proved and only then absorbs that term into a further factor two.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Natural-valued polynomial loss for selecting one complete oriented coarse-cell type. -/
def cwProportionalFullCellTypeSelectionLossNat
    (Part : Type v) [Fintype Part] (depth mass r : ℕ) : ℕ :=
  (mass * r + 1) ^ Fintype.card (CWOrientedCoarseCell Part depth)

@[simp] theorem natCast_cwProportionalFullCellTypeSelectionLossNat
    (Part : Type v) [Fintype Part] (depth mass r : ℕ) :
    (cwProportionalFullCellTypeSelectionLossNat Part depth mass r : ℝ) =
      cwProportionalFullCellTypeSelectionLoss Part depth mass r := by
  unfold cwProportionalFullCellTypeSelectionLossNat
    cwProportionalFullCellTypeSelectionLoss
  norm_cast

@[simp] theorem natCast_cwProportionalTargetRepairBudgetNat
    (width r : ℕ) :
    (cwProportionalTargetRepairBudgetNat width r : ℝ) =
      cwTargetRepairBudgetLoss width r := by
  simp only [cwProportionalTargetRepairBudgetNat, cwOutputInterfaceRepairDepth,
    cwTargetRepairBudgetLoss, HoleRepair.interfaceRepairDepth]

/-- The post-positivity natural loss `4 * L * R` is twice the previously packaged proportional
target-repair loss `2 * L * R`. -/
theorem natCast_four_mul_cwFixedTypeTargetLosses
    (Part : Type v) [Fintype Part] (depth mass width r : ℕ) :
    ((4 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
        cwProportionalTargetRepairBudgetNat width r : ℕ) : ℝ) =
      2 * cwProportionalTargetRepairLoss Part depth mass width r := by
  simp only [Nat.cast_mul, Nat.cast_ofNat,
    natCast_cwProportionalFullCellTypeSelectionLossNat,
    natCast_cwProportionalTargetRepairBudgetNat,
    cwProportionalTargetRepairLoss]
  ring

/-- Real-valued loss after the fixed-type quotient and its explicit positivity bootstrap. -/
noncomputable def cwFixedTypeTargetOutputQuotientLoss
    (Part : Type v) [Fintype Part] (depth mass width r : ℕ) : ℝ :=
  2 * cwProportionalTargetRepairLoss Part depth mass width r

/-- The complete fixed-type output-count loss is subexponential in the proportional repetition. -/
theorem cwFixedTypeTargetOutputQuotientLoss_subexponential
    (Part : Type v) [Fintype Part] (depth mass width : ℕ)
    (hwidth : 0 < width) :
    Growth.Subexponential
      (cwFixedTypeTargetOutputQuotientLoss Part depth mass width) := by
  unfold cwFixedTypeTargetOutputQuotientLoss
  exact (cwProportionalTargetRepairLoss_subexponential
    Part depth mass width hwidth).const_mul (by norm_num)

/-- Multiplying an existing positive subexponential ambient loss by the fixed-type quotient loss
preserves subexponentiality. -/
theorem cwFixedTypeTargetOutput_combinedLoss_subexponential
    (Part : Type v) [Fintype Part] (depth mass width : ℕ)
    (hwidth : 0 < width) (ambientLoss : ℕ → ℝ)
    (hambient : Growth.Subexponential ambientLoss) :
    Growth.Subexponential (fun r ↦ ambientLoss r *
      cwFixedTypeTargetOutputQuotientLoss Part depth mass width r) :=
  hambient.mul
    (cwFixedTypeTargetOutputQuotientLoss_subexponential
      Part depth mass width hwidth)

/-- Exact strict floor remainder before positivity. -/
theorem familyCard_lt_two_mul_cwTargetLosses_mul_fixedTypeCount_add_one
    (Part : Type v) [Fintype Part]
    (depth mass width r familyCard fixedTypeCard : ℕ)
    (htype : familyCard ≤
      cwProportionalFullCellTypeSelectionLossNat Part depth mass r * fixedTypeCard) :
    familyCard <
      2 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
        cwProportionalTargetRepairBudgetNat width r *
          (cwFixedTypeTargetRepairOutputCount width r fixedTypeCard + 1) := by
  simpa only [cwFixedTypeTargetRepairOutputCount] using
    total_lt_two_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount_add_one
      familyCard
      (cwProportionalFullCellTypeSelectionLossNat Part depth mass r)
      fixedTypeCard (cwProportionalTargetRepairBudgetNat width r)
      (by unfold cwProportionalFullCellTypeSelectionLossNat; positivity)
      (cwProportionalTargetRepairBudgetNat_pos width r) htype

/-- Once one complete selected-type denominator fits, the pre-type family loses at most the
explicit positive subexponential quotient factor. -/
theorem natCast_familyCard_le_cwFixedTypeTargetOutputQuotientLoss_mul_count
    (Part : Type v) [Fintype Part]
    (depth mass width r familyCard fixedTypeCard : ℕ)
    (htype : familyCard ≤
      cwProportionalFullCellTypeSelectionLossNat Part depth mass r * fixedTypeCard)
    (hfits :
      2 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
        cwProportionalTargetRepairBudgetNat width r ≤ familyCard) :
    (familyCard : ℝ) ≤
      cwFixedTypeTargetOutputQuotientLoss Part depth mass width r *
        (cwFixedTypeTargetRepairOutputCount width r fixedTypeCard : ℕ) := by
  have hnat := total_le_four_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount
    familyCard
    (cwProportionalFullCellTypeSelectionLossNat Part depth mass r)
    fixedTypeCard (cwProportionalTargetRepairBudgetNat width r)
    (by unfold cwProportionalFullCellTypeSelectionLossNat; positivity)
    (cwProportionalTargetRepairBudgetNat_pos width r) htype hfits
  have hreal : (familyCard : ℝ) ≤
      ((4 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
          cwProportionalTargetRepairBudgetNat width r *
          cwFixedTypeTargetRepairOutputCount width r fixedTypeCard : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_mul, natCast_four_mul_cwFixedTypeTargetLosses] at hreal
  exact hreal

/-- Compose any pre-type family-growth estimate with the exact fixed-type quotient bound. -/
theorem pow_le_ambientLoss_mul_cwFixedTypeTargetOutputQuotientLoss_mul_count
    (Part : Type v) [Fintype Part]
    (depth mass width r familyCard fixedTypeCard : ℕ)
    (base ambientLoss : ℝ)
    (hambientLoss : 0 ≤ ambientLoss)
    (hfamily : base ^ r ≤ ambientLoss * (familyCard : ℝ))
    (htype : familyCard ≤
      cwProportionalFullCellTypeSelectionLossNat Part depth mass r * fixedTypeCard)
    (hfits :
      2 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
        cwProportionalTargetRepairBudgetNat width r ≤ familyCard) :
    base ^ r ≤
      (ambientLoss * cwFixedTypeTargetOutputQuotientLoss
        Part depth mass width r) *
        (cwFixedTypeTargetRepairOutputCount width r fixedTypeCard : ℕ) := by
  have hquotient :=
    natCast_familyCard_le_cwFixedTypeTargetOutputQuotientLoss_mul_count
      Part depth mass width r familyCard fixedTypeCard htype hfits
  calc
    base ^ r ≤ ambientLoss * (familyCard : ℝ) := hfamily
    _ ≤ ambientLoss *
        (cwFixedTypeTargetOutputQuotientLoss Part depth mass width r *
          (cwFixedTypeTargetRepairOutputCount width r fixedTypeCard : ℕ)) :=
      mul_le_mul_of_nonneg_left hquotient hambientLoss
    _ = (ambientLoss * cwFixedTypeTargetOutputQuotientLoss
        Part depth mass width r) *
          (cwFixedTypeTargetRepairOutputCount width r fixedTypeCard : ℕ) := by ring

end AlgebraicComplexity.Examples
