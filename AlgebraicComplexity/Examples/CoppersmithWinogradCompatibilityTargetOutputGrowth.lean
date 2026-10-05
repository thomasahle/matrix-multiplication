/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.SubexponentialDenominator
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputCount

/-!
# Eventual positivity of repaired CW compatibility outputs

The fixed-type repair quotient is positive once its exact denominator
`2 * typeSelectionLoss * repairBudget` fits in the pre-type family.  That denominator is
subexponential.  Consequently an exponentially growing pre-type family satisfies the fit
condition automatically after one finite cutoff.

The final theorem preserves the original exponential base in the output-count inequality.  The
smaller intermediate base is used only to prove eventual positivity.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

universe v

/-- The exact natural denominator used before taking the fixed-type repair quotient. -/
def cwFixedTypeTargetOutputDenominatorNat
    (Part : Type v) [Fintype Part] (depth mass width r : ℕ) : ℕ :=
  2 * cwProportionalFullCellTypeSelectionLossNat Part depth mass r *
    cwProportionalTargetRepairBudgetNat width r

@[simp] theorem natCast_cwFixedTypeTargetOutputDenominatorNat
    (Part : Type v) [Fintype Part] (depth mass width r : ℕ) :
    (cwFixedTypeTargetOutputDenominatorNat Part depth mass width r : ℝ) =
      cwProportionalTargetRepairLoss Part depth mass width r := by
  simp only [cwFixedTypeTargetOutputDenominatorNat, Nat.cast_mul, Nat.cast_ofNat,
    natCast_cwProportionalFullCellTypeSelectionLossNat,
    natCast_cwProportionalTargetRepairBudgetNat,
    cwProportionalTargetRepairLoss]

/-- The exact integral quotient denominator is subexponential. -/
theorem cwFixedTypeTargetOutputDenominatorNat_subexponential
    (Part : Type v) [Fintype Part] (depth mass width : ℕ) (hwidth : 0 < width) :
    Growth.Subexponential
      (fun r ↦ (cwFixedTypeTargetOutputDenominatorNat Part depth mass width r : ℝ)) := by
  simpa only [natCast_cwFixedTypeTargetOutputDenominatorNat] using
    cwProportionalTargetRepairLoss_subexponential Part depth mass width hwidth

/-- An exponentially growing pre-type family eventually contains one full type-selection and
repair denominator. -/
theorem exists_cutoff_cwFixedTypeTargetOutputDenominatorNat_le_familyCard
    (Part : Type v) [Fintype Part] (depth mass width : ℕ) (hwidth : 0 < width)
    (base : ℝ) (hbase : 1 < base) (ambientLoss : ℕ → ℝ)
    (hambient : Growth.Subexponential ambientLoss) (familyCard : ℕ → ℕ)
    (hfamily : ∀ r, base ^ r ≤ ambientLoss r * (familyCard r : ℝ)) :
    ∃ cutoff : ℕ, ∀ r, cutoff ≤ r →
      cwFixedTypeTargetOutputDenominatorNat Part depth mass width r ≤ familyCard r :=
  Growth.Subexponential.exists_forall_natCast_denominator_le_count_of_pow_le_mul
    hbase hambient
      (cwFixedTypeTargetOutputDenominatorNat_subexponential
        Part depth mass width hwidth)
      hfamily

/-- After a finite cutoff, the exact fixed-type quotient preserves the ambient exponential base
up to the explicit product of the ambient loss and the quotient loss.

This is the sequence-facing form of the positivity bootstrap: clients supply the pre-type family
growth and the ordinary largest-type inequality, but no separate `hfits` premise. -/
theorem exists_cutoff_pow_le_ambientLoss_mul_cwFixedTypeTargetOutputQuotientLoss_mul_count
    (Part : Type v) [Fintype Part] (depth mass width : ℕ) (hwidth : 0 < width)
    (base : ℝ) (hbase : 1 < base) (ambientLoss : ℕ → ℝ)
    (hambient : Growth.Subexponential ambientLoss)
    (familyCard fixedTypeCard : ℕ → ℕ)
    (hfamily : ∀ r, base ^ r ≤ ambientLoss r * (familyCard r : ℝ))
    (htype : ∀ r, familyCard r ≤
      cwProportionalFullCellTypeSelectionLossNat Part depth mass r * fixedTypeCard r) :
    ∃ cutoff : ℕ, ∀ r, cutoff ≤ r →
      base ^ r ≤
        (ambientLoss r * cwFixedTypeTargetOutputQuotientLoss
          Part depth mass width r) *
          (cwFixedTypeTargetRepairOutputCount width r (fixedTypeCard r) : ℕ) := by
  obtain ⟨cutoff, hfits⟩ :=
    exists_cutoff_cwFixedTypeTargetOutputDenominatorNat_le_familyCard
      Part depth mass width hwidth base hbase ambientLoss hambient familyCard hfamily
  refine ⟨cutoff, fun r hr ↦ ?_⟩
  exact pow_le_ambientLoss_mul_cwFixedTypeTargetOutputQuotientLoss_mul_count
    Part depth mass width r (familyCard r) (fixedTypeCard r) base (ambientLoss r)
      (hambient.nonneg r) (hfamily r) (htype r) (hfits r hr)

end AlgebraicComplexity.Examples
