/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm
import MatrixMultiplication.LevelFourA5OccurrenceProgramCore
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualFormRescale
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Exact semantic contract for one paired total-weight A5 row

The frozen paired checker stores a level-four top row at denominator `2 ^ 32`.  The recursive
Lean source stores the same top row at denominator `2 ^ 20` and then multiplies it by two
independent child profiles of size `2 ^ 48`.  Thus the literal occurrence profile is the checker
row multiplied by `2 ^ 84`, and its retained form lives at width 116.

This module makes that scale boundary load-bearing.  It is parameterized by arbitrary top rows,
so the generated replacement client must bind the record to its own SHA-pinned table.  It does
not import the obsolete selected-node wrapper or any generated certificate.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open scoped BigOperators

namespace MatrixMultiplication.PairedTotalWeightA5Row

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm
open MatrixMultiplication.LevelFourA5OccurrenceProgram
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualFormRescale

noncomputable section

/-- One frozen b32 checker row, exactly bound to a supplied b20 level-four top table.  The
replacement certificate uses the diagonal root/region and the fixed `xzy` orientation. -/
structure Row (top : TopBranchRows) where
  region : Fin 6
  parent : Fin positiveLevelFourShapeCount
  count32 : LevelFourValidSlot parent → ℕ
  count32_eq_top : ∀ slot,
    count32 slot =
      levelFourSlotNumerator top region region parent slot *
        AlgebraicComplexity.dyadicDenominator 12
  count32Mass_pos : 0 < WordType.profileMass count32
  weights : CategoricalIntegerWeights parent xzy

/-- The two depth-three child profiles contribute precisely the b32-to-b116 scale. -/
theorem levelFourChildSamples_sq_eq_dyadicScales :
    levelFourChildSamples * levelFourChildSamples =
      AlgebraicComplexity.dyadicDenominator 12 *
        AlgebraicComplexity.dyadicDenominator 84 := by
  norm_num [levelFourChildSamples, childBits, AlgebraicComplexity.dyadicDenominator]

namespace Row

variable {top : TopBranchRows}

/-- Pointwise, the semantic occurrence profile is the frozen b32 checker row rescaled by
`2 ^ 84`. -/
theorem occurrenceProfile_apply_eq_count32_rescale
    (row : Row top) (slot : LevelFourValidSlot row.parent) :
    levelFourOccurrenceSourceProfile top row.region row.region row.parent slot =
      row.count32 slot * AlgebraicComplexity.dyadicDenominator 84 := by
  unfold levelFourOccurrenceSourceProfile
  calc
    levelFourSlotNumerator top row.region row.region row.parent slot *
          (levelFourChildSamples * levelFourChildSamples) =
        levelFourSlotNumerator top row.region row.region row.parent slot *
          (AlgebraicComplexity.dyadicDenominator 12 *
            AlgebraicComplexity.dyadicDenominator 84) := by
      rw [levelFourChildSamples_sq_eq_dyadicScales]
    _ =
        (levelFourSlotNumerator top row.region row.region row.parent slot *
          AlgebraicComplexity.dyadicDenominator 12) *
            AlgebraicComplexity.dyadicDenominator 84 :=
      (Nat.mul_assoc _ _ _).symm
    _ = row.count32 slot * AlgebraicComplexity.dyadicDenominator 84 :=
      congrArg (· * AlgebraicComplexity.dyadicDenominator 84)
        (row.count32_eq_top slot).symm

/-- Function form of the exact b32-to-b116 occurrence-profile identity. -/
theorem occurrenceProfile_eq_count32_rescale (row : Row top) :
    levelFourOccurrenceSourceProfile top row.region row.region row.parent =
      fun slot ↦ row.count32 slot * AlgebraicComplexity.dyadicDenominator 84 := by
  funext slot
  exact row.occurrenceProfile_apply_eq_count32_rescale slot

/-- Positivity of the frozen checker row implies positivity of the semantic occurrence row. -/
theorem occurrenceProfileMass_pos (row : Row top) :
    0 < WordType.profileMass
      (levelFourOccurrenceSourceProfile top row.region row.region row.parent) := by
  rw [row.occurrenceProfile_eq_count32_rescale]
  change 0 < ∑ slot,
    row.count32 slot * AlgebraicComplexity.dyadicDenominator 84
  rw [← Finset.sum_mul]
  exact Nat.mul_pos
    (by simpa only [WordType.profileMass] using row.count32Mass_pos)
    (by norm_num [AlgebraicComplexity.dyadicDenominator])

/-- Exact positive parent-mass premise consumed by the certificate-parameterized A5 program. -/
theorem parentMass_pos (row : Row top) :
    0 < levelFourParentSamples top row.region row.region row.parent := by
  rw [← profileMass_levelFourOccurrenceSourceProfile]
  exact row.occurrenceProfileMass_pos

/-- The semantic A5 program attached to one replacement-certificate row. -/
noncomputable def program (row : Row top) : Program row.parent xzy :=
  cwLevelFourOccurrenceA5Program top row.region row.region row.parent xzy
    row.parentMass_pos row.weights

@[simp] theorem program_stateProfile (row : Row top) :
    row.program.stateProfile =
      levelFourOccurrenceSourceProfile top row.region row.region row.parent :=
  rfl

@[simp] theorem program_weights (row : Row top) : row.program.weights = row.weights :=
  rfl

/-- The constructed program exposes exactly the rescaled frozen checker row. -/
theorem program_stateProfile_eq_count32_rescale (row : Row top) :
    row.program.stateProfile =
      fun slot ↦ row.count32 slot * AlgebraicComplexity.dyadicDenominator 84 := by
  rw [row.program_stateProfile, row.occurrenceProfile_eq_count32_rescale]

/-- Exact width-32 form serialized and bounded by the frozen paired checker. -/
def checkerRetainedForm32 (row : Row top) : Form :=
  retainedRowForm 32
    (levelFourA5Coordinate row.parent xzy .Z)
    row.count32 (categoricalProductWeight row.weights)

/-- Literal width-116 retained form of the semantic occurrence program. -/
noncomputable def semanticRetainedForm116 (row : Row top) : Form :=
  categoricalRetainedForm 116 row.program

/-- The semantic width-116 form and frozen width-32 checker form have exactly equal evaluation. -/
theorem semanticRetainedForm116_eval_eq_checkerRetainedForm32_eval (row : Row top) :
    Form.eval 116 row.semanticRetainedForm116 =
      Form.eval 32 row.checkerRetainedForm32 := by
  simpa only [semanticRetainedForm116, categoricalRetainedForm,
      program_stateProfile_eq_count32_rescale, program_weights,
      checkerRetainedForm32] using
    (retainedRowForm_eval_rescale 32 84
      (levelFourA5Coordinate row.parent xzy .Z)
      row.count32 (categoricalProductWeight row.weights))

end Row

end

end MatrixMultiplication.PairedTotalWeightA5Row
