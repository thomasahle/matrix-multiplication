/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore

set_option autoImplicit false

/-!
# Lightweight constructor for a level-four A5 occurrence program

This core attaches positive categorical weights to the exact occurrence profile used in the
Coppersmith--Winograd analysis (`coppersmith1990matrix`).  It proves only profile positivity and
constructs the finite program.  Feasibility, joint-law reconstruction, and ordered-state counting
remain in the full client module, so numerical row certificates do not import those semantic
layers or generated data.

## References

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace MatrixMultiplication.LevelFourA5OccurrenceProgram

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

noncomputable section

private theorem nonempty_of_profileMass_pos
    {I : Type*} [Fintype I] (profile : I → ℕ)
    (hprofile : 0 < WordType.profileMass profile) : Nonempty I := by
  classical
  have hsum : (∑ i, profile i) ≠ 0 := by
    simpa only [WordType.profileMass] using Nat.ne_of_gt hprofile
  obtain ⟨i, _hi, _hprofilei⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨i⟩

/-- Positive mass of a literal occurrence profile supplies a genuine valid local slot. -/
theorem nonempty_levelFourValidSlot_of_parentMass_pos
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hmass : 0 < levelFourParentSamples top root region parent) :
    Nonempty (LevelFourValidSlot parent) := by
  apply nonempty_of_profileMass_pos
    (levelFourOccurrenceSourceProfile top root region parent)
  rw [profileMass_levelFourOccurrenceSourceProfile]
  exact hmass

/-- The categorical A5 program attached to one occurrence profile from arbitrary top rows. -/
noncomputable def cwLevelFourOccurrenceA5Program
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hmass : 0 < levelFourParentSamples top root region parent)
    (weights : CategoricalIntegerWeights parent sigma) : Program parent sigma where
  stateProfile := levelFourOccurrenceSourceProfile top root region parent
  stateProfileMass_pos := by
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hmass
  slotNonempty :=
    nonempty_levelFourValidSlot_of_parentMass_pos top root region parent hmass
  weights := weights

/-- The constructed A5 program exposes the supplied occurrence profile definitionally. -/
@[simp] theorem cwLevelFourOccurrenceA5Program_stateProfile
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hmass : 0 < levelFourParentSamples top root region parent)
    (weights : CategoricalIntegerWeights parent sigma) :
    (cwLevelFourOccurrenceA5Program top root region parent sigma hmass weights).stateProfile =
      levelFourOccurrenceSourceProfile top root region parent :=
  rfl

end

end MatrixMultiplication.LevelFourA5OccurrenceProgram
