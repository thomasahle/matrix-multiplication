/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawModel

set_option autoImplicit false

/-!
# Injectivity of the level-four occurrence-state cell

Within one parent and orientation, the left-child shape determines the valid ordered slot.  The
bounded coarse state-cell used by the hashing model records that shape, hence is injective on the
valid level-four state space.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Within a fixed parent and orientation, the intrinsic left-child shape determines the valid
ordered slot. -/
theorem levelFourChildShape_injective
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    Function.Injective (levelFourChildShape parent sigma) := by
  intro left right hshape
  have hleg :
      (levelFourPairAtSlot parent left.1 left.2).1.leg =
        (levelFourPairAtSlot parent right.1 right.2).1.leg := by
    funext c
    have h := congrArg (fun child ↦ child.get (sigma.symm c)) hshape
    simpa only [levelFourChildShape_get, Shape.orientedLeg_apply,
      Equiv.apply_symm_apply] using h
  have hleft :
      (levelFourPairAtSlot parent left.1 left.2).1 =
        (levelFourPairAtSlot parent right.1 right.2).1 := by
    generalize hleftShape : (levelFourPairAtSlot parent left.1 left.2).1 = leftShape at hleg ⊢
    generalize hrightShape :
      (levelFourPairAtSlot parent right.1 right.2).1 = rightShape at hleg ⊢
    rcases leftShape with ⟨lx, ly, lz⟩
    rcases rightShape with ⟨rx, ry, rz⟩
    have hx : lx = rx := by
      simpa [Shape.leg] using congrFun hleg .X
    have hy : ly = ry := by
      simpa [Shape.leg] using congrFun hleg .Y
    have hz : lz = rz := by
      simpa [Shape.leg] using congrFun hleg .Z
    subst rx
    subst ry
    subst rz
    rfl
  apply levelFourPairAtSlot_injective parent
  apply Prod.ext
  · exact hleft
  · rw [← levelFourRightChild_eq_complement parent left,
      ← levelFourRightChild_eq_complement parent right, hleft]

/-- The bounded state-cell name used by the finite hashing model is injective on valid level-four
slots. -/
theorem levelFourOccurrenceStateCell_injective
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    Function.Injective
      (cwRecursiveOccurrenceStateCell 2
        (levelFourOccurrenceCoarseIndex parent sigma)
        (levelFourOccurrenceCoarseIndex_total parent sigma)) := by
  intro left right hcell
  apply levelFourChildShape_injective parent sigma
  apply RecursiveChildShape.ext
  intro c
  have h := congrArg
    (fun cell : CWOrientedCoarseCell PUnit 2 ↦ ((cell.2 c : Fin (coarseTotal 2 + 1)) : ℕ))
    hcell
  simpa only [cwRecursiveOccurrenceStateCell, cwRecursiveOccurrenceFiniteCell,
    levelFourOccurrenceCoarseIndex, levelFourOccurrenceChildShape_left,
    recursiveChildShapeCoarseIndex_get] using h

end AlgebraicComplexity.Examples
