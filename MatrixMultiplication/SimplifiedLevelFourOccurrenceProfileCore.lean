/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.MatrixMultiplication.RecursiveSplitCertificateGeometry
import MatrixMultiplication.SimplifiedExponentLevelFourRowDefs
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Lightweight level-four occurrence profiles

This module owns the exact top-slot, parent-mass, and ordered occurrence-profile definitions used
by the recursive Coppersmith--Winograd analysis [coppersmith1990matrix].  It deliberately stops
before child-row reconstruction, validity, target realization, and generated certificate data.
The historical semantic owners import this module and retain their established qualified APIs.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveSplitTypes

open AlgebraicComplexity.LevelFourReconstruction

/-! ## Level four -/

/-- Literal ordered top-split numerator at a valid level-four parent-local slot. -/
def levelFourSlotNumerator
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) : ℕ :=
  MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.topSplitNumerator
    top root.val region.val parent.val slot.1.val

/-- Literal sample count of one level-four ordered split row.  This is the parent occurrence
subtotal, not in general the global top-law denominator. -/
def levelFourSamples
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount) : ℕ :=
  ∑ slot : LevelFourValidSlot parent, levelFourSlotNumerator top root region parent slot

end MatrixMultiplication.SimplifiedRecursiveSplitTypes

namespace MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Common exact sample size of a reconstructed depth-three child profile. -/
def levelFourChildSamples : ℕ := 2 ^ childBits

/-- Product scale contributed by the two independently concatenated child profiles. -/
def levelFourChildProductScale : ℕ := 2 ^ (2 * childBits)

/-- Exact sample count of one level-four parent row. -/
def levelFourParentSamples
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) : ℕ :=
  levelFourSamples top root region parent * levelFourChildProductScale

end MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- The exact ordered-state profile underlying one level-four occurrence package. -/
def levelFourOccurrenceSourceProfile
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) : ℕ :=
  levelFourSlotNumerator top root region parent slot *
    (levelFourChildSamples * levelFourChildSamples)

/-- The occurrence-state profile has the same mass as the recursively assembled parent term. -/
theorem profileMass_levelFourOccurrenceSourceProfile
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) =
      levelFourParentSamples top root region parent := by
  simp only [WordType.profileMass, levelFourOccurrenceSourceProfile,
    levelFourParentSamples, levelFourSamples, levelFourChildProductScale,
    levelFourChildSamples, childBits]
  rw [← Finset.sum_mul]
  norm_num

end AlgebraicComplexity.Examples
