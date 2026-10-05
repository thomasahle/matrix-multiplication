/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceRegionalFamily
import MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

/-!
# Diagonal level-four semantic regional families

The compact level-four certificate uses six labelled regions with the diagonal convention
`root = incomingRegion`.  This module assembles those six reconstructed semantic parent terms into
one exact regional family.  It uses only child-row validity and therefore does not pass through the
evaluator-row representation.

The construction is orientation-parametric.  In particular, a client may use the same orientation
for all six regions; no distinctness premise is present.  Compatibility boundaries and finite
hashing/extraction stages belong to the later staged client and are deliberately absent here.
-/

namespace MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilies

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Retype one recursively constructed diagonal parent term as a regional leaf at its common
constituent index. -/
noncomputable def levelFourDiagonalSemanticRegionalLeaf
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree region region parent sigma) :
    ExactInterfaceRegionalLeaf (levelFourParentIndex parent sigma) :=
  let term := levelFourRecursiveParentTerm
    top betaThree region region parent sigma hchild
  { multiplicity := term.multiplicity
    split := term.split
    multiplicityCase := ExactInterfaceTermMultiplicityCase.ofTerm term }

/-- Forgetting the regional wrapper returns the recursively constructed semantic term. -/
@[simp] theorem levelFourDiagonalSemanticRegionalLeaf_toTerm
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree region region parent sigma) :
    (levelFourDiagonalSemanticRegionalLeaf
      top betaThree region parent sigma hchild).toTerm =
      levelFourRecursiveParentTerm top betaThree region region parent sigma hchild :=
  rfl

/-- The six diagonal semantic regions, in certificate region order `0, ..., 5`. -/
noncomputable def levelFourDiagonalSemanticRegionalFamily
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hchild : ∀ region,
      LevelFourChildRowsValid top betaThree region region parent sigma) :
    ExactInterfaceRegionalFamily (levelFourParentIndex parent sigma) :=
  ExactInterfaceRegionalFamily.six
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 0 parent sigma (hchild 0)))
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 1 parent sigma (hchild 1)))
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 2 parent sigma (hchild 2)))
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 3 parent sigma (hchild 3)))
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 4 parent sigma (hchild 4)))
    (.leaf (levelFourDiagonalSemanticRegionalLeaf top betaThree 5 parent sigma (hchild 5)))

/-- Exact division tree computed from the six diagonal semantic regions. -/
noncomputable def levelFourDiagonalSemanticDivisionTree
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hchild : ∀ region,
      LevelFourChildRowsValid top betaThree region region parent sigma) :
    ExactInterfaceTermDivisionTree
      (levelFourDiagonalSemanticRegionalFamily top betaThree parent sigma hchild).toTerm :=
  (levelFourDiagonalSemanticRegionalFamily top betaThree parent sigma hchild).toDivisionTree

/-- The family multiplicity is the literal sum of its six diagonal parent subtotals. -/
@[simp] theorem levelFourDiagonalSemanticRegionalFamily_multiplicity
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hchild : ∀ region,
      LevelFourChildRowsValid top betaThree region region parent sigma) :
    (levelFourDiagonalSemanticRegionalFamily top betaThree parent sigma hchild).multiplicity =
      (levelFourParentSamples top 0 0 parent +
          (levelFourParentSamples top 1 1 parent + levelFourParentSamples top 2 2 parent)) +
        (levelFourParentSamples top 3 3 parent +
          (levelFourParentSamples top 4 4 parent + levelFourParentSamples top 5 5 parent)) := by
  simp only [levelFourDiagonalSemanticRegionalFamily,
    ExactInterfaceRegionalFamily.six_multiplicity,
    ExactInterfaceRegionalFamily.multiplicity,
    levelFourDiagonalSemanticRegionalLeaf,
    levelFourRecursiveParentTerm_multiplicity]

end MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilies
