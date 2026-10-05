/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceRegionalFamilyStage
import MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilies

/-!
# Checked stages for diagonal level-four regional families

The semantic diagonal family fixes the exact six-leaf tree.  A finite certificate constructs one
local exact-division leaf stage for each region.  This module aligns those six dependent objects
with the semantic family and compiles them to the leaf-stage tree consumed by the tensor fold.

Only the locally proved stages are inputs.  There is no premise asserting a restriction of their
product or of the assembled regional term.
-/

namespace MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilies
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

universe u v w z

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Package six locally checked diagonal leaves in the exact semantic-family shape. -/
noncomputable def levelFourDiagonalSemanticRegionalStages
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord 3)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hchild : ∀ region,
      LevelFourChildRowsValid top betaThree region region parent sigma)
    (stages : ∀ region,
      ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
        (.leaf (levelFourDiagonalSemanticRegionalLeaf
          top betaThree region parent sigma (hchild region)).multiplicityCase)) :
    ExactInterfaceRegionalFamily.Stages.{u, v, w, z} K P encode
      (levelFourDiagonalSemanticRegionalFamily top betaThree parent sigma hchild) :=
  ExactInterfaceRegionalFamily.Stages.six K
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 0 parent sigma (hchild 0))
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 1 parent sigma (hchild 1))
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 2 parent sigma (hchild 2))
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 3 parent sigma (hchild 3))
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 4 parent sigma (hchild 4))
    (levelFourDiagonalSemanticRegionalLeaf top betaThree 5 parent sigma (hchild 5))
    (stages 0) (stages 1) (stages 2) (stages 3) (stages 4) (stages 5)

/-- Compile the six diagonal local stages to the exact division-tree stage object. -/
noncomputable def levelFourDiagonalSemanticDivisionTreeLeafStages
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord 3)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (hchild : ∀ region,
      LevelFourChildRowsValid top betaThree region region parent sigma)
    (stages : ∀ region,
      ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
        (.leaf (levelFourDiagonalSemanticRegionalLeaf
          top betaThree region parent sigma (hchild region)).multiplicityCase)) :
    ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (levelFourDiagonalSemanticRegionalFamily top betaThree parent sigma hchild).toDivisionTree :=
  (levelFourDiagonalSemanticRegionalStages K P encode
    top betaThree parent sigma hchild stages).toDivisionTreeLeafStages

end MatrixMultiplication.SimplifiedRecursiveDiagonalRegionalFamilyStage
