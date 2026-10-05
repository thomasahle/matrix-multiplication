/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceRegionalFamily
import MatrixMultiplication.SimplifiedRecursiveChildProfiles
import MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles

/-!
# Reconstructed recursive terms as six-region division families

The total-weight certificate assigns one logical orientation to each of six labelled regions.
For a fixed recursive parent, the orientation is held fixed while the regional multiplicities and
complete-split profiles vary.  Hence the six checked regional terms have definitionally the same
constituent index and may be assembled by `ExactInterfaceRegionalFamily.six`.

This module is the generated-data-free bridge from the concrete level-three and level-four
reconstruction APIs to the generic exact regional-division tree.  It assumes only the local row
normalization and evaluator-agreement propositions already required to construct each checked
term.  In particular it assumes no tensor restriction, extraction stage, cardinality estimate,
orientation distinctness, or assembled-product statement.
-/

namespace MatrixMultiplication.SimplifiedRecursiveRegionalFamilies

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedRecursiveChildProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveParentTerms
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Regard an exact term as a one-region leaf indexed by its own constituent shape. -/
private noncomputable def regionalLeafOfTerm {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) :
    ExactInterfaceRegionalLeaf term.index where
  multiplicity := term.multiplicity
  split := term.split
  multiplicityCase := ExactInterfaceTermMultiplicityCase.ofTerm term

/-- The level-three certificate's named region count is definitionally six, exposed through an
explicit bounded-index map so clients do not rely on numeral instance reduction through that
name. -/
private def levelThreeRegion (region : Fin 6) : Fin PositiveLevelThreeData.regionCount :=
  ⟨region.val, by simpa only [PositiveLevelThreeData.regionCount] using region.isLt⟩

/-! ## Level three -/

/-- One quotient-parametric checked level-three regional term, retyped at the common parent
constituent index. -/
noncomputable def levelThreeCheckedRegionalLeafFor
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hchild : LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma) :
    ExactInterfaceRegionalLeaf (levelThreeParentIndex node sigma) := by
  exact regionalLeafOfTerm
    (levelThreeCheckedParentTermFor supportSlot data node region sigma hchild hrows)

/-- The six checked level-three regions at one fixed node and orientation.  Repetition of the
orientation is built into the common `sigma` argument and requires no distinctness premise. -/
noncomputable def levelThreeCheckedRegionalFamilyFor
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (sigma : Orientation)
    (hchild : ∀ region, LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : ∀ region, LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma) :
    ExactInterfaceRegionalFamily (levelThreeParentIndex node sigma) :=
  ExactInterfaceRegionalFamily.six
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 0) sigma
      (hchild (levelThreeRegion 0)) (hrows (levelThreeRegion 0))))
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 1) sigma
      (hchild (levelThreeRegion 1)) (hrows (levelThreeRegion 1))))
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 2) sigma
      (hchild (levelThreeRegion 2)) (hrows (levelThreeRegion 2))))
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 3) sigma
      (hchild (levelThreeRegion 3)) (hrows (levelThreeRegion 3))))
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 4) sigma
      (hchild (levelThreeRegion 4)) (hrows (levelThreeRegion 4))))
    (.leaf (levelThreeCheckedRegionalLeafFor supportSlot data node (levelThreeRegion 5) sigma
      (hchild (levelThreeRegion 5)) (hrows (levelThreeRegion 5))))

/-- Exact regional-division tree computed from all six level-three certificate regions. -/
noncomputable def levelThreeCheckedDivisionTreeFor
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (sigma : Orientation)
    (hchild : ∀ region, LevelThreeChildRowsValidFor supportSlot data node region sigma)
    (hrows : ∀ region, LevelThreeEvaluatorRowsAgreeFor supportSlot data node region sigma) :
    ExactInterfaceTermDivisionTree
      (levelThreeCheckedRegionalFamilyFor supportSlot data node sigma hchild hrows).toTerm :=
  (levelThreeCheckedRegionalFamilyFor supportSlot data node sigma hchild hrows).toDivisionTree

/-! ## Level four -/

/-- One checked level-four regional parent, retyped at the common selected-parent index. -/
noncomputable def levelFourCheckedRegionalLeaf
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (betaThree : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : LevelFourEvaluatorRowsAgree top betaThree root region parent sigma) :
    ExactInterfaceRegionalLeaf (levelFourParentIndex parent sigma) := by
  exact regionalLeafOfTerm
    (levelFourCheckedParentTerm top betaThree root region parent sigma hchild hrows)

/-- The six checked level-four regions belonging to one fixed root, selected parent, and logical
orientation. -/
noncomputable def levelFourCheckedRegionalFamily
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (betaThree : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaThreeRows)
    (root : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : ∀ region, LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : ∀ region, LevelFourEvaluatorRowsAgree top betaThree root region parent sigma) :
    ExactInterfaceRegionalFamily (levelFourParentIndex parent sigma) :=
  ExactInterfaceRegionalFamily.six
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 0 parent sigma
      (hchild 0) (hrows 0)))
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 1 parent sigma
      (hchild 1) (hrows 1)))
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 2 parent sigma
      (hchild 2) (hrows 2)))
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 3 parent sigma
      (hchild 3) (hrows 3)))
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 4 parent sigma
      (hchild 4) (hrows 4)))
    (.leaf (levelFourCheckedRegionalLeaf top betaThree root 5 parent sigma
      (hchild 5) (hrows 5)))

/-- Exact regional-division tree computed from all six level-four certificate regions. -/
noncomputable def levelFourCheckedDivisionTree
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (betaThree : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaThreeRows)
    (root : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hchild : ∀ region, LevelFourChildRowsValid top betaThree root region parent sigma)
    (hrows : ∀ region, LevelFourEvaluatorRowsAgree top betaThree root region parent sigma) :
    ExactInterfaceTermDivisionTree
      (levelFourCheckedRegionalFamily top betaThree root parent sigma hchild hrows).toTerm :=
  (levelFourCheckedRegionalFamily top betaThree root parent sigma hchild hrows).toDivisionTree

end MatrixMultiplication.SimplifiedRecursiveRegionalFamilies
