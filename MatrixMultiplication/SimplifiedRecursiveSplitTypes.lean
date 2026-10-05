/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveSplitCertificateGeometry
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceTermCounts
import MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore

/-!
# Exact recursive split types reconstructed from simplified-certificate rows

This module assigns a finite mathematical type to the ordered `alpha` rows used by the simplified
certificate.  A row's sample count is its literal numerator subtotal, rather than an asserted
global denominator.  Thus inactive rows and conditional rows are handled without a full-support
or normalization assumption; a generated client may prove a more convenient closed form for the
subtotal separately.

The construction retains the distinction required by Proposition 6.3 of *More Asymmetry Yields
Faster Matrix Multiplication*: these are types of the labelled **left child**.  The right-child
occurrences and the doubled self-complementary mass are derived later by
`ExactRecursiveSplitType.occurrenceCount`.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveSplitTypes

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor

/-- Evaluator coordinate carried by one physical tensor leg. -/
def coordinateOfLeg : Leg → Fin 3
  | .X => 0
  | .Y => 1
  | .Z => 2

@[simp] theorem coordinateOfLeg_X : coordinateOfLeg .X = 0 := rfl
@[simp] theorem coordinateOfLeg_Y : coordinateOfLeg .Y = 1 := rfl
@[simp] theorem coordinateOfLeg_Z : coordinateOfLeg .Z = 2 := rfl

/-- Shape lookup through the evaluator coordinate convention agrees with leg lookup. -/
theorem shapeCoordinate_coordinateOfLeg (shape : Shape) (c : Leg) :
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.shapeCoordinate
        shape (coordinateOfLeg c) = shape.leg c := by
  cases c <;> rfl

/-- Level-three parent constituent index in an arbitrary logical orientation. -/
def levelThreeParentIndex
    (node : Fin PositiveLevelThreeData.nodeCount) (sigma : Orientation) :
    LevelConstituentIndex 2 where
  count := (PositiveLevelThreeData.nodeShape node).orientedLeg sigma
  total := by
    rw [Tensor.sum_leg, Shape.orientedLeg_total,
      (PositiveLevelThreeData.nodeShape_geometry node).2]
    norm_num

/-- Level-four parent constituent index in an arbitrary logical orientation. -/
def levelFourParentIndex
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    LevelConstituentIndex 3 where
  count := (positiveLevelFourShape parent).orientedLeg sigma
  total := by
    rw [Tensor.sum_leg, Shape.orientedLeg_total,
      (positiveLevelFourShape_geometry parent).2]
    norm_num

/-! ## Level three -/

/-- Literal ordered-split numerator at a valid level-three certificate slot. -/
def levelThreeSlotNumerator
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount)
    (slot : LevelThreeValidSlot node) : ℕ :=
  MatrixMultiplication.SimplifiedVolumeReconstruction.dyadicNumeratorAt
    data.pos3Alpha (node.val * PositiveLevelThreeData.regionCount + region.val) slot.1.val

/-- Literal sample count of one level-three ordered split row. -/
def levelThreeSamples
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) : ℕ :=
  ∑ slot : LevelThreeValidSlot node, levelThreeSlotNumerator data node region slot

/-- Exact ordered left-child type reconstructed from one level-three row. -/
noncomputable def levelThreeSplitType
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) :
    ExactRecursiveSplitType
      ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4
      (levelThreeSamples data node region) :=
  levelThreeExactSplitType node sigma (levelThreeSamples data node region)
    (levelThreeSlotNumerator data node region) rfl

theorem levelThreeSplitType_total
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) :
    ∑ child, (levelThreeSplitType data node region sigma).count child =
      levelThreeSamples data node region :=
  (levelThreeSplitType data node region sigma).total

/-- Exact ordered left-child type reconstructed from one level-four parent row. -/
noncomputable def levelFourSplitType
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) :
    ExactRecursiveSplitType ((positiveLevelFourShape parent).orientedLeg sigma) 8
      (levelFourSamples top root region parent) :=
  levelFourExactSplitType parent sigma (levelFourSamples top root region parent)
    (levelFourSlotNumerator top root region parent) rfl

theorem levelFourSplitType_total
    (top : MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.TopBranchRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation) :
    ∑ child, (levelFourSplitType top root region parent sigma).count child =
      levelFourSamples top root region parent :=
  (levelFourSplitType top root region parent sigma).total

end MatrixMultiplication.SimplifiedRecursiveSplitTypes
