/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceConditionalEntropy
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceSource

set_option autoImplicit false

/-!
# Exact target profiles for level-four complementary occurrences

This file identifies the evaluator's scaled recursive target table with the proportional
cell/symbol profile of the labelled complementary-occurrence law.  The result is the algebraic
profile bridge used by the exact target-cardinality theorem; it does not assume compatibility
cleanup, sparse repair, a tensor restriction, generated certificate facts, or endpoint arithmetic.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Integral bounded-cell profile of the two labelled occurrences at one level-four node. -/
noncomputable def levelFourOccurrenceExactTargetCellProfile
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) :
    CWOrientedCoarseCell PUnit.{1} 2 → ℕ :=
  complementaryOccurrenceCellProfile
    (levelFourOccurrenceSourceProfile top root region parent)
    (levelFourComplementSlotPerm parent)
    (cwRecursiveOccurrenceStateCell 2
      (levelFourOccurrenceCoarseIndex parent sigma)
      (levelFourOccurrenceCoarseIndex_total parent sigma))

/-- Integral bounded-cell/split-word profile of one logical-leg occurrence law. -/
noncomputable def levelFourOccurrenceExactTargetJointProfile
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (logicalLeg : Leg) :
    CWOrientedCoarseCell PUnit.{1} 2 × SplitWord 2 → ℕ :=
  ComplementaryOccurrenceLaw.cellJointProfile
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid logicalLeg)
    (levelFourComplementSlotPerm parent)
    (cwRecursiveOccurrenceStateCell 2
      (levelFourOccurrenceCoarseIndex parent sigma)
      (levelFourOccurrenceCoarseIndex_total parent sigma))

/-- The sole nonexponential loss in the exact level-four target lower bound. -/
noncomputable def levelFourOccurrenceExactTargetLoss
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (logicalLeg : Leg) (k : ℕ) : ℝ :=
  WordType.structuralZeroMultinomialLoss
    (levelFourOccurrenceExactTargetJointProfile
      top betaThree root region parent sigma hvalid logicalLeg) k

/-- Repeating a labelled occurrence law repeats every pooled cell/symbol entry. -/
theorem cwProportionalOccurrenceLaw_cellJointProfile
    {State Symbol Cell : Type*}
    [Fintype State] [Fintype Symbol] [Fintype Cell] [DecidableEq Cell]
    {profile : State → ℕ}
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) (k : ℕ) :
    (cwProportionalOccurrenceLaw law k).cellJointProfile complement cellOf =
      WordType.proportionalCounts
        (law.cellJointProfile complement cellOf) k := by
  classical
  funext entry
  unfold ComplementaryOccurrenceLaw.cellJointProfile WordType.proportionalCounts
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases hcell :
      cellOf (occurrence.childState complement) = entry.1 <;>
    simp [hcell, cwProportionalOccurrenceLaw_count]

/-- The exact-target loss is positive. -/
theorem levelFourOccurrenceExactTargetLoss_pos
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (logicalLeg : Leg) (k : ℕ) :
    0 < levelFourOccurrenceExactTargetLoss
      top betaThree root region parent sigma hvalid logicalLeg k :=
  WordType.structuralZeroMultinomialLoss_pos _ _

/-- The exact-target lower-bound loss is subexponential. -/
theorem levelFourOccurrenceExactTargetLoss_subexponential
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (logicalLeg : Leg) :
    Growth.Subexponential
      (levelFourOccurrenceExactTargetLoss
        top betaThree root region parent sigma hvalid logicalLeg) :=
  WordType.structuralZeroMultinomialLoss_subexponential _

/-- The scaled recursive target table is exactly the proportional bounded-cell occurrence
profile. -/
theorem levelFourOccurrenceScaledExactProfile_eq_proportionalJointProfile
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (logicalLeg : Leg) (k : ℕ)
    (cell : CWOrientedCoarseCell PUnit.{1} 2) (word : SplitWord 2) :
    let scaledData := cwProportionalRecursiveOccurrenceTargetData
      (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
        hvalid hboundary) k
    scaledData.toCompatibilityTargets.exactProfile logicalLeg
        (cwOrientedCoarseCellToIndex cell) word =
      WordType.proportionalCounts
        (levelFourOccurrenceExactTargetJointProfile
          top betaThree root region parent sigma hvalid logicalLeg) k (cell, word) := by
  dsimp only
  let baseData := levelFourOccurrenceTargetData
    top betaThree order sigma horder root region parent hvalid hboundary
  let scaledData := cwProportionalRecursiveOccurrenceTargetData baseData k
  let coarseOf := levelFourOccurrenceCoarseIndex parent sigma
  let complement := levelFourComplementSlotPerm parent
  let cellOf := cwRecursiveOccurrenceStateCell 2 coarseOf
    (levelFourOccurrenceCoarseIndex_total parent sigma)
  let law := levelFourOccurrenceLaw
    top betaThree root region parent sigma hvalid logicalLeg
  have hcoarse : ∀ occurrence,
      coarseOf occurrence =
        coarseOf (occurrence.childState complement, .left) := by
    intro occurrence
    calc
      coarseOf occurrence =
          levelFourSlotCoarseIndex parent sigma
            (occurrence.childState complement) :=
        levelFourOccurrenceCoarseIndex_eq_childState parent sigma occurrence
      _ = coarseOf (occurrence.childState complement, .left) := rfl
  have hbase :
      recursiveOccurrenceExactProfile coarseOf law
          (cwOrientedCoarseCellToIndex cell) word =
        law.cellJointProfile complement cellOf (cell, word) := by
    exact recursiveOccurrenceExactProfile_eq_cellJointProfile_stateCell
      coarseOf law complement
        (levelFourOccurrenceCoarseIndex_total parent sigma) hcoarse cell word
  have hexact :
      scaledData.toCompatibilityTargets.exactProfile logicalLeg =
        recursiveOccurrenceExactProfile coarseOf (scaledData.law logicalLeg) := by
    cases logicalLeg <;> rfl
  rw [congrFun (congrFun hexact (cwOrientedCoarseCellToIndex cell)) word,
    cwProportionalRecursiveOccurrenceTargetData_law]
  change
    recursiveOccurrenceExactProfile coarseOf
        (cwProportionalOccurrenceLaw law k)
        (cwOrientedCoarseCellToIndex cell) word =
      law.cellJointProfile complement cellOf (cell, word) * k
  simpa only [recursiveOccurrenceExactProfile,
    recursiveOccurrencePooledProfile_proportionalCounts] using
      congrArg (· * k) hbase

end AlgebraicComplexity.Examples
