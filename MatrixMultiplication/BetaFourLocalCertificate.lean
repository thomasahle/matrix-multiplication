/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourGather
import MatrixMultiplication.BetaFourLocalChecker

/-!
# Semantic adapter for parent-local beta-four certificates

`BetaFourLocalChecker.lean` checks one small serialized parent without loading the global
recurrence.  This module supplies the deliberately separate semantic bridge: it projects the
global top and beta-three caches to local slot records, states exact realization by that
projection, and proves that local gather/scatter evaluation recovers the established global
definitions.

Padding remains explicit.  An unrestricted scatter/gather theorem is false for arbitrary padded
rows because an out-of-support child symbol decodes to code zero.  The checker exposes
`BetaFourLocalData.IsSupportZero`; any later gather-to-scatter bridge must assume and discharge
that invariant rather than hide it.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

set_option maxRecDepth 1000000

namespace LocalGeometry

/-- The local and global coordinate readers are definitionally the same operation. -/
theorem shapeCoordinate_eq (shape : AlgebraicComplexity.LevelFourReconstruction.Shape)
    (coordinate : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate shape coordinate =
      MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.shapeCoordinate
        shape coordinate := by
  rfl

/-- The local and global ternary support enumerations are definitionally equal. -/
theorem ternarySupportCodes_eq (length total : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes length total =
      MatrixMultiplication.SimplifiedVolumeReconstruction.ternarySupportCodes
        length total := by
  rfl

/-- The local and global padded ternary-code lookups are definitionally equal. -/
theorem ternarySupportCodeAt_eq (length total symbol : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
        length total symbol =
      MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.ternarySupportCodeAt
        length total symbol := by
  rfl

/-- The local and global parent-shape lookups are definitionally equal. -/
theorem parentShapeAt_eq (parent : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent =
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.parentShapeAt parent := by
  rfl

/-- The local and global valid-slot lists are definitionally equal. -/
theorem validSlots_eq (parent : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.validSlots parent =
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.validSlots parent := by
  rfl

/-- The local and global ordered-pair lookups are definitionally equal. -/
theorem pairAt_eq (parent slot : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slot =
      MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.pairAt parent slot := by
  rfl

/-- The local and global child-word lengths are the same constant. -/
theorem childWordLength_eq :
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength =
      levelThreeWordLength := by
  rfl

/-- The local and global parent-word lengths are the same constant. -/
theorem parentWordLength_eq :
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength =
      parentWordLength := by
  rfl

/-- The local and global region counts are the same constant. -/
theorem regionCount_eq :
    MatrixMultiplication.BetaFourLocalGeometry.regionCount = regionCount := by
  rfl

/-- The local and global child support widths are the same constant. -/
theorem childSupportWidth_eq :
    MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth = childSupportWidth := by
  rfl

/-- The local and global parent support widths are the same constant. -/
theorem parentSupportWidth_eq :
    MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth = parentSupportWidth := by
  rfl

/-- The local and global total-eight shape indices are definitionally equal. -/
theorem shapeEightIndex_eq (shape : AlgebraicComplexity.LevelFourReconstruction.Shape) :
    MatrixMultiplication.BetaFourLocalGeometry.shapeEightIndex shape =
      MatrixMultiplication.SimplifiedVolumeReconstruction.shapeEightIndex shape := by
  rfl

/-- The local and global padded additions are definitionally equal. -/
theorem addNumeratorAt_eq (row : Array ℕ) (slot numerator : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.addNumeratorAt row slot numerator =
      addNumeratorAt row slot numerator := by
  rfl

/-- The local and global concatenated parent slots are definitionally equal. -/
theorem concatenatedParentSlotForPair_eq (parent coordinate : ℕ)
    (pair : AlgebraicComplexity.LevelFourReconstruction.Shape ×
      AlgebraicComplexity.LevelFourReconstruction.Shape)
    (leftSymbol rightSymbol : ℕ) :
    MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
        parent coordinate pair leftSymbol rightSymbol =
      concatenatedParentSlotForPair parent coordinate pair leftSymbol rightSymbol := by
  rfl

end LocalGeometry

/-- One coordinate row of the global beta-three cache. -/
def betaThreeCoordinateRowFrom (rows : BetaThreeRows) (row coordinate : ℕ) : Array ℕ :=
  (rows[row]?.getD #[])[coordinate]?.getD #[]

namespace BetaFourLocalSlotData

/-- The global cache projected to one local slot record. -/
def fromGlobal (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate slot : ℕ) : BetaFourLocalSlotData :=
  let pair := MatrixMultiplication.BetaFourLocalGeometry.pairAt parent slot
  let leftRow := MatrixMultiplication.BetaFourLocalGeometry.shapeEightIndex pair.1 *
    MatrixMultiplication.BetaFourLocalGeometry.regionCount + region
  let rightRow := MatrixMultiplication.BetaFourLocalGeometry.shapeEightIndex pair.2 *
    MatrixMultiplication.BetaFourLocalGeometry.regionCount + region
  { slot := slot
    splitNumerator := topSplitNumerator top root region parent slot
    leftNumerators := betaThreeCoordinateRowFrom betaThree leftRow coordinate
    rightNumerators := betaThreeCoordinateRowFrom betaThree rightRow coordinate }

end BetaFourLocalSlotData

namespace BetaFourLocalData

/-- Projection of the global caches onto exactly the rows consumed by one parent. -/
def fromGlobal (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) : BetaFourLocalData :=
  { slots := (MatrixMultiplication.BetaFourLocalGeometry.validSlots parent).map fun slot ↦
      BetaFourLocalSlotData.fromGlobal top betaThree root region parent coordinate slot }

/-- A parent-local certificate is faithful when it is exactly the finite global projection. -/
def Realizes (data : BetaFourLocalData) (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) : Prop :=
  data = fromGlobal top betaThree root region parent coordinate

/-- A faithful local certificate computes exactly the global pointwise gather numerator.

Proof sketch: replace the certificate by its global projection.  The local and global geometry
definitions then reduce to the same valid slots, ternary support codes, and two total beta-three
lookups. -/
theorem gatherNumerator_eq_global (data : BetaFourLocalData)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate symbol : ℕ)
    (hrealizes : data.Realizes top betaThree root region parent coordinate) :
    data.gatherNumerator parent coordinate symbol =
      betaFourParentNumeratorGather top betaThree root region parent coordinate symbol := by
  unfold Realizes at hrealizes
  subst data
  unfold gatherNumerator fromGlobal betaFourParentNumeratorGather
  rw [LocalGeometry.parentWordLength_eq, LocalGeometry.parentShapeAt_eq,
    LocalGeometry.shapeCoordinate_eq, LocalGeometry.ternarySupportCodes_eq,
    LocalGeometry.validSlots_eq]
  split
  · simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro slot _
    unfold BetaFourLocalSlotData.gatherNumerator BetaFourLocalSlotData.fromGlobal
      betaFourGatherSlotNumerator betaThreeCoordinateRowFrom
    simp only [Function.comp_apply]
    rw [LocalGeometry.pairAt_eq, LocalGeometry.shapeEightIndex_eq,
      LocalGeometry.regionCount_eq, LocalGeometry.childWordLength_eq,
      LocalGeometry.ternarySupportCodeAt_eq, LocalGeometry.ternarySupportCodes_eq,
      LocalGeometry.shapeCoordinate_eq]
    rfl
  · rfl

/-- A faithful local certificate reproduces the existing dense global scatter row.

Proof sketch: after replacing the certificate by `fromGlobal`, folding its mapped slot records is
the same as folding `addBetaFourSlot` over the global `validSlots`.  Every local geometry helper
has the same executable body as its global counterpart. -/
theorem scatter_eq_global (data : BetaFourLocalData)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ)
    (hrealizes : data.Realizes top betaThree root region parent coordinate) :
    data.scatter parent coordinate =
      betaFourParentRow top betaThree root region parent coordinate := by
  unfold Realizes at hrealizes
  subst data
  unfold scatter fromGlobal betaFourParentRow
  rw [LocalGeometry.validSlots_eq]
  simp only [List.foldl_map]
  have hstep :
      (fun row slot ↦
        (BetaFourLocalSlotData.fromGlobal top betaThree root region parent coordinate slot).addToRow
          parent coordinate row) =
        addBetaFourSlot top betaThree root region parent coordinate := by
    funext row slot
    unfold BetaFourLocalSlotData.fromGlobal BetaFourLocalSlotData.addToRow
      BetaFourLocalSlotData.addContribution addBetaFourSlot addBetaFourContribution
      betaThreeCoordinateRowFrom
      MatrixMultiplication.BetaFourLocalGeometry.pairAt
      MatrixMultiplication.BetaFourLocalGeometry.shapeEightIndex
      MatrixMultiplication.BetaFourLocalGeometry.regionCount
      MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth
      MatrixMultiplication.BetaFourLocalGeometry.addNumeratorAt
      MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
      MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotFromSupports
      MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.ternaryCodeWeight
      MatrixMultiplication.BetaFourLocalGeometry.ternaryDigit
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength
    rfl
  rw [hstep]
  rw [LocalGeometry.parentSupportWidth_eq]

/-- A faithful local certificate computes every requested global gather shard. -/
theorem gatherOn_eq_global (data : BetaFourLocalData)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent coordinate : ℕ) (symbols : List ℕ)
    (hrealizes : data.Realizes top betaThree root region parent coordinate) :
    data.gatherOn parent coordinate symbols =
      betaFourParentRowGatherOn top betaThree root region parent coordinate symbols := by
  unfold gatherOn betaFourParentRowGatherOn
  apply List.map_congr_left
  intro symbol _
  exact gatherNumerator_eq_global data top betaThree root region parent coordinate symbol hrealizes

end BetaFourLocalData

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
