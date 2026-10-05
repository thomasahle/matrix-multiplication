/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityIndexRegion5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import Mathlib.Tactic.FinCases

/-!
# Bounded level-four active-slot coverage: region 5, chunk 48

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, this module checks exactly 2 positive-parent
indices.  Their parent-local key sets have diagnostic sizes [0, 0].  Each decision
enumerates one canonical five-slot shard and uses the regional index assembled from at-most-64-entry
data chunks.  The untrusted index has authority only where an exact array-read check reduces to
`true`; the reusable shard-coverage theorem assembles the resulting semantic parent facts.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Coverage.Region5.Chunk48

open AlgebraicComplexity.Tensor
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

/-- Positive level-four parent checked by local oracle 0. -/
def parent0 : Fin positiveLevelFourShapeCount := (96 : Fin 105)

/-- Exact indexed coverage check for canonical five-slot shard 0. -/
opaque checked0_0 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (0 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 1. -/
opaque checked0_1 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (1 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 2. -/
opaque checked0_2 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (2 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 3. -/
opaque checked0_3 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (3 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 4. -/
opaque checked0_4 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (4 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 5. -/
opaque checked0_5 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard (5 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- The six independently sealed checks cover every canonical five-slot shard. -/
theorem checked0 : ∀ shard : Fin 6,
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent0 xzy
        (levelFourCoverageSlotShard shard) Keys.Region5.array
        Index.Region5.index = true := by
  intro shard
  fin_cases shard
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked0_3
  · exact checked0_4
  · exact checked0_5

/-- Every active labelled child of `parent0` occurs in the submitted regional key array. -/
theorem covered0 :
    ∀ slot c, levelFourSlotNumerator Top.expectedRows 5 5 parent0 slot ≠ 0 →
      levelFourLeftChildRowKey 5 parent0 xzy slot c ∈ Keys.Region5.array ∧
        levelFourRightChildRowKey 5 parent0 xzy slot c ∈ Keys.Region5.array := by
  exact levelFourChildRowKeyIndexedCoverage_of_shards
    Top.expectedRows 5 5 parent0 xzy Keys.Region5.array
      Index.Region5.index checked0

/-- Indexed coverage plus the shared regional normalization proof validates `parent0`. -/
theorem childRowsValid0 (betaThree : BetaThreeRows)
    (hnormalized : levelFourChildRowKeysNormalizedCheck
      betaThree Keys.Region5.entries = true) :
    LevelFourChildRowsValid Top.expectedRows betaThree 5 5 parent0 xzy :=
  levelFourChildRowsValid_of_array_key_coverage
    Top.expectedRows betaThree 5 5 parent0 xzy Keys.Region5.entries
      Keys.Region5.array Keys.Region5.array_toList_eq_entries covered0
      hnormalized

/-- Positive level-four parent checked by local oracle 1. -/
def parent1 : Fin positiveLevelFourShapeCount := (97 : Fin 105)

/-- Exact indexed coverage check for canonical five-slot shard 0. -/
opaque checked1_0 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (0 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 1. -/
opaque checked1_1 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (1 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 2. -/
opaque checked1_2 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (2 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 3. -/
opaque checked1_3 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (3 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 4. -/
opaque checked1_4 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (4 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- Exact indexed coverage check for canonical five-slot shard 5. -/
opaque checked1_5 :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard (5 : Fin 6)) Keys.Region5.array
        Index.Region5.index = true := by
  decide +kernel

/-- The six independently sealed checks cover every canonical five-slot shard. -/
theorem checked1 : ∀ shard : Fin 6,
    levelFourSlotListChildRowKeyIndexedCoverageCheck
      Top.expectedRows 5 5 parent1 xzy
        (levelFourCoverageSlotShard shard) Keys.Region5.array
        Index.Region5.index = true := by
  intro shard
  fin_cases shard
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked1_3
  · exact checked1_4
  · exact checked1_5

/-- Every active labelled child of `parent1` occurs in the submitted regional key array. -/
theorem covered1 :
    ∀ slot c, levelFourSlotNumerator Top.expectedRows 5 5 parent1 slot ≠ 0 →
      levelFourLeftChildRowKey 5 parent1 xzy slot c ∈ Keys.Region5.array ∧
        levelFourRightChildRowKey 5 parent1 xzy slot c ∈ Keys.Region5.array := by
  exact levelFourChildRowKeyIndexedCoverage_of_shards
    Top.expectedRows 5 5 parent1 xzy Keys.Region5.array
      Index.Region5.index checked1

/-- Indexed coverage plus the shared regional normalization proof validates `parent1`. -/
theorem childRowsValid1 (betaThree : BetaThreeRows)
    (hnormalized : levelFourChildRowKeysNormalizedCheck
      betaThree Keys.Region5.entries = true) :
    LevelFourChildRowsValid Top.expectedRows betaThree 5 5 parent1 xzy :=
  levelFourChildRowsValid_of_array_key_coverage
    Top.expectedRows betaThree 5 5 parent1 xzy Keys.Region5.entries
      Keys.Region5.array Keys.Region5.array_toList_eq_entries covered1
      hnormalized

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Coverage.Region5.Chunk48
