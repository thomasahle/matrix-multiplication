/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-!
# Zero-padding contract for serialized beta-three rows

The level-four recurrence stores each fixed-weight ternary row in a common padded array.  Semantic
proofs may read those rows through total array lookup, so they need an explicit guarantee that the
padding carries no mass.

This file isolates that guarantee from both its finite certificate checker and the larger
beta-four evaluator/semantics proof.  Generated clients prove the predicate through a compact
Boolean check; structural recurrence arguments consume only the predicate.
-/

namespace MatrixMultiplication.BetaFourSemanticAgreement

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Every serialized beta-three coordinate row is zero beyond its genuine fixed-weight support.

The shape and region are typed, so this predicate says nothing about unused out-of-range cache
indices.  It is precisely the invariant needed to rule out `List.idxOf`'s fallback position from
carrying mass. -/
def BetaThreeRowsHaveZeroPadding (betaThree : BetaThreeRows) : Prop :=
  ∀ (shape : Shape), shape ∈ shapes 8 →
    ∀ (region : Fin regionCount) (coordinate : Fin 3) (symbol : ℕ),
      (ternarySupportCodes levelThreeWordLength
          (shapeCoordinate shape coordinate.val)).length ≤ symbol →
        betaThreeNumeratorFrom betaThree
          (shapeEightIndex shape * regionCount + region.val) coordinate.val symbol = 0

end MatrixMultiplication.BetaFourSemanticAgreement
