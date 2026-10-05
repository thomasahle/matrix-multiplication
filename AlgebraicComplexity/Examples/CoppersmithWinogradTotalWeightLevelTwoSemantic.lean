/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLevelTwoSquare

/-!
# Semantic equivalence of the depth-one total-weight quotient and the CW square

`CoppersmithWinogradTotalWeightLevelTwoSquare` proves that the two constructions use exactly the
same coarsening map.  This file exposes the corresponding tensor semantics: each constituent and
the whole realized partition are legwise isomorphic.  Both restriction directions are recorded
as convenient clients because later extraction theorems are phrased using `Restricts`.

These are identity transports after rewriting the coarsening map.  No extraction rate, support
count, or degeneration hypothesis is introduced.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-- Every depth-one total-weight quotient constituent is the corresponding CW-square constituent,
up to the identity leg isomorphisms exposed after rewriting the coarsening map. -/
theorem cwTotalWeightLevelTwo_constituent_isomorphic_cwSquare
    (address : CWSquareAddress) :
    Isomorphic
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).constituent address)
      ((cwSquarePartitionedTensor K q).constituent address) := by
  rw [cwTotalWeightChunkCoarsening_one_eq_cwSquareDegreeMap]
  exact Isomorphic.refl _

/-- Restriction-facing form from a total-weight constituent to the square constituent. -/
theorem cwTotalWeightLevelTwo_constituent_restricts_cwSquare
    (address : CWSquareAddress) :
    Restricts
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).constituent address)
      ((cwSquarePartitionedTensor K q).constituent address) :=
  (cwTotalWeightLevelTwo_constituent_isomorphic_cwSquare K q address).restricts

/-- Reverse restriction from a square constituent to its total-weight presentation. -/
theorem cwSquare_constituent_restricts_cwTotalWeightLevelTwo
    (address : CWSquareAddress) :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent address)
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).constituent address) :=
  (cwTotalWeightLevelTwo_constituent_isomorphic_cwSquare K q address).symm.restricts

/-- The whole realized depth-one total-weight quotient is the realized coarsened CW square. -/
theorem cwTotalWeightLevelTwo_realize_isomorphic_cwSquare :
    Isomorphic
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).realize)
      ((cwSquarePartitionedTensor K q).realize) := by
  rw [cwTotalWeightChunkCoarsening_one_eq_cwSquareDegreeMap]
  exact Isomorphic.refl _

/-- Restriction-facing form from the realized total-weight quotient to the realized CW square. -/
theorem cwTotalWeightLevelTwo_realize_restricts_cwSquare :
    Restricts
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).realize)
      ((cwSquarePartitionedTensor K q).realize) :=
  (cwTotalWeightLevelTwo_realize_isomorphic_cwSquare K q).restricts

/-- Reverse restriction from the realized CW square to its total-weight presentation. -/
theorem cwSquare_realize_restricts_cwTotalWeightLevelTwo :
    Restricts
      ((cwSquarePartitionedTensor K q).realize)
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).realize) :=
  (cwTotalWeightLevelTwo_realize_isomorphic_cwSquare K q).symm.restricts

end AlgebraicComplexity.Examples
