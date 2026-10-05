/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityProportionalStage
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage

/-!
# Proportional compatibility stages as exact division leaves

`CoppersmithWinogradCompatibilityProportionalStage` constructs the finite stage produced by one
oriented hash, compatibility cleanup, and sparse repair at an exact proportional type.  Exact
recursive assembly consumes the same object as the positive leaf of an
`ExactInterfaceTermDivisionTree`.

This module checks that source identification directly.  It changes no finite hypothesis: the
aggregate incidences, half-density budget, target-size bound, and intact-box restriction remain
visible.  In particular, it neither assumes a restriction of an assembled regional product nor
introduces an asymptotic counting claim.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- A proportional oriented compatibility cleanup supplies the corresponding positive leaf of an
exact interface-division tree.

The output copy count is the literal fixed-type repair count.  The definition only applies the
generic `LeafStages.ofNonempty` adapter to the already-constructed finite stage, so elaboration
checks that the selected CW constituent is exactly the leaf restriction computed by the division
tree. -/
noncomputable def
    cwOrientedHashCleanup_proportionalFixedTypeTargetOutputDivisionLeafStage_of_incidence
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    {depth : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (mass r : ℕ) (hsamples : n + 1 = mass * r)
    (budget : Leg → ℕ)
    (haggregate :
      let cleanup := cwOrientedHashCompatibilityCleanupData
        encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
      ∀ c,
        (r + 2) * 4 *
            ∑ coarse : cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma cleanup.coarseKept reference,
              ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
                targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
                  cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference).holes
                    coarse c).card ≤
          budget c *
            (cwExactTargetCoarseFiberParts
              partAt sigma targets reference c).card)
    (hhalf :
      let cleanup := cwOrientedHashCompatibilityCleanupData
        encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
      2 * (budget .X + budget .Y + budget .Z) ≤
        Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference))
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf (.positive n hmultiplicity)) :=
  ExactInterfaceTermDivisionTree.LeafStages.ofNonempty K (.positive n hmultiplicity)
    (nonempty_cwOrientedHashCleanup_proportionalFixedTypeTargetOutputWholeStage_of_incidence
      encoding K q partAt term hmultiplicity sigma targets pooled B hB seed reference
        mass r hsamples budget haggregate hhalf target xSize ySize zSize hbox)

end AlgebraicComplexity.Examples
