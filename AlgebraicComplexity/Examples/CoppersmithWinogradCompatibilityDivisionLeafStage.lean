/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFiniteStage
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage

/-!
# Repaired CW compatibility families as exact division-tree leaves

The finite compatibility theorem constructs a whole-constituent stage on
`cwSelectedExactInterfaceTerm`.  A positive leaf of an `ExactInterfaceTermDivisionTree` expects a
stage on `PartitionedTensor.exactInterfaceTermPowerRestriction`.  For the CW chunk partition these
sources are definitionally identical.

This module records that source identification as a checked client.  All hashing, compatibility,
incidence, repair, target-size, and intact-box premises remain explicit.  The result can therefore
populate one positive recursive leaf without accepting a restriction of the assembled division
tree as a hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- One concrete positive CW hash/cleanup/repair pass supplies the corresponding exact
division-tree leaf stage.

The proof is intentionally only the generic `LeafStages.ofNonempty` adapter applied to the
constructed finite stage.  Successful elaboration checks that the repair stage's selected CW
source is exactly the target computed by the division leaf. -/
noncomputable def cwOrientedHashCleanup_fixedTypeTargetOutputDivisionLeafStage
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
    (width r : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hhalf :
      let cleanup := cwOrientedHashCompatibilityCleanupData
        encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
      Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference) ≤
        2 * (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
          targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
            cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference (r + 2)).card)
    (htarget : ∀ c, (target c).card ≤ 3 ^ (width * r))
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf (.positive n hmultiplicity)) :=
  ExactInterfaceTermDivisionTree.LeafStages.ofNonempty K (.positive n hmultiplicity)
    (nonempty_cwOrientedHashCleanup_fixedTypeTargetOutputWholeStage
      encoding K q partAt term hmultiplicity sigma targets pooled B hB seed reference
        width r target hhalf htarget xSize ySize zSize hbox)

end AlgebraicComplexity.Examples
