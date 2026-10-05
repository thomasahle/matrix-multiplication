/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanupDataHash
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputStageData

/-!
# End-to-end finite CW compatibility stages

This module composes the concrete oriented affine hash and compatibility cleanup with the exact
fixed-type repair quotient.  The assembled source restriction is constructed by
`cwOrientedHashCompatibilityCleanupData`; it is never accepted as a premise.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- One concrete oriented hash/cleanup/repair pass produces the fixed-type number of intact
rectangular matrix-multiplication copies.  The theorem is orientation-parametric, so the same
orientation may be reused in any number of regions. -/
theorem nonempty_cwOrientedHashCleanup_fixedTypeTargetOutputWholeStage
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
    let cleanup := cwOrientedHashCompatibilityCleanupData
      encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (cwFixedTypeTargetRepairOutputCount width r
        (Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference)))
      xSize ySize zSize) := by
  let cleanup := cwOrientedHashCompatibilityCleanupData
    encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
  exact cleanup.nonempty_fixedTypeTargetOutputWholeStage
    K q partAt term hmultiplicity sigma targets reference width r target
      hhalf htarget xSize ySize zSize hbox

end AlgebraicComplexity.Examples
