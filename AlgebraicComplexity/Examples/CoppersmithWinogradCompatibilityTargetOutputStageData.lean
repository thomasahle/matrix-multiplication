/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanupData
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputStage

/-!
# Sealing compatibility-cleanup data into a fixed-type output stage

This module is the record adapter for the generic fixed-type stage constructor.  Keeping it
separate makes the load-bearing constructor independent of the cleanup-data convenience record.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- Record-based form of `nonempty_cwGroupedCleanup_fixedTypeTargetOutputWholeStage`.  The source
restriction comes from the cleanup constructor rather than a client hypothesis. -/
theorem CWCompatibilityCleanupData.nonempty_fixedTypeTargetOutputWholeStage
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    {source : Tensor3 K S}
    (cleanup : CWCompatibilityCleanupData K q partAt term hmultiplicity sigma targets source)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (width r : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hhalf :
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
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K source
      (cwFixedTypeTargetRepairOutputCount width r
        (Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference)))
      xSize ySize zSize) := by
  exact nonempty_cwGroupedCleanup_fixedTypeTargetOutputWholeStage
    K q partAt term hmultiplicity sigma targets cleanup.coarseKept cleanup.finalSupport
      cleanup.projection_closed cleanup.exact_profiles cleanup.grouping cleanup.group_eq
      reference source cleanup.source_restricts width r target hhalf htarget
      xSize ySize zSize hbox

end AlgebraicComplexity.Examples
