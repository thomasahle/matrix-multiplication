/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetOutputCore
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetStage

/-!
# Fixed-type repaired-output CW stages

This module instantiates target repair with the exact fixed-type quotient `I / (2 * R)`.  Its
finite hypothesis says that at least half of the selected fixed type is simultaneously sparse;
the output-count theorem then supplies enough sparse repair plans.  No pre-type family size,
entropy estimate, or assembled tensor degeneration is accepted here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- A half-sparse fixed target type yields its exact candidate-independent number of intact
copies. -/
theorem nonempty_cwGroupedCleanup_fixedTypeTargetOutputWholeStage
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    (source : Tensor3 K S)
    (hsource : Restricts source
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize)))
    (width r : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hhalf :
      Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma coarseKept reference) ≤
        2 * (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
          targets coarseKept finalSupport hclosed hExact G hgroup reference (r + 2)).card)
    (htarget : ∀ c, (target c).card ≤ 3 ^ (width * r))
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K source
      (cwFixedTypeTargetRepairOutputCount width r
        (Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma coarseKept reference)))
      xSize ySize zSize) := by
  let fixedTypeCard := Fintype.card (cwFixedTargetCellTypeCoarseSupport
    depth n partAt sigma coarseKept reference)
  let copies := cwFixedTypeTargetRepairOutputCount width r fixedTypeCard
  let d := HoleRepair.logarithmicRepairDepth (r + 2) target
  have hbase : 1 < r + 2 := by omega
  have hsupply : copies * HoleRepair.sevenBranchBudget d ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference (r + 2)).card := by
    simpa only [copies, fixedTypeCard, d] using
      cwFixedTypeTargetRepairOutputCount_mul_sevenBranchBudget_le_sparse_of_half
        width r fixedTypeCard
          (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
            targets coarseKept finalSupport hclosed hExact G hgroup reference (r + 2)).card
          target hhalf htarget
  simpa only [copies, fixedTypeCard, Fintype.card_fin] using
    nonempty_cwGroupedCleanup_repairedTargetCellTypeWholeStage_of_sparse_count
      K q partAt term hmultiplicity sigma targets coarseKept finalSupport hclosed
        hExact G hgroup reference source hsource (O := Fin copies) hbase d target le_rfl
        (by simpa only [Fintype.card_fin] using hsupply) xSize ySize zSize hbox

end AlgebraicComplexity.Examples
