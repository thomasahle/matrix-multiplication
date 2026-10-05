/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetRepair
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeCopies

/-!
# Whole-constituent stages from repaired CW target cells

The total-weight quotient cleanup and target-specific repair theorems produce arbitrarily many
intact copies of one exact target box.  This module is the final, purely semantic adapter from that
finite repair statement to `WholeConstituentLaserVolumeStage`.

All type counting, hashing, sparse-address, and repair-depth estimates remain explicit hypotheses
of the upstream repair theorem.  The only new premise is the recursive/leaf identification of one
intact target box with the desired rectangular matrix-multiplication tensor.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The intact exact box selected inside the normalized reference coarse constituent. -/
noncomputable def cwExactTargetBoxTensor
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c)) :=
  ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
    (cwExactTargetCoarseFiberParts partAt sigma targets reference)).box target).realize

/-- A repaired family of exact target cells is a whole-constituent laser-volume stage as soon as
one intact target box has been identified with the desired matrix-multiplication tensor.

This is the shortest finite endpoint of the total-weight quotient route: all compatibility
zeroing and hole repair are discharged by
`exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count`; only its displayed quantitative
count/depth hypotheses and the recursive intact-box identification remain. -/
theorem nonempty_cwGroupedCleanup_repairedTargetCellTypeWholeStage_of_sparse_count
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
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base).card)
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K source
      (Fintype.card O) xSize ySize zSize) := by
  obtain ⟨_plans, _pick, _hholes, hrepair⟩ :=
    exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count
      K q partAt term hmultiplicity sigma targets coarseKept finalSupport hclosed
        hExact G hgroup reference source hsource hbase d target hdepth hcount
  exact ⟨WholeConstituentLaserVolumeStage.ofIndexedCopies
    K rfl (by simpa only [cwExactTargetBoxTensor] using hrepair) hbox⟩

end AlgebraicComplexity.Examples
