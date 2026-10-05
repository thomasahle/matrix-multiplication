/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanupData
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetRepair
import AlgebraicComplexity.MatrixMultiplication.OuterConstituentStageCore

set_option autoImplicit false

/-!
# Repaired CW boxes as outer-constituent stages

Compatibility cleanup and sparse hole repair first produce intact copies of a tensor box.  In a
recursive proof that box should remain an unevaluated constituent: identifying it immediately
with a matrix-multiplication tensor would conflate the outer repair with the later recursive leaf
extraction.

This module records the narrow adapter to `OuterConstituentStage`.  It packages the indexed direct
sum already proved by the target-repair theorem and deliberately assumes no restriction or
degeneration of one intact box.  A downstream client can therefore refine every retained box by a
standard-form child-product extraction, and only the final leaf needs to become matrix
multiplication through `NestedLaserVolumeComposition`.

Nothing here changes the repair count.  The output index is the caller's finite type `O`, so the
stage has exactly `Fintype.card O` copies.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- Sparse repair of a checked CW compatibility cleanup yields an outer stage of intact boxes.

The result retains each repaired box as a whole, not-yet-evaluated constituent.  In particular,
there is no `hbox` premise asserting that the box is matrix multiplication.  The only quantitative
inputs are the same repair-depth and sparse-address supply inequalities used by the underlying
finite repair theorem.

Proof sketch: invoke `exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count` using the
semantic fields stored by `cleanup`, project its final indexed-direct-sum restriction by classical
choice (the repair plans themselves do not enter the result), and package that restriction with
`OuterConstituentStage.ofIndexedConstituents`. -/
noncomputable def CWCompatibilityCleanupData.repairedTargetCellTypeOuterStage_of_sparse_count
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    {source : Tensor3 K S}
    (cleanup : CWCompatibilityCleanupData K q partAt term hmultiplicity sigma targets source)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
          cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference base).card) :
    OuterConstituentStage K source (Fintype.card O) := by
  have hrepairData := exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count
      K q partAt term hmultiplicity sigma targets cleanup.coarseKept cleanup.finalSupport
        cleanup.projection_closed cleanup.exact_profiles cleanup.grouping cleanup.group_eq
        reference source cleanup.source_restricts hbase d target hdepth hcount
  exact OuterConstituentStage.ofIndexedConstituents K rfl
    (Classical.choose_spec (Classical.choose_spec hrepairData)).2

end AlgebraicComplexity.Examples
