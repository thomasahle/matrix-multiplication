/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradParentChildChunkPower
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetRepair

set_option autoImplicit false

/-!
# Recursive approximate repair with the target relabelings discharged

`CoppersmithWinogradRecursiveApproximateTargetRepair` deliberately accepts a uniform structure-
relabeling family as a client hypothesis.  The recursive target-relabeling package constructs that
family from a lift of doubled child-occurrence permutations, and
`CoppersmithWinogradParentChildChunkPower` proves the lift for every such permutation.

This module performs only the resulting mechanical specialization of the highest-level approximate
repair theorem.  The sparse-count implication and every cleanup, target, and depth hypothesis are
unchanged.  In particular, no target allocation, cardinality lower bound, degeneration, growth
estimate, or endpoint claim is proved here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-! ## The client with constructed relabelings -/

/-- Recursive approximate cleanup and repair after discharging the uniform structure-relabeling
premise with the exact recursive target action and the parent/child chunk-power lift.

Compared with
`cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies`, the abstract finite
relabeling type and its `UniformStructureRelabelings` value disappear.  The only added inputs are
the exact weight-support and coarse-total-support facts consumed by
`cwRecursiveExactTargetUniformStructureRelabelings`; the sparse count remains the same visible
implication in the conclusion. -/
theorem cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies_of_supportedTargets
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X)) coarseKept)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d) :
    ∃ (finalSupport : Finset (BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
      (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
          (CWRecursiveCoarseAddress depth n)),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        Restricts
          ((cwRecursiveApproximateAlphaMarginalSelectedTerm
              K q term hmultiplicity epsilon sigma alpha).withSupport
            (cwRecursiveFineSupportOverCoarseSupport
              (cwRecursiveApproximateAlphaMarginalSelectedTerm
                K q term hmultiplicity epsilon sigma alpha).support coarseKept)).realize
          (Tensor.indexedDirectSum
            (fun coarse : CWRecursiveCoarseAddress depth n ↦ (G.fiber coarse).realize)) ∧
        (Fintype.card O * HoleRepair.sevenBranchBudget d ≤
            (cwRecursiveApproximateSparseRetainedCoarse K q partAt term hmultiplicity
              epsilon sigma alpha targets coarseKept G reference base).card →
          Restricts
            ((cwRecursiveApproximateAlphaMarginalSelectedTerm
                K q term hmultiplicity epsilon sigma alpha).withSupport
              (cwRecursiveFineSupportOverCoarseSupport
                (cwRecursiveApproximateAlphaMarginalSelectedTerm
                  K q term hmultiplicity epsilon sigma alpha).support coarseKept)).realize
            (Tensor.indexedDirectSum (fun _output : O ↦
              ((compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
                (cwRecursiveExactTargetFiberParts
                  partAt sigma targets reference)).box target).realize))) := by
  classical
  let CellPerm := cwRecursiveReferenceCellPermSubgroup
    depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  exact cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept hcoarseX
      reference hreference
      (cwRecursiveExactTargetUniformStructureRelabelings
        K q partAt sigma targets hsupported hcoarseSupported reference
          (cwRecursiveChildOccurrenceRelabelingLift_holds
            K q depth n partAt sigma reference))
      hbase d target hdepth

end AlgebraicComplexity.Examples
