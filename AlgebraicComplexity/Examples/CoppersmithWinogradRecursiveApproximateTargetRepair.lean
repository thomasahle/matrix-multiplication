/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetModel

/-!
# Instantiating the generic repair API for recursive approximate cleanup

This module is **mechanical packaging only**.  It proves no count and constructs no relabeling.

Two adapters are supplied.  First, the all-quotient indexed direct sum produced by recursive
approximate cleanup is restricted to the retained same-tagged-multiplicity subtype, using the
generic `Tensor.Restricts.indexedDirectSum_subfamily`.  Second, the modeled damaged-box family of
`CoppersmithWinogradRecursiveApproximateTargetModel` is fed to the generic
`HoleRepair.ModeledFiberFamily.exists_repairPlans_of_mul_budget_le_sparse`, and the two are
composed.

## The two honest boundaries, stated once

* **The relabeling family is a named hypothesis here, and it is now constructible.**  Every
  repair-facing statement below takes
  `relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel) P` with
  `P := compactBox ((cwChunkPartitionedTensor K q (depth+1)).positivePower n)
  (cwRecursiveExactTargetFiberParts partAt sigma targets reference)`,
  for a finite nonempty `Relabel`.  Keeping it a parameter is deliberate, so that this module stays
  independent of how the family is built; nothing here weakens, approximates, or silently
  discharges it.  A committed value of exactly that type now exists:
  `cwRecursiveExactTargetUniformStructureRelabelings`, at `Relabel` the opposite doubled
  tagged-cell stabilizer, whose single geometric hypothesis is in turn discharged by
  `cwRecursiveChildOccurrenceRelabelingLift_holds`.  Those two modules are named in prose only;
  this file deliberately does not import them.  The older
  `cwExactTargetUniformStructureRelabelings` remains tied to the exact-selector coarse alphabet
  and is still not convertible to this type.
* **The sparse count is a hypothesis.**  `cwRecursiveApproximateSparseRetainedCoarse` names the
  finite set whose cardinality the quantitative layer must lower-bound; this module only
  transports that cardinality into the generic repair theorem.  No hole bound is proved.

## Why the grouping is fixed once

`cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup` is invoked exactly once, in
`cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies`, to fix a single
grouping `G`; the exact-profile invariant is then obtained from
`cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact` for that same support.  The
existential target-box endpoint is never invoked per quotient, which would yield an incoherent
family of groupings.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-! ## The finite sparse supply -/

/-- Retained quotients whose recursive compact hole triple satisfies the literal paper
hole-density inequality against the exact full-child target alphabet.

This is the set whose cardinality the quantitative type-counting layer must lower-bound.  It is
deliberately defined without reference to the projection-closure or exact-profile proofs, so that
a client which has fixed one grouping can state its count before those proofs are named. -/
noncomputable def cwRecursiveApproximateSparseRetainedCoarse
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n)
    (base : ℕ) :
    Finset (cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference) := by
  classical
  exact Finset.univ.filter fun coarse ↦ ∀ physicalLeg,
    base * (4 * (cwRecursiveApproximateCleanedFiberHoles K q partAt term hmultiplicity
      epsilon sigma alpha targets G reference coarse.1
      (cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
        partAt sigma term alpha coarseKept reference coarse) physicalLeg).card) ≤
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg).card

@[simp] theorem mem_cwRecursiveApproximateSparseRetainedCoarse_iff
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n)
    (base : ℕ)
    (coarse : cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference) :
    coarse ∈ cwRecursiveApproximateSparseRetainedCoarse K q partAt term hmultiplicity
        epsilon sigma alpha targets coarseKept G reference base ↔
      ∀ physicalLeg,
        base * (4 * (cwRecursiveApproximateCleanedFiberHoles K q partAt term hmultiplicity
          epsilon sigma alpha targets G reference coarse.1
          (cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
            partAt sigma term alpha coarseKept reference coarse) physicalLeg).card) ≤
          (cwRecursiveExactTargetFiberParts
            partAt sigma targets reference physicalLeg).card := by
  classical
  simp [cwRecursiveApproximateSparseRetainedCoarse]

/-- The independently defined sparse supply is exactly the generic model's `sparseIndices`.
The ambient cardinality in the generic condition is `Fintype.card` of the compact target-part
type, which is by construction the cardinality of the exact full-child target alphabet. -/
theorem cwRecursiveApproximateSparseRetainedCoarse_eq_sparseIndices
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (base : ℕ) :
    cwRecursiveApproximateSparseRetainedCoarse K q partAt term hmultiplicity epsilon
        sigma alpha targets coarseKept G reference base =
      (cwRecursiveApproximateTargetCleanedModel K q partAt term hmultiplicity epsilon
        sigma alpha targets coarseKept finalSupport hclosed hExact G hgroup reference
          hreference).sparseIndices base := by
  classical
  ext coarse
  rw [HoleRepair.ModeledFiberFamily.mem_sparseIndices_iff,
    mem_cwRecursiveApproximateSparseRetainedCoarse_iff]
  simp only [cwRecursiveApproximateTargetCleanedModel, Fintype_card_BoxPart]

/-! ## Restricting the all-quotient direct sum to the retained subtype -/

/-- The grouped cleaned family over all quotients restricts to its retained
same-tagged-multiplicity subfamily.  This is the generic finite subfamily restriction; no
property of the recursive quotient alphabet is used. -/
theorem cwRecursiveApproximateGroupedFibers_restricts_retained
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n) :
    Restricts
      (Tensor.indexedDirectSum
        (fun coarse : CWRecursiveCoarseAddress depth n ↦ (G.fiber coarse).realize))
      (Tensor.indexedDirectSum
        (fun coarse : cwRecursiveApproximateRetainedCoarseSupport
            partAt sigma term alpha coarseKept reference ↦
          (G.fiber coarse.1).realize)) :=
  Tensor.Restricts.indexedDirectSum_subfamily
    (fun coarse : CWRecursiveCoarseAddress depth n ↦ (G.fiber coarse).realize)
    (cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference)

/-! ## Postcomposing the generic modeled-family repair theorem -/

/-- A sparse count over the retained subtype supplies disjoint varying repair plans and an
indexed direct sum of intact compact full-child target boxes.

`relabelings` is the named hypothesis discussed in the module header; it is **not** proved here,
but a committed value of its type now exists — see the module header. -/
theorem exists_cwRecursiveApproximateTarget_repairPlans_of_sparse_count
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    {Relabel : Type} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel)
      (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwRecursiveApproximateSparseRetainedCoarse K q partAt term hmultiplicity epsilon
        sigma alpha targets coarseKept G reference base).card) :
    ∃ plans : O → Tensor.RepairPlan
        (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
          (cwRecursiveExactTargetFiberParts partAt sigma targets reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwRecursiveApproximateRetainedCoarseSupport
            partAt sigma term alpha coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            (cwRecursiveApproximateTargetCleanedModel K q partAt term hmultiplicity
              epsilon sigma alpha targets coarseKept finalSupport hclosed hExact G hgroup
                reference hreference).holes (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum
            (fun coarse : cwRecursiveApproximateRetainedCoarseSupport
                partAt sigma term alpha coarseKept reference ↦
              (G.fiber coarse.1).realize))
          (Tensor.indexedDirectSum (fun _output : O ↦
            ((compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
              (cwRecursiveExactTargetFiberParts
                partAt sigma targets reference)).box target).realize)) := by
  apply (cwRecursiveApproximateTargetCleanedModel K q partAt term hmultiplicity epsilon
    sigma alpha targets coarseKept finalSupport hclosed hExact G hgroup reference
      hreference).exists_repairPlans_of_mul_budget_le_sparse
        relabelings hbase d target hdepth
  rw [← cwRecursiveApproximateSparseRetainedCoarse_eq_sparseIndices K q partAt term
    hmultiplicity epsilon sigma alpha targets coarseKept finalSupport hclosed hExact G
      hgroup reference hreference base]
  exact hcount

/-- The all-quotient cleaned direct sum restricts to the requested number of intact compact
full-child target boxes.  This is the composition of the subfamily restriction with the generic
repair conclusion; it is the shape a degeneration client consumes. -/
theorem cwRecursiveApproximateGroupedFibers_restricts_repairedTargetCopies
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    {Relabel : Type} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel)
      (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwRecursiveApproximateSparseRetainedCoarse K q partAt term hmultiplicity epsilon
        sigma alpha targets coarseKept G reference base).card) :
    Restricts
      (Tensor.indexedDirectSum
        (fun coarse : CWRecursiveCoarseAddress depth n ↦ (G.fiber coarse).realize))
      (Tensor.indexedDirectSum (fun _output : O ↦
        ((compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
          (cwRecursiveExactTargetFiberParts
            partAt sigma targets reference)).box target).realize)) := by
  obtain ⟨_plans, _pick, _hholes, hrepair⟩ :=
    exists_cwRecursiveApproximateTarget_repairPlans_of_sparse_count K q partAt term
      hmultiplicity epsilon sigma alpha targets coarseKept finalSupport hclosed hExact G
        hgroup reference hreference relabelings hbase d target hdepth hcount
  exact (cwRecursiveApproximateGroupedFibers_restricts_retained K q partAt term
    hmultiplicity epsilon sigma alpha G coarseKept reference).trans hrepair

/-! ## One cleanup call, one grouping, repaired target copies -/

/-- Recursive approximate cleanup, run **once**, together with the repair of its retained
same-tagged-multiplicity fibers into intact compact full-child target boxes.

The projection closure and the three exact-profile invariants are conclusions of the cleanup
construction, obtained here from `…_withCoarseGroup` and `…_finalMatchesExact` for the single
grouping that cleanup returns; no caller supplies them.  The sparse count appears as an
implication *inside* the existential precisely because it must speak about that one grouping.

The two remaining inputs are exactly the two honest obligations of the census: the named
relabeling family `relabelings` (unproved for this target — see the module header) and the
cardinality lower bound that discharges the implication's antecedent.  This module proves
neither. -/
theorem cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies
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
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X)) coarseKept)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    {Relabel : Type} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel)
      (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)))
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
  obtain ⟨G, hgroup, hclosed, hcleanup⟩ :=
    cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept hcoarseX
  have hmatches := cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  refine ⟨_, G, hgroup, hcleanup, fun hcount ↦ hcleanup.trans ?_⟩
  exact cwRecursiveApproximateGroupedFibers_restricts_repairedTargetCopies K q partAt term
    hmultiplicity epsilon sigma alpha targets coarseKept _ hclosed
      (fun address haddress logicalLeg ↦ by
        cases logicalLeg with
        | X => exact hmatches address haddress .X
        | Y => exact hmatches address haddress .Y
        | Z => exact hmatches address haddress .Z)
      G hgroup reference hreference relabelings hbase d target hdepth hcount

end AlgebraicComplexity.Examples
