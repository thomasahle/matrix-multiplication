/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetBox
import AlgebraicComplexity.MatrixMultiplication.GroupedVariableHoleRepair

/-!
# Recursive approximate cleanup fibers as one modeled damaged-box family

This module is **mechanical packaging only**.  It contains no counting argument, no hole-density
estimate, no relabeling construction, and no asymptotic passage.  Everything proved here is a
retyping of results already committed elsewhere:
`cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox` supplies the entire
mathematical content, and this file merely re-presents it in the shape the generic repair API
consumes.

Three pieces are assembled.

* The *retained* quotient subtype, whose elements simultaneously lie in the client's coarse
  selection `coarseKept`, lie in the relaxed abstract ambient quotient family, and share the
  tagged ordered-left type of a chosen `reference`.  The middle condition is the relaxed-ambient
  membership that the transport lemma needs; it is not a lift into any exact parent empirical
  type.
* The *compact holes* of one transported fiber, defined as `Finset.univ` minus the compact
  subparts of the moved present labels, together with the double-complement identity that turns
  them back into those subparts.
* The `HoleRepair.ModeledFiberFamily` over the compact exact full-child target of the reference.

The grouping `G` is a **parameter** of every declaration below.  That is deliberate and is the
point of the file: a client calls approximate cleanup exactly once, fixes one `G`, and then
instantiates this family over the whole retained subtype.  Calling the existential target-box
theorem separately for each quotient would produce a different grouping per quotient and would
not assemble into a family at all.

What is *not* here, and must be supplied elsewhere: the finite nonempty relabeling family
`HoleRepair.UniformStructureRelabelings` for this recursive compact target, and any lower bound
on the number of sparse retained quotients.  Neither is used, assumed, or weakened by this file.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## The retained same-tagged-multiplicity quotient subtype -/

/-- Retained quotients of one recursive approximate cleanup: kept by the client's coarse
selection, present in the relaxed abstract ambient family, and of the same tagged ordered-left
type as `reference`.

These are exactly the three side conditions of
`cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox`, bundled so that the
whole family can be indexed by a single subtype. -/
noncomputable def cwRecursiveApproximateRetainedCoarseSupport
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact coarseKept.filter fun coarse ↦
    coarse ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha ∧
      WordType.multiplicity
          (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
        WordType.multiplicity
          (cwRecursiveTaggedLeftTripleWord partAt sigma coarse)

@[simp] theorem mem_cwRecursiveApproximateRetainedCoarseSupport_iff
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference coarse : CWRecursiveCoarseAddress depth n) :
    coarse ∈ cwRecursiveApproximateRetainedCoarseSupport
        partAt sigma term alpha coarseKept reference ↔
      coarse ∈ coarseKept ∧
        coarse ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha ∧
          WordType.multiplicity
              (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
            WordType.multiplicity
              (cwRecursiveTaggedLeftTripleWord partAt sigma coarse) := by
  classical
  simp [cwRecursiveApproximateRetainedCoarseSupport, and_assoc]

/-- A retained quotient is kept by the client's coarse selection. -/
theorem cwRecursiveApproximateRetainedCoarse_mem_coarseKept
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n)
    (coarse : cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference) :
    coarse.1 ∈ coarseKept :=
  ((mem_cwRecursiveApproximateRetainedCoarseSupport_iff
    partAt sigma term alpha coarseKept reference coarse.1).1 coarse.2).1

/-- A retained quotient lies in the relaxed abstract ambient quotient family. -/
theorem cwRecursiveApproximateRetainedCoarse_mem_relaxedAmbient
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n)
    (coarse : cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference) :
    coarse.1 ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha :=
  (((mem_cwRecursiveApproximateRetainedCoarseSupport_iff
    partAt sigma term alpha coarseKept reference coarse.1).1 coarse.2).2).1

/-- A retained quotient has the tagged ordered-left type of the reference. -/
theorem cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (reference : CWRecursiveCoarseAddress depth n)
    (coarse : cwRecursiveApproximateRetainedCoarseSupport
      partAt sigma term alpha coarseKept reference) :
    WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse.1) :=
  (((mem_cwRecursiveApproximateRetainedCoarseSupport_iff
    partAt sigma term alpha coarseKept reference coarse.1).1 coarse.2).2).2

/-! ## Recursive compact holes -/

/-- The labels of the compact exact full-child target of `reference` that one transported
approximate cleanup fiber is missing.

This is the joint input-profile/compatibility hole set of the recursive step, expressed in the
compact alphabet.  No bound on its cardinality is proved anywhere in this file. -/
noncomputable def cwRecursiveApproximateCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset (BoxPart
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference) physicalLeg) :=
  Finset.univ \ compactBoxSubparts
    (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
    (cwRecursiveApproximateMovedCleanedFiberParts
      K q partAt term hmultiplicity epsilon sigma alpha G reference coarse hsame)
    physicalLeg

/-- The double-complement identity: removing the recursive compact holes from the full compact
alphabet returns exactly the surviving transported labels. -/
@[simp] theorem univ_sdiff_cwRecursiveApproximateCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset.univ \ cwRecursiveApproximateCleanedFiberHoles K q partAt term
        hmultiplicity epsilon sigma alpha targets G reference coarse hsame physicalLeg =
      compactBoxSubparts
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
        (cwRecursiveApproximateMovedCleanedFiberParts
          K q partAt term hmultiplicity epsilon sigma alpha G reference coarse hsame)
        physicalLeg := by
  classical
  apply Finset.sdiff_sdiff_eq_self
  exact Finset.subset_univ _

/-- The accepted per-fiber restriction, restated in the explicit `univ \ holes` form that the
generic modeled-family API expects.  This is `e2b1e4e`'s
`cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox` rewritten along the
double-complement identity, and nothing else. -/
theorem cwRecursiveApproximateCleanedFiber_restricts_compactHoleBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hcoarseSupport : coarse ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hcoarseKept : coarse ∈ coarseKept)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse)) :
    Restricts (G.fiber coarse).realize
      ((compactBox
          ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
          (cwRecursiveExactTargetFiberParts
            partAt sigma targets reference)).box
        (fun physicalLeg ↦ Finset.univ \
          cwRecursiveApproximateCleanedFiberHoles K q partAt term hmultiplicity
            epsilon sigma alpha targets G reference coarse hsame physicalLeg)).realize := by
  have hholes :
      (fun physicalLeg ↦ Finset.univ \
        cwRecursiveApproximateCleanedFiberHoles K q partAt term hmultiplicity
          epsilon sigma alpha targets G reference coarse hsame physicalLeg) =
        compactBoxSubparts
          (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
          (cwRecursiveApproximateMovedCleanedFiberParts
            K q partAt term hmultiplicity epsilon sigma alpha G
              reference coarse hsame) := by
    funext physicalLeg
    exact univ_sdiff_cwRecursiveApproximateCleanedFiberHoles K q partAt term
      hmultiplicity epsilon sigma alpha targets G reference coarse hsame physicalLeg
  rw [hholes]
  exact cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox
    K q partAt term hmultiplicity epsilon sigma alpha targets coarseKept finalSupport
      hclosed hExact G hgroup reference coarse hreference hcoarseSupport hcoarseKept hsame

/-! ## The modeled damaged-box family -/

/-- Every retained quotient fiber of one fixed approximate cleanup, presented as a differently
damaged box of the single compact exact full-child target of `reference`.

The grouping `G`, its projection closure, its coarse-group readability, and its exact-profile
invariant are all parameters: a client obtains them from **one** call of
`cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup` together with
`cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact` (three `logicalLeg` cases), and
then instantiates this family once.  Nothing here re-derives cleanup, and nothing here is
quantitative. -/
noncomputable def cwRecursiveApproximateTargetCleanedModel
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
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha) :
    HoleRepair.ModeledFiberFamily
      (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference))
      (fun coarse : cwRecursiveApproximateRetainedCoarseSupport
          partAt sigma term alpha coarseKept reference ↦
        (G.fiber coarse.1).realize) where
  holes coarse :=
    cwRecursiveApproximateCleanedFiberHoles K q partAt term hmultiplicity epsilon
      sigma alpha targets G reference coarse.1
      (cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
        partAt sigma term alpha coarseKept reference coarse)
  fiber_restricts coarse :=
    cwRecursiveApproximateCleanedFiber_restricts_compactHoleBox K q partAt term
      hmultiplicity epsilon sigma alpha targets coarseKept finalSupport hclosed hExact
        G hgroup reference coarse.1 hreference
        (cwRecursiveApproximateRetainedCoarse_mem_relaxedAmbient
          partAt sigma term alpha coarseKept reference coarse)
        (cwRecursiveApproximateRetainedCoarse_mem_coarseKept
          partAt sigma term alpha coarseKept reference coarse)
        (cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
          partAt sigma term alpha coarseKept reference coarse)

end AlgebraicComplexity.Examples
