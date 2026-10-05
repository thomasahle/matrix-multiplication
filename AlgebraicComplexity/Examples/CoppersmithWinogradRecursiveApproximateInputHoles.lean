/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetBox

/-!
# Input-profile holes in a recursive CW target alphabet

The intact recursive target alphabet is defined by exact child complete-split tables.  A label in
that alphabet may nevertheless be absent from the source because joining its two child halves
does not satisfy the approximately prescribed parent complete-split law.  This module isolates
that first class of holes from the holes introduced later by compatibility cleanup.

The separation is exact and finite.  After normalizing a present cleaned fiber to one reference
quotient, the complement of its moved labels in the target alphabet is the disjoint union of:

* target labels failing the parent approximate-profile predicate; and
* target labels passing that predicate but absent after cleanup.

No probability estimate or asymptotic bound is used.  The downstream concentration theorem has
the single task of bounding the first set; the compatibility incidence theorem bounds the second.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The one-leg predicate imposed by the approximate parent interface selector. -/
def cwRecursiveParentLabelApproximatelyMatches
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) : Prop :=
  ((cwRecursiveSemanticParentTerm term hmultiplicity).split physicalLeg).MatchesEncodedPositiveWordApproximately
      (cwChunkSplitWord (depth + 1)) fine epsilon

/-- Exact target labels which also pass the approximate parent input predicate. -/
noncomputable def cwRecursiveApproximateInputTargetParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    Finset (PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) := by
  classical
  exact (cwRecursiveExactTargetFiberParts
    partAt sigma targets reference physicalLeg).filter
      (cwRecursiveParentLabelApproximatelyMatches
        term hmultiplicity epsilon physicalLeg)

@[simp] theorem mem_cwRecursiveApproximateInputTargetParts_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    fine ∈ cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets reference physicalLeg ↔
      fine ∈ cwRecursiveExactTargetFiberParts
          partAt sigma targets reference physicalLeg ∧
        cwRecursiveParentLabelApproximatelyMatches
          term hmultiplicity epsilon physicalLeg fine := by
  classical
  simp [cwRecursiveApproximateInputTargetParts]

/-- Exact target labels rejected solely by the approximate parent input profile. -/
noncomputable def cwRecursiveInputProfileHoles
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    Finset (PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :=
  cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg \
    cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg

@[simp] theorem mem_cwRecursiveInputProfileHoles_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    fine ∈ cwRecursiveInputProfileHoles
        partAt sigma term hmultiplicity epsilon targets reference physicalLeg ↔
      fine ∈ cwRecursiveExactTargetFiberParts
          partAt sigma targets reference physicalLeg ∧
        ¬ cwRecursiveParentLabelApproximatelyMatches
          term hmultiplicity epsilon physicalLeg fine := by
  classical
  simp only [cwRecursiveInputProfileHoles, Finset.mem_sdiff,
    mem_cwRecursiveApproximateInputTargetParts_iff]
  tauto

/-- Every label occurring in a cleaned approximate-input fiber satisfies the parent approximate
profile predicate on its physical leg. -/
theorem cwRecursiveApproximateCleanedFiberParts_parentLabelApproximatelyMatches
    (K : Type u) [CommRing K] (q : ℕ)
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (coarse : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (hfine : fine ∈ G.fiberParts coarse physicalLeg) :
    cwRecursiveParentLabelApproximatelyMatches
      term hmultiplicity epsilon physicalLeg fine := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  obtain ⟨address, haddress, _hgroup, hlabel⟩ :=
    (G.mem_fiberParts_iff coarse physicalLeg fine).1 hfine
  have hambient : address ∈ fineAmbient := hclosed.1 haddress
  have halpha : address ∈ alphaSelected.support :=
    (mem_cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept address).1 hambient |>.1
  have hparent :=
    (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha address).1 halpha |>.1
  change address ∈
    ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
      (fun _c ↦ cwChunkSplitWord (depth + 1))
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
      epsilon).support at hparent
  have hpredicate :=
    ((Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
      (cwChunkPartitionedTensor K q (depth + 1))
      (fun _c ↦ cwChunkSplitWord (depth + 1))
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
      epsilon address).1 hparent).2 physicalLeg
  simpa [cwRecursiveParentLabelApproximatelyMatches,
    CompleteSplitDistribution.MatchesEncodedPositiveWordApproximately, hlabel] using hpredicate

/-- After same-type normalization, every moved present label lies in the portion of the exact
target alphabet admitted by the approximate parent input. -/
theorem cwRecursiveApproximateMovedCleanedFiberParts_subset_inputTargetParts
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
    (hcoarse : coarse ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    cwRecursiveApproximateMovedCleanedFiberParts
        K q partAt term hmultiplicity epsilon sigma alpha G
          reference coarse hsame physicalLeg ⊆
      cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets reference physicalLeg := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  intro fine hfine
  apply (mem_cwRecursiveApproximateInputTargetParts_iff
    partAt sigma term hmultiplicity epsilon targets reference physicalLeg fine).2
  constructor
  · exact cwRecursiveApproximateMovedCleanedFiberParts_subset_reference
      K q partAt term hmultiplicity epsilon sigma alpha targets finalSupport hExact
        G hgroup reference coarse hreference hcoarse hsame physicalLeg hfine
  · change fine ∈ relabelParts relabeling.partEquiv
      (G.fiberParts coarse) physicalLeg at hfine
    let source :=
      (positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau).symm fine
    have hfine' : source ∈ G.fiberParts coarse physicalLeg := by
      simpa [source, relabeling] using hfine
    have hsource : cwRecursiveParentLabelApproximatelyMatches
        term hmultiplicity epsilon physicalLeg source :=
      cwRecursiveApproximateCleanedFiberParts_parentLabelApproximatelyMatches
        K q term hmultiplicity epsilon sigma alpha coarseKept finalSupport hclosed
          G coarse physicalLeg source hfine'
    have hinvariant :=
      ((cwRecursiveSemanticParentTerm term hmultiplicity).split physicalLeg).matchesEncodedPositiveWordApproximately_positionEquiv_iff
          (cwChunkSplitWord (depth + 1)) source tau epsilon
    have hmoved := hinvariant.mpr hsource
    simpa [cwRecursiveParentLabelApproximatelyMatches, source] using hmoved

/-- Target labels admitted by the approximate input but absent from the normalized cleaned fiber.
These are precisely the non-input-profile holes; later counting identifies their compatibility
incidence source. -/
noncomputable def cwRecursiveCompatibilityCleanupHoles
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
    Finset (PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :=
  cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg \
    cwRecursiveApproximateMovedCleanedFiberParts
      K q partAt term hmultiplicity epsilon sigma alpha G
        reference coarse hsame physicalLeg

/-- The whole missing target alphabet is exactly the disjoint union of input-profile holes and
post-input cleanup holes. -/
theorem cwRecursive_target_sdiff_moved_eq_inputProfileHoles_union_cleanupHoles
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
    (hcoarse : coarse ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg \
        cwRecursiveApproximateMovedCleanedFiberParts
          K q partAt term hmultiplicity epsilon sigma alpha G
            reference coarse hsame physicalLeg =
      cwRecursiveInputProfileHoles
          partAt sigma term hmultiplicity epsilon targets reference physicalLeg ∪
        cwRecursiveCompatibilityCleanupHoles
          K q partAt term hmultiplicity epsilon sigma alpha targets G
            reference coarse hsame physicalLeg := by
  classical
  let target := cwRecursiveExactTargetFiberParts
    partAt sigma targets reference physicalLeg
  let input := cwRecursiveApproximateInputTargetParts
    partAt sigma term hmultiplicity epsilon targets reference physicalLeg
  let moved := cwRecursiveApproximateMovedCleanedFiberParts
    K q partAt term hmultiplicity epsilon sigma alpha G
      reference coarse hsame physicalLeg
  have hinputTarget : input ⊆ target := by
    intro fine hfine
    exact (mem_cwRecursiveApproximateInputTargetParts_iff
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg fine).1 hfine |>.1
  have hmovedInput : moved ⊆ input := by
    simpa [moved, input] using
      cwRecursiveApproximateMovedCleanedFiberParts_subset_inputTargetParts
        K q partAt term hmultiplicity epsilon sigma alpha targets coarseKept
          finalSupport hclosed hExact G hgroup reference coarse hreference hcoarse
            hsame physicalLeg
  change target \ moved = (target \ input) ∪ (input \ moved)
  ext fine
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨htarget, hnotMoved⟩
    by_cases hinput : fine ∈ input
    · exact Or.inr ⟨hinput, hnotMoved⟩
    · exact Or.inl ⟨htarget, hinput⟩
  · rintro (hinputHole | hcleanupHole)
    · refine ⟨hinputHole.1, ?_⟩
      intro hmoved
      exact hinputHole.2 (hmovedInput hmoved)
    · exact ⟨hinputTarget hcleanupHole.1, hcleanupHole.2⟩

/-- The two hole classes in the exact decomposition are disjoint. -/
theorem cwRecursive_inputProfileHoles_disjoint_cleanupHoles
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
    Disjoint
      (cwRecursiveInputProfileHoles
        partAt sigma term hmultiplicity epsilon targets reference physicalLeg)
      (cwRecursiveCompatibilityCleanupHoles
        K q partAt term hmultiplicity epsilon sigma alpha targets G
          reference coarse hsame physicalLeg) := by
  classical
  apply Finset.disjoint_left.2
  intro fine hinput hcleanup
  have hnotGood := (mem_cwRecursiveInputProfileHoles_iff
    partAt sigma term hmultiplicity epsilon targets reference physicalLeg fine).1 hinput |>.2
  have hgood : fine ∈ cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg :=
    (Finset.mem_sdiff.mp hcleanup).1
  exact hnotGood ((mem_cwRecursiveApproximateInputTargetParts_iff
    partAt sigma term hmultiplicity epsilon targets reference physicalLeg fine).1 hgood |>.2)

/-! ## Direct cleanup-to-hole-decomposition constructor -/

/-- Construct one cleaned approximate recursive fiber together with its exact damaged-box model
and disjoint hole decomposition.

The final support, grouping, projection closure, and exact-profile facts are all constructed
internally.  Thus a repair client receives one coherent witness rather than independently supplied
semantic premises which might describe different cleanups. -/
theorem exists_cwRecursiveApproximate_orientedGroupedCleanup_holeDecomposition
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
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X)) coarseKept)
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
    let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha
    let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept
    let hashed := alphaSelected.withSupport fineAmbient
    ∃ (finalSupport : Finset (BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
      (G : (alphaSelected.withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n)),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support finalSupport Finset.univ ∧
          Restricts hashed.realize
            (Tensor.indexedDirectSum (fun quotient ↦ (G.fiber quotient).realize)) ∧
          Restricts (G.fiber coarse).realize
            ((compactBox
                ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
                (cwRecursiveExactTargetFiberParts
                  partAt sigma targets reference)).box
              (compactBoxSubparts
                (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
                (cwRecursiveApproximateMovedCleanedFiberParts
                  K q partAt term hmultiplicity epsilon sigma alpha G
                    reference coarse hsame))).realize ∧
          ∀ physicalLeg,
            cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg \
                cwRecursiveApproximateMovedCleanedFiberParts
                  K q partAt term hmultiplicity epsilon sigma alpha G
                    reference coarse hsame physicalLeg =
              cwRecursiveInputProfileHoles
                  partAt sigma term hmultiplicity epsilon targets reference physicalLeg ∪
                cwRecursiveCompatibilityCleanupHoles
                  K q partAt term hmultiplicity epsilon sigma alpha targets G
                    reference coarse hsame physicalLeg ∧
            Disjoint
              (cwRecursiveInputProfileHoles
                partAt sigma term hmultiplicity epsilon targets reference physicalLeg)
              (cwRecursiveCompatibilityCleanupHoles
                K q partAt term hmultiplicity epsilon sigma alpha targets G
                  reference coarse hsame physicalLeg) := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  change ∃ (finalSupport : Finset (BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
      (G : (alphaSelected.withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n)),
    (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
      IsProjectionClosed hashed.support finalSupport Finset.univ ∧
        Restricts hashed.realize
          (Tensor.indexedDirectSum (fun quotient ↦ (G.fiber quotient).realize)) ∧
        Restricts (G.fiber coarse).realize
          ((compactBox
              ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
              (cwRecursiveExactTargetFiberParts
                partAt sigma targets reference)).box
            (compactBoxSubparts
              (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
              (cwRecursiveApproximateMovedCleanedFiberParts
                K q partAt term hmultiplicity epsilon sigma alpha G
                  reference coarse hsame))).realize ∧
        ∀ physicalLeg,
          cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg \
              cwRecursiveApproximateMovedCleanedFiberParts
                K q partAt term hmultiplicity epsilon sigma alpha G
                  reference coarse hsame physicalLeg =
            cwRecursiveInputProfileHoles
                partAt sigma term hmultiplicity epsilon targets reference physicalLeg ∪
              cwRecursiveCompatibilityCleanupHoles
                K q partAt term hmultiplicity epsilon sigma alpha targets G
                  reference coarse hsame physicalLeg ∧
          Disjoint
            (cwRecursiveInputProfileHoles
              partAt sigma term hmultiplicity epsilon targets reference physicalLeg)
            (cwRecursiveCompatibilityCleanupHoles
              K q partAt term hmultiplicity epsilon sigma alpha targets G
                reference coarse hsame physicalLeg)
  obtain ⟨G, hgroup, hclosed, hcleanup, hbox⟩ :=
    cwRecursiveApproximate_orientedGroupedCleanup_withTargetBox
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept hcoarseX
        reference coarse hreference hcoarseSupport hcoarseKept hsame
  have hExact : ∀ address ∈ zUsefulSupport, ∀ logicalLeg,
      model.MatchesExact (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg) := by
    intro address haddress logicalLeg
    cases logicalLeg with
    | X =>
        exact cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
            address haddress .X
    | Y =>
        exact cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
            address haddress .Y
    | Z =>
        exact cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
            address haddress .Z
  refine ⟨zUsefulSupport, G, hgroup, hclosed, hcleanup, hbox, ?_⟩
  intro physicalLeg
  constructor
  · exact cwRecursive_target_sdiff_moved_eq_inputProfileHoles_union_cleanupHoles
      K q partAt term hmultiplicity epsilon sigma alpha targets coarseKept zUsefulSupport
        hclosed hExact G hgroup reference coarse hreference hcoarseSupport hsame physicalLeg
  · exact cwRecursive_inputProfileHoles_disjoint_cleanupHoles
      K q partAt term hmultiplicity epsilon sigma alpha targets G reference coarse hsame
        physicalLeg

end AlgebraicComplexity.Examples
