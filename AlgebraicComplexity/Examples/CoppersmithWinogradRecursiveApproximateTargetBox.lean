/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateCleanup
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiber
import AlgebraicComplexity.Tensor.PartitionedBoxRetyping
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

/-!
# Recursive CW cleanup inside the full child target box

The approximate parent selector is smaller than the independently assembled standard child
product.  Consequently a cleaned quotient fiber must be compared with a box of the full parent
positive power, rather than with a box of one exactly selected parent empirical type.  The labels
missing from this larger box include the input-profile holes of the recursive constituent theorem.

This module proves the finite semantic comparison.  It reconstructs approximate-input and
ordered-left-marginal membership legwise from witnesses already present in a cleaned fiber, moves
same-type quotient fibers by paired parent-position permutations, and restricts each moved fiber
to a damaged compact box whose intact alphabet is the exact independently assembled child target.

No concentration estimate, compatibility competitor count, sparse-hole bound, repair plan,
asymptotic passage, or certificate-specific number is assumed or proved here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## A present cleaned fiber is a box of the full parent positive power -/

/-- Projection-closed cleanup inside one retained relaxed quotient creates no hidden
non-Cartesian deletion relative to the full parent positive power.

The converse direction is the important one.  Given one full-parent address whose three leg
labels each occur in the cleaned fiber, witnesses for those labels reconstruct the approximate
complete-split predicates and the three exact ordered-left marginals.  Readability of the
quotient reconstructs membership in the retained coarse fiber, after which projection closure
reconstructs membership in the final support. -/
theorem cwRecursiveApproximateCleanedFiber_eq_fullParentBox_fiberParts
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
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (coarse : CWRecursiveCoarseAddress depth n)
    (hcoarse : coarse ∈ coarseKept) :
    G.fiber coarse =
      ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (G.fiberParts coarse) := by
  classical
  let full := (cwChunkPartitionedTensor K q (depth + 1)).positivePower n
  let parentApprox := cwSelectedApproximateInterfaceTerm K q
    (cwRecursiveSemanticParentTerm term hmultiplicity)
    (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.LegGrouping.fiber,
      PartitionedTensor.withSupport_support,
      PartitionedTensor.LegGrouping.fiberSupport, Finset.mem_filter,
      PartitionedTensor.mem_box_support]
    constructor
    · rintro ⟨hfinal, haddressGroup⟩
      have hambient : address ∈ fineAmbient := hclosed.1 hfinal
      have halpha : address ∈ alphaSelected.support :=
        (mem_cwRecursiveFineSupportOverCoarseSupport
          alphaSelected.support coarseKept address).1 hambient |>.1
      have hparent : address ∈ parentApprox.support :=
        (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
          K q term hmultiplicity epsilon sigma alpha address).1 halpha |>.1
      have hfull : address ∈ full.support := by
        change address ∈
          ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon).support at hparent
        exact ((Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
          (cwChunkPartitionedTensor K q (depth + 1))
          (fun _c ↦ cwChunkSplitWord (depth + 1))
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon address).1 hparent).1
      refine ⟨hfull, ?_⟩
      intro physicalLeg
      exact (G.mem_fiberParts_iff coarse physicalLeg (address physicalLeg)).2
        ⟨address, hfinal, haddressGroup, rfl⟩
    · rintro ⟨hfull, hparts⟩
      have hcoarseAddress : cwRecursiveChildGroup depth n address = coarse := by
        funext physicalLeg occurrence
        obtain ⟨witness, _hwitness, hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff coarse physicalLeg (address physicalLeg)).1
            (hparts physicalLeg)
        calc
          cwRecursiveChildGroup depth n address physicalLeg occurrence =
              cwRecursiveLabelledChildWord depth n
                (address physicalLeg) occurrence := rfl
          _ =
              cwRecursiveLabelledChildWord depth n
                (witness physicalLeg) occurrence := by rw [hwitnessLabel]
          _ = cwRecursiveChildGroup depth n witness physicalLeg occurrence := rfl
          _ = coarse physicalLeg occurrence := by
            rw [← hgroup witness, hwitnessGroup]
      have hparent : address ∈ parentApprox.support := by
        change address ∈
          ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon).support
        apply (Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
          (cwChunkPartitionedTensor K q (depth + 1))
          (fun _c ↦ cwChunkSplitWord (depth + 1))
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon address).2
        refine ⟨hfull, ?_⟩
        intro physicalLeg
        obtain ⟨witness, hwitness, _hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff coarse physicalLeg (address physicalLeg)).1
            (hparts physicalLeg)
        have hwitnessAmbient : witness ∈ fineAmbient := hclosed.1 hwitness
        have hwitnessAlpha : witness ∈ alphaSelected.support :=
          (mem_cwRecursiveFineSupportOverCoarseSupport
            alphaSelected.support coarseKept witness).1 hwitnessAmbient |>.1
        have hwitnessParent : witness ∈ parentApprox.support :=
          (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
            K q term hmultiplicity epsilon sigma alpha witness).1 hwitnessAlpha |>.1
        change witness ∈
          ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon).support at hwitnessParent
        have hwitnessPredicate :=
          ((Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
            (cwChunkPartitionedTensor K q (depth + 1))
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon witness).1 hwitnessParent).2 physicalLeg
        simpa [hwitnessLabel] using hwitnessPredicate
      have halpha : address ∈ alphaSelected.support := by
        apply (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
          K q term hmultiplicity epsilon sigma alpha address).2
        refine ⟨hparent, ?_⟩
        intro physicalLeg
        obtain ⟨witness, hwitness, _hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff coarse physicalLeg (address physicalLeg)).1
            (hparts physicalLeg)
        have hwitnessAmbient : witness ∈ fineAmbient := hclosed.1 hwitness
        have hwitnessAlpha : witness ∈ alphaSelected.support :=
          (mem_cwRecursiveFineSupportOverCoarseSupport
            alphaSelected.support coarseKept witness).1 hwitnessAmbient |>.1
        have hwitnessMarginal :=
          (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
            K q term hmultiplicity epsilon sigma alpha witness).1 hwitnessAlpha |>.2
              physicalLeg
        simpa [hwitnessLabel] using hwitnessMarginal
      have hambient : address ∈ fineAmbient :=
        (mem_cwRecursiveFineSupportOverCoarseSupport
          alphaSelected.support coarseKept address).2
          ⟨halpha, hcoarseAddress.symm ▸ hcoarse⟩
      have hfinal : address ∈ finalSupport := by
        apply hclosed.2 address hambient
        intro physicalLeg _hactive
        obtain ⟨witness, hwitness, _hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff coarse physicalLeg (address physicalLeg)).1
            (hparts physicalLeg)
        exact ⟨witness, hwitness, hwitnessLabel.symm⟩
      refine ⟨hfinal, ?_⟩
      rw [hgroup address, hcoarseAddress]
  · rfl

/-! ## Exact target membership and same-type transport -/

/-- Every physical-leg label in an approximately selected cleaned fiber realizes the prescribed
exact child profile for that quotient.  Approximate input membership is irrelevant to this local
statement; only final-support exactness and quotient readability are used. -/
theorem cwRecursiveApproximateCleanedFiberParts_subset_exactTarget
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (coarse : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    G.fiberParts coarse physicalLeg ⊆
      cwRecursiveExactTargetFiberParts
        partAt sigma targets coarse physicalLeg := by
  classical
  intro fine hfine
  obtain ⟨address, haddress, haddressGroup, hlabel⟩ :=
    (G.mem_fiberParts_iff coarse physicalLeg fine).1 hfine
  have hcoarse : cwRecursiveChildGroup depth n address = coarse := by
    calc
      cwRecursiveChildGroup depth n address = G.group address :=
        (hgroup address).symm
      _ = coarse := haddressGroup
  apply (mem_cwRecursiveExactTargetFiberParts_iff
    partAt sigma targets coarse physicalLeg fine).2
  constructor
  · calc
      cwRecursiveLabelledChildWord depth n fine =
          cwRecursiveLabelledChildWord depth n (address physicalLeg) := by rw [hlabel]
      _ = cwRecursiveChildGroup depth n address physicalLeg := rfl
      _ = coarse physicalLeg := congrFun hcoarse physicalLeg
  · intro cell word
    let logicalLeg := sigma.symm physicalLeg
    have hphysical : sigma logicalLeg = physicalLeg :=
      sigma.apply_symm_apply physicalLeg
    have hmatch := hExact address haddress logicalLeg cell word
    have hcoarseModel :
        (cwRecursiveChildCompatibilityModel depth n partAt).coarse
            (logicalAddress sigma address) =
          cwRecursiveOrientedCoarseIndexSequence
            depth n partAt sigma coarse := by
      rw [cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence,
        hcoarse]
    have hchunks :
        (cwRecursiveChildCompatibilityModel depth n partAt).chunks logicalLeg
            (logicalAddress sigma address logicalLeg) =
          positiveWordLabelledChildren
            (cwChunkSplitWord (depth + 1)) fine := by
      funext occurrence
      change positiveWordLabelledChildren
          (cwChunkSplitWord (depth + 1)) (address (sigma logicalLeg)) occurrence =
        positiveWordLabelledChildren
          (cwChunkSplitWord (depth + 1)) fine occurrence
      rw [hphysical, hlabel]
    rw [hcoarseModel, hchunks] at hmatch
    exact hmatch

/-- Fine labels surviving in one approximate-input cleaned quotient fiber, transported to a
reference quotient by the canonical paired parent-position permutation of the full parent
positive power. -/
noncomputable def cwRecursiveApproximateMovedCleanedFiberParts
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part]
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse)) :
    ∀ _c : Leg,
      Finset (PositiveWord
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :=
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  relabelParts relabeling.partEquiv (G.fiberParts coarse)

/-- The moved present labels lie in the exact full-child target alphabet of the reference
quotient.  Reference and source quotients need only belong to the relaxed abstract ambient; no
fine lift in one exact parent empirical type is required. -/
theorem cwRecursiveApproximateMovedCleanedFiberParts_subset_reference
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
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
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
      cwRecursiveExactTargetFiberParts
        partAt sigma targets reference physicalLeg := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  have hpart : partAt ∘ tau = partAt :=
    partAt_comp_cwRecursivePositionPermOfSameTaggedMultiplicity
      partAt sigma reference coarse hsame
  have hquotient :
      cwRecursivePositionRelabelCoarseAddress depth n tau coarse = reference :=
    cwRecursivePositionRelabelCoarseAddress_of_relaxedAmbient_sameTaggedMultiplicity
      partAt term sigma alpha reference coarse hreference hcoarse hsame
  intro fine hfine
  change fine ∈ relabelParts relabeling.partEquiv
    (G.fiberParts coarse) physicalLeg at hfine
  have hfine' :
      (positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau).symm fine ∈
        G.fiberParts coarse physicalLeg := by
    simpa [relabeling] using hfine
  have hsource := cwRecursiveApproximateCleanedFiberParts_subset_exactTarget
    K q partAt term hmultiplicity epsilon sigma alpha targets finalSupport hExact
      G hgroup coarse physicalLeg hfine'
  simpa using cwRecursiveExactTargetFiberParts_positionRelabel
    partAt sigma targets reference coarse tau hpart hquotient physicalLeg hsource

/-! ## Restriction to a damaged compact full-child target -/

/-- A cleaned same-type quotient fiber restricts to a damaged box in the compact exact target
tensor cut out of the full parent positive power.  The complement of the moved present labels is
therefore the joint input-profile/compatibility hole set required by the paper. -/
theorem cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox
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
        (compactBoxSubparts
          (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
          (cwRecursiveApproximateMovedCleanedFiberParts
            K q partAt term hmultiplicity epsilon sigma alpha G
              reference coarse hsame))).realize := by
  let full := (cwChunkPartitionedTensor K q (depth + 1)).positivePower n
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  let moved := cwRecursiveApproximateMovedCleanedFiberParts
    K q partAt term hmultiplicity epsilon sigma alpha G reference coarse hsame
  have hfiber : G.fiber coarse = full.box (G.fiberParts coarse) :=
    cwRecursiveApproximateCleanedFiber_eq_fullParentBox_fiberParts
      K q term hmultiplicity epsilon sigma alpha coarseKept finalSupport hclosed
        G hgroup coarse hcoarseKept
  have hrelabel : Isomorphic (full.box (G.fiberParts coarse)).realize
      (full.box moved).realize := by
    simpa [moved, cwRecursiveApproximateMovedCleanedFiberParts, tau, relabeling] using
      relabeling.box_isomorphic (G.fiberParts coarse)
  have hsubset : ∀ physicalLeg, moved physicalLeg ⊆
      cwRecursiveExactTargetFiberParts
        partAt sigma targets reference physicalLeg := by
    intro physicalLeg
    simpa [moved] using
      cwRecursiveApproximateMovedCleanedFiberParts_subset_reference
        K q partAt term hmultiplicity epsilon sigma alpha targets finalSupport hExact
          G hgroup reference coarse hreference hcoarseSupport hsame physicalLeg
  exact (Restricts.of_eq (congrArg PartitionedTensor.realize hfiber)).trans
    (hrelabel.restricts.trans
      (Restricts.box_to_compactBox_box full
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
        moved hsubset))

/-! ## Direct composition with approximate cleanup -/

/-- Approximate-input cleanup constructs both the grouped direct sum and, for every retained
same-type quotient, its restriction to a damaged compact box in the full exact child target.

The projection closure and exact-profile invariant are conclusions of the cleanup construction;
neither is accepted as a client premise.  The remaining hypotheses refer only to the retained
coarse family and to the common tagged multiplicity class used to transport one quotient to the
chosen reference. -/
theorem cwRecursiveApproximate_orientedGroupedCleanup_withTargetBox
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
    let group := cwRecursiveChildGroup depth n
    let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept
    let hashed := alphaSelected.withSupport fineAmbient
    let model := cwRecursiveChildCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support group (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support group (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    ∃ G : (alphaSelected.withSupport zUsefulSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
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
                    reference coarse hsame))).realize := by
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
  let zUseful := zIsolated.withSupport zUsefulSupport
  change ∃ G : (alphaSelected.withSupport zUsefulSupport).LegGrouping
      (CWRecursiveCoarseAddress depth n),
    (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
      IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
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
                  reference coarse hsame))).realize
  obtain ⟨G, hgroup, hclosed, hcleanup⟩ :=
    cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept hcoarseX
  change (alphaSelected.withSupport zUsefulSupport).LegGrouping
    (CWRecursiveCoarseAddress depth n) at G
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
  refine ⟨G, hgroup, hclosed, hcleanup, ?_⟩
  exact cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox
    K q partAt term hmultiplicity epsilon sigma alpha targets coarseKept zUsefulSupport
      hclosed hExact G hgroup reference coarse hreference hcoarseSupport hcoarseKept hsame

end AlgebraicComplexity.Examples
