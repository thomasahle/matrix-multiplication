/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputHoles

set_option autoImplicit false

/-!
# Semantic supports and operation holes for recursive approximate cleanup

This module isolates the finite semantic boundary of the recursive compatibility cleanup in
[alman2025more, Claim 6.18].  The paper's logical-`Y` compatibility and unique-triple deletion
appear in `papers/sources/2404.16349/constituent.tex:253-276`; the logical-`Z` counterparts
appear at lines 292-326.  The corresponding Total-Weight formulation is Proposition
`prop:grouped-cleanup` and the three-class damaged-box discussion in
`better_bound/paper.tex:859-898,948-1048`.

An address is *compatibility-ready* after all deterministic exact and pooled filters but before
the two grouped isolation deletions.  The declarations below construct the literal intermediate
supports, show that every final address was ready, and prove that a ready address lost before the
final support lies in the `Y`- or `Z`-deletion set.  They then transport ready labels to one
reference quotient and define the residual source-nonrealizability class.

This is deliberately the narrow, qualitative layer.  It assumes no competitor count, incidence
bound, hole charge, or asymptotic estimate; those quantitative statements remain in
`CoppersmithWinogradRecursiveApproximateCleanupHoleCharging`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v

/-- Fine parent labels at one recursive depth. -/
abbrev CWRecursiveApproximateFineLabel (depth n : ℕ) :=
  PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n

/-- Three-leg fine addresses at one recursive depth. -/
abbrev CWRecursiveApproximateFineAddress (depth n : ℕ) :=
  BlockAddress (fun _c : Leg ↦ CWRecursiveApproximateFineLabel depth n)

/-! ## The pre-isolation realizability boundary -/

/-- The four supports surrounding the two grouped compatibility isolations, together with the
final support after the exact-`Z` deterministic filter. -/
structure CWRecursiveApproximateCleanupSupportData (depth n : ℕ) where
  yAmbient : Finset (CWRecursiveApproximateFineAddress depth n)
  ySupport : Finset (CWRecursiveApproximateFineAddress depth n)
  zAmbient : Finset (CWRecursiveApproximateFineAddress depth n)
  zSupport : Finset (CWRecursiveApproximateFineAddress depth n)
  finalSupport : Finset (CWRecursiveApproximateFineAddress depth n)

/-- The literal supports used by recursive approximate cleanup.  Naming them once makes the
deleted-support codomain of the charging map independent of the existential grouping assembled
after cleanup. -/
noncomputable def cwRecursiveApproximateCleanupSupportData
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
    CWRecursiveApproximateCleanupSupportData depth n := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  exact
    { yAmbient := yFirst.support
      ySupport := ySupport
      zAmbient := zFirst.support
      zSupport := zSupport
      finalSupport := zUsefulSupport }

/-- Addresses which have passed the deterministic input filters needed on both sides of the two
grouped compatibility isolations.

Membership in `yFirst.support` already includes the exact-`X` and pooled-`Y` filters.  The three
extra conjuncts are exact `Y`, pooled `Z`, and exact `Z`.  Therefore a ready address which fails
to reach the final support is deleted by the `Y` or `Z` grouped isolation, rather than by an
intervening deterministic profile filter. -/
noncomputable def cwRecursiveApproximateCompatibilityReadySupport
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
    Finset (CWRecursiveApproximateFineAddress depth n) := by
  classical
  let supports := cwRecursiveApproximateCleanupSupportData
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let yKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let zKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  exact supports.yAmbient.filter fun address ↦
    yKeep address ∧
      CWRecursivePooledAllLabelMatches
        partAt pooled.zAll (address (sigma .Z)) ∧
      zKeep address

/-- Every final address is compatibility-ready: the final support is obtained from the `Z`
survivors by exact-`Z` filtering, and tracing it backwards recovers exact `Y`, pooled `Z`, and
membership in the first `Y` ambient. -/
theorem cwRecursiveApproximateCleanupFinalSupport_subset_ready
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
    (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled
          coarseKept).finalSupport ⊆
      cwRecursiveApproximateCompatibilityReadySupport
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  change zUsefulSupport ⊆ yFirst.support.filter fun address ↦
    yKeep address ∧
      CWRecursivePooledAllLabelMatches
        partAt pooled.zAll (address (sigma .Z)) ∧
      zKeep address
  intro address haddress
  have hzData : address ∈ zSupport ∧ zKeep address := by
    simpa [zUsefulSupport, zIsolated, groupStableSupport] using haddress
  have hzFirst : address ∈ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ hzData.1
  have hzFirstData := (mem_cwRecursivePooledZFirstZeroOut_support
    yUseful sigma partAt pooled.zAll address).mp hzFirst
  have hyData : address ∈ ySupport ∧ yKeep address := by
    simpa [yUseful, yUsefulSupport, yIsolated, groupStableSupport] using hzFirstData.1
  have hyFirst : address ∈ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY hyData.1
  exact Finset.mem_filter.mpr
    ⟨hyFirst, hyData.2, hzFirstData.2, hzData.2⟩

/-- A compatibility-ready address absent from the final support was deleted by one of the two
grouped compatibility isolations.  Deterministic filters cannot account for the loss because
their predicates are part of readiness. -/
theorem cwRecursiveApproximateCompatibilityReady_mem_yDeleted_or_zDeleted
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
    (address : CWRecursiveApproximateFineAddress depth n)
    (hready : address ∈ cwRecursiveApproximateCompatibilityReadySupport
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept)
    (hnotFinal : address ∉
      (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled
          coarseKept).finalSupport) :
    address ∈
        (cwRecursiveApproximateCleanupSupportData
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled
            coarseKept).yAmbient \
          (cwRecursiveApproximateCleanupSupportData
            K q partAt term hmultiplicity epsilon sigma alpha targets pooled
              coarseKept).ySupport ∨
      address ∈
        (cwRecursiveApproximateCleanupSupportData
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled
            coarseKept).zAmbient \
          (cwRecursiveApproximateCleanupSupportData
            K q partAt term hmultiplicity epsilon sigma alpha targets pooled
              coarseKept).zSupport := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun candidate : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma candidate) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun candidate : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma candidate) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun candidate : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma candidate) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  change address ∈ yFirst.support.filter (fun candidate ↦
    yKeep candidate ∧
      CWRecursivePooledAllLabelMatches
        partAt pooled.zAll (candidate (sigma .Z)) ∧
      zKeep candidate) at hready
  change address ∉ zUsefulSupport at hnotFinal
  change address ∈ yFirst.support \ ySupport ∨
    address ∈ zFirst.support \ zSupport
  have hreadyData := Finset.mem_filter.mp hready
  by_cases hy : address ∈ ySupport
  · have hyUseful : address ∈ yUsefulSupport := by
      change address ∈ groupStableSupport ySupport yKeep
      exact Finset.mem_filter.mpr ⟨hy, hreadyData.2.1⟩
    have hzFirst : address ∈ zFirst.support :=
      (mem_cwRecursivePooledZFirstZeroOut_support
        yUseful sigma partAt pooled.zAll address).mpr
          ⟨hyUseful, hreadyData.2.2.1⟩
    have hz : address ∉ zSupport := by
      intro hzSupport
      apply hnotFinal
      change address ∈ groupStableSupport zSupport zKeep
      exact Finset.mem_filter.mpr ⟨hzSupport, hreadyData.2.2.2⟩
    exact Or.inr (Finset.mem_sdiff.mpr ⟨hzFirst, hz⟩)
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨hreadyData.1, hy⟩)

/-- Compatibility-ready labels in one coarse fiber, transported to the reference quotient and
intersected with the admitted approximate-input target alphabet. -/
noncomputable def cwRecursiveApproximateMovedReadyParts
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset (CWRecursiveApproximateFineLabel depth n) := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  let ready := cwRecursiveApproximateCompatibilityReadySupport
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  exact
    cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets reference physicalLeg ∩
      (ready.filter fun address ↦
        cwRecursiveChildGroup depth n address = coarse).image
          (fun address ↦ relabeling.partEquiv physicalLeg (address physicalLeg))

/-- A canonical compatibility-ready source address for a label in the moved ready alphabet. -/
noncomputable def cwRecursiveApproximateReadyAddress
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg)
    (fine : CWRecursiveApproximateFineLabel depth n)
    (hfine : fine ∈ cwRecursiveApproximateMovedReadyParts
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
        reference coarse hsame physicalLeg) :
    CWRecursiveApproximateFineAddress depth n := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  let ready := cwRecursiveApproximateCompatibilityReadySupport
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  have himage : fine ∈
      (ready.filter fun address ↦
        cwRecursiveChildGroup depth n address = coarse).image
          (fun address ↦ relabeling.partEquiv physicalLeg (address physicalLeg)) :=
    (Finset.mem_inter.mp hfine).2
  exact Classical.choose (Finset.mem_image.mp himage)

/-- The chosen ready address lies in the named ready support, has the requested coarse group, and
transports to the requested fine label. -/
theorem cwRecursiveApproximateReadyAddress_spec
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg)
    (fine : CWRecursiveApproximateFineLabel depth n)
    (hfine : fine ∈ cwRecursiveApproximateMovedReadyParts
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
        reference coarse hsame physicalLeg) :
    let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
      partAt sigma reference coarse hsame
    let relabeling :=
      PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
        (cwChunkPartitionedTensor K q (depth + 1)) n tau
    let address := cwRecursiveApproximateReadyAddress
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
        reference coarse hsame physicalLeg fine hfine
    address ∈ cwRecursiveApproximateCompatibilityReadySupport
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept ∧
      cwRecursiveChildGroup depth n address = coarse ∧
        relabeling.partEquiv physicalLeg (address physicalLeg) = fine := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  let ready := cwRecursiveApproximateCompatibilityReadySupport
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  have himage : fine ∈
      (ready.filter fun address ↦
        cwRecursiveChildGroup depth n address = coarse).image
          (fun address ↦ relabeling.partEquiv physicalLeg (address physicalLeg)) :=
    (Finset.mem_inter.mp hfine).2
  have hchosen := Classical.choose_spec (Finset.mem_image.mp himage)
  have hdata := Finset.mem_filter.mp hchosen.1
  exact ⟨hdata.1, hdata.2, hchosen.2⟩

/-- A final moved label is ready whenever the final support is a subset of the named ready
support and the same label is known to lie in the approximate input target.  This is the exact
projection step used by the cleanup construction; it does not create a source address for a label
which was absent initially. -/
theorem cwRecursiveApproximateMovedCleanedFiberParts_subset_movedReady
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
    {finalSupport : Finset (CWRecursiveApproximateFineAddress depth n)}
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (hfinalReady : finalSupport ⊆
      cwRecursiveApproximateCompatibilityReadySupport
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept)
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg)
    (hfinalInput :
      cwRecursiveApproximateMovedCleanedFiberParts
          K q partAt term hmultiplicity epsilon sigma alpha G
            reference coarse hsame physicalLeg ⊆
        cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets reference physicalLeg) :
    cwRecursiveApproximateMovedCleanedFiberParts
        K q partAt term hmultiplicity epsilon sigma alpha G
          reference coarse hsame physicalLeg ⊆
      cwRecursiveApproximateMovedReadyParts
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
          reference coarse hsame physicalLeg := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  let ready := cwRecursiveApproximateCompatibilityReadySupport
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
  intro fine hfine
  apply Finset.mem_inter.mpr
  refine ⟨hfinalInput hfine, ?_⟩
  change fine ∈ relabelParts relabeling.partEquiv
      (G.fiberParts coarse) physicalLeg at hfine
  have hsource := (mem_relabelParts
    relabeling.partEquiv (G.fiberParts coarse) physicalLeg fine).mp hfine
  obtain ⟨address, haddress, haddressGroup, haddressLabel⟩ :=
    (G.mem_fiberParts_iff coarse physicalLeg
      ((relabeling.partEquiv physicalLeg).symm fine)).mp hsource
  apply Finset.mem_image.mpr
  refine ⟨address, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hfinalReady ?_, ?_⟩
    · simpa using haddress
    · exact (hgroup address).symm.trans haddressGroup
  · calc
      relabeling.partEquiv physicalLeg (address physicalLeg) =
          relabeling.partEquiv physicalLeg
            ((relabeling.partEquiv physicalLeg).symm fine) := by
        rw [haddressLabel]
      _ = fine := (relabeling.partEquiv physicalLeg).apply_symm_apply fine

/-- The canonical cleanup support discharges the final-ready premise, while the already-proved
target-box comparison discharges final-input membership. -/
theorem cwRecursiveApproximateMovedCleanedFiberParts_subset_movedReady_of_cleanup
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
    (hclosed : IsProjectionClosed
      (cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept)
      (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled
          coarseKept).finalSupport Finset.univ)
    (hExact : ∀ address ∈
        (cwRecursiveApproximateCleanupSupportData
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled
            coarseKept).finalSupport,
      ∀ logicalLeg,
        (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
          (logicalAddress sigma address) logicalLeg
          (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).withSupport
        (cwRecursiveApproximateCleanupSupportData
          K q partAt term hmultiplicity epsilon sigma alpha targets pooled
            coarseKept).finalSupport).LegGrouping
              (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hreference :
      reference ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hcoarse :
      coarse ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    cwRecursiveApproximateMovedCleanedFiberParts
        K q partAt term hmultiplicity epsilon sigma alpha G
          reference coarse hsame physicalLeg ⊆
      cwRecursiveApproximateMovedReadyParts
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
          reference coarse hsame physicalLeg := by
  apply cwRecursiveApproximateMovedCleanedFiberParts_subset_movedReady
    K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept G hgroup
      (cwRecursiveApproximateCleanupFinalSupport_subset_ready
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept)
      reference coarse hsame physicalLeg
  exact cwRecursiveApproximateMovedCleanedFiberParts_subset_inputTargetParts
    K q partAt term hmultiplicity epsilon sigma alpha targets coarseKept
      (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled
          coarseKept).finalSupport
      hclosed hExact G hgroup reference coarse hreference hcoarse hsame physicalLeg

/-! ## Containment in the selected fine ambient -/

/-- The literal `Y` cleanup ambient remains inside the fine support over `coarseKept`. -/
theorem cwRecursiveApproximateCleanup_yAmbient_subset_fineAmbient
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
    (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept).yAmbient ⊆
      cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  change yFirst.support ⊆ fineAmbient
  intro address haddress
  have hxUseful : address ∈ xUseful.support :=
    (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hxSupport : address ∈ xSupport := by
    simpa only [xUseful, PartitionedTensor.withSupport_support] using hxUseful
  have hhashed : address ∈ hashed.support :=
    groupStableSupport_subset hashed.support xKeep hxSupport
  simpa only [hashed, PartitionedTensor.withSupport_support] using hhashed

/-- The later `Z` cleanup ambient also remains inside the same fine support. -/
theorem cwRecursiveApproximateCleanup_zAmbient_subset_fineAmbient
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
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
    (cwRecursiveApproximateCleanupSupportData
        K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept).zAmbient ⊆
      cwRecursiveFineSupportOverCoarseSupport
        (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support coarseKept := by
  classical
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ CWRecursiveApproximateFineLabel depth n) sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : CWRecursiveApproximateFineAddress depth n ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  change zFirst.support ⊆ fineAmbient
  intro address haddress
  have hyUseful : address ∈ yUseful.support :=
    (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hyUsefulSupport : address ∈ yUsefulSupport := by
    simpa only [yUseful, PartitionedTensor.withSupport_support] using hyUseful
  have hySupport : address ∈ ySupport :=
    groupStableSupport_subset yIsolated.support yKeep hyUsefulSupport
  have hyFirst : address ∈ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY hySupport
  have hxUseful : address ∈ xUseful.support :=
    (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirst |>.1
  have hxSupport : address ∈ xSupport := by
    simpa only [xUseful, PartitionedTensor.withSupport_support] using hxUseful
  have hhashed : address ∈ hashed.support :=
    groupStableSupport_subset hashed.support xKeep hxSupport
  simpa only [hashed, PartitionedTensor.withSupport_support] using hhashed

/-- Admitted one-leg target labels for which no compatibility-ready address has been exhibited. -/
noncomputable def cwRecursiveApproximateSourceNonrealizableHoles
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
    (reference coarse : CWRecursiveCoarseAddress depth n)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset (CWRecursiveApproximateFineLabel depth n) :=
  cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg \
    cwRecursiveApproximateMovedReadyParts
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled coarseKept
        reference coarse hsame physicalLeg


end AlgebraicComplexity.Examples
