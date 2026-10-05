/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateHashExtraction

/-!
# Compatibility cleanup on an approximate recursive CW input

Compatibility soundness uses native CW fine legality, coarse-weight correctness, and the profile
predicates installed by the preceding zero-outs.  It does not use equality with one exact parent
empirical type.  This module makes that dependency boundary explicit and runs the complete grouped
X/Y/Z cleanup inside the fine preimages retained by relaxed marked hashing.

The output contains every present cleaned fine fiber.  Comparison with the independently assembled
full child product, and bounds on its input-profile and compatibility holes, remain downstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## Compatibility soundness from approximate parent support -/

/-- The profile equations before logical-Y isolation, together with approximate-input support,
supply the full generic pooled-all invariant. -/
theorem cwRecursiveApproximate_passesYPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support)
    (hprofiles : CWRecursivePooledAllYProfileMatches
      sigma partAt targets pooled address) :
    (cwRecursiveChildCompatibilityModel depth n partAt).PassesYPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hYAll⟩
  exact
    ⟨cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_approximateSelected_support
        K q partAt term hmultiplicity epsilon sigma address haddress,
      cwRecursiveChildCompatibilityModel_hasCoarseWeights
        depth n partAt (logicalAddress sigma address), hX, hYAll⟩

/-- Logical-Z analogue of `cwRecursiveApproximate_passesYPooledAllZeroOut`. -/
theorem cwRecursiveApproximate_passesZPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support)
    (hprofiles : CWRecursivePooledAllZProfileMatches
      sigma partAt targets pooled address) :
    (cwRecursiveChildCompatibilityModel depth n partAt).PassesZPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hY, hZAll⟩
  exact
    ⟨cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_approximateSelected_support
        K q partAt term hmultiplicity epsilon sigma address haddress,
      cwRecursiveChildCompatibilityModel_hasCoarseWeights
        depth n partAt (logicalAddress sigma address), hX, hY, hZAll⟩

/-- Arbitrary-orientation Y-compatibility soundness on any subfamily of the approximate parent
support satisfying the two preceding profile equations. -/
theorem cwRecursiveApproximate_orientedYCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support)
    (hprofiles : ∀ address ∈ ambient,
      CWRecursivePooledAllYProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Y)
      (OrientedCompatibleY
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedYCompatibility_sound
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesYFirstZeroOut_of_pooledAll
  exact cwRecursiveApproximate_passesYPooledAllZeroOut
    K q partAt term hmultiplicity epsilon sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-- Arbitrary-orientation Z-compatibility soundness on approximate parent support. -/
theorem cwRecursiveApproximate_orientedZCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support)
    (hprofiles : ∀ address ∈ ambient,
      CWRecursivePooledAllZProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Z)
      (OrientedCompatibleZ
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedZCompatibility_sound
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesZFirstZeroOut_of_pooledAll
  exact cwRecursiveApproximate_passesZPooledAllZeroOut
    K q partAt term hmultiplicity epsilon sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-! ## Complete grouped cleanup -/

/-- Paper-faithful compatibility and usefulness cleanup in the present fine preimages of an
approximately selected parent.  Every restriction is constructed internally. -/
theorem cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X)) coarseKept) :
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
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
          Restricts hashed.realize
            (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let parentApprox := cwSelectedApproximateInterfaceTerm K q
    (cwRecursiveSemanticParentTerm term hmultiplicity)
    (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon
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

  have hXHashed : HasGroupUniqueLegFibers hashed.support hashed.support
      group (sigma .X) := by
    simpa [hashed, fineAmbient, group] using
      cwRecursiveFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
        alphaSelected.support coarseKept (sigma .X) hcoarseX
  have hxSubset : xSupport ⊆ hashed.support :=
    groupStableSupport_subset hashed.support xKeep
  have hXYFirstSubset : yFirst.support ⊆ xSupport := by
    intro address haddress
    exact (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hYSubset : ySupport ⊆ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY
  have hYUsefulSubset : yUsefulSupport ⊆ ySupport := by
    change groupStableSupport ySupport yKeep ⊆ ySupport
    exact groupStableSupport_subset ySupport yKeep
  have hZFirstSubset : zFirst.support ⊆ yUsefulSupport := by
    intro address haddress
    exact (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hZSubset : zSupport ⊆ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ
  have hZUsefulSubset : zUsefulSupport ⊆ zSupport := by
    change groupStableSupport zSupport zKeep ⊆ zSupport
    exact groupStableSupport_subset zSupport zKeep

  have hAlphaSelectedSubsetParent : alphaSelected.support ⊆ parentApprox.support := by
    intro address haddress
    exact (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha address).mp haddress |>.1
  have hYFirstSubsetParent : yFirst.support ⊆ parentApprox.support := by
    intro address haddress
    have hx := hXYFirstSubset haddress
    have hhash := hxSubset hx
    have halpha := (mem_cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept address).mp hhash |>.1
    exact hAlphaSelectedSubsetParent halpha
  have hYProfiles : ∀ address ∈ yFirst.support,
      CWRecursivePooledAllYProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hfirst.1
    refine ⟨hxData.2, ?_⟩
    exact (cwRecursive_matchesYPooledAll_iff_labelMatches
      sigma partAt pooled.yAll address).mpr hfirst.2
  have hSoundY : IsCompatibilitySound yFirst.support (sigma .Y) compatibleY := by
    exact cwRecursiveApproximate_orientedYCompatibility_sound
      K q partAt term hmultiplicity epsilon sigma targets pooled yFirst.support
        hYFirstSubsetParent hYProfiles
  have hYGroup : HasGroupUniqueLegFibers yFirst.support ySupport
      group (sigma .Y) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hYGroupSelf : HasGroupUniqueLegFibers ySupport ySupport
      group (sigma .Y) := hYGroup.toSelf

  have hZFirstSubsetParent : zFirst.support ⊆ parentApprox.support := by
    intro address haddress
    exact hYFirstSubsetParent
      (hYSubset (hYUsefulSubset (hZFirstSubset haddress)))
  have hZProfiles : ∀ address ∈ zFirst.support,
      CWRecursivePooledAllZProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress
    have hyData : address ∈ ySupport ∧ yKeep address := by
      simpa [yUseful, yUsefulSupport, yIsolated, groupStableSupport] using hfirst.1
    have hyFirstMem := hYSubset hyData.1
    have hyFirstData := (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hyFirstData.1
    refine ⟨hxData.2, hyData.2, ?_⟩
    exact (cwRecursive_matchesZPooledAll_iff_labelMatches
      sigma partAt pooled.zAll address).mpr hfirst.2
  have hSoundZ : IsCompatibilitySound zFirst.support (sigma .Z) compatibleZ := by
    exact cwRecursiveApproximate_orientedZCompatibility_sound
      K q partAt term hmultiplicity epsilon sigma targets pooled zFirst.support
        hZFirstSubsetParent hZProfiles
  have hZGroup : HasGroupUniqueLegFibers zFirst.support zSupport
      group (sigma .Z) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hZGroupSelf : HasGroupUniqueLegFibers zSupport zSupport
      group (sigma .Z) := hZGroup.toSelf

  have hxRestrict : Restricts hashed.realize xUseful.realize := by
    simpa [xUseful, xSupport, xKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter hashed group (sigma .X) xKeep
        hXHashed (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma hashed.support .X targets.xExact)
  have hyFirstRestrict : Restricts xUseful.realize yFirst.realize :=
    cwRecursivePooledYFirstZeroOut_restricts xUseful sigma partAt pooled.yAll
  have hyCompatibilityRestrict : Restricts yFirst.realize yIsolated.realize := by
    simpa [yIsolated, ySupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        yFirst group (sigma .Y) compatibleY hSoundY
  have hyUsefulRestrict : Restricts yIsolated.realize yUseful.realize := by
    simpa [yUseful, yUsefulSupport, yKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter yIsolated group (sigma .Y) yKeep
        (by simpa [yIsolated] using hYGroupSelf)
        (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma yIsolated.support .Y targets.yExact)
  have hzFirstRestrict : Restricts yUseful.realize zFirst.realize :=
    cwRecursivePooledZFirstZeroOut_restricts yUseful sigma partAt pooled.zAll
  have hzCompatibilityRestrict : Restricts zFirst.realize zIsolated.realize := by
    simpa [zIsolated, zSupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        zFirst group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulRestrict : Restricts zIsolated.realize zUseful.realize := by
    simpa [zUseful, zUsefulSupport, zKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter zIsolated group (sigma .Z) zKeep
        (by simpa [zIsolated] using hZGroupSelf)
        (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma zIsolated.support .Z targets.zExact)

  have hXFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .X) := by
    have hXAtX := hXHashed.restrictToSubset hxSubset
    have hXAtYFirst := hXAtX.restrictToSubset hXYFirstSubset
    have hXAtY := hXAtYFirst.restrictToSubset hYSubset
    have hXAtYUseful := hXAtY.restrictToSubset hYUsefulSubset
    have hXAtZFirst := hXAtYUseful.restrictToSubset hZFirstSubset
    have hXAtZ := hXAtZFirst.restrictToSubset hZSubset
    exact (hXAtZ.restrictToSubset hZUsefulSubset).toSelf
  have hYFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .Y) := by
    have hYAtUseful := hYGroup.restrictToSubset hYUsefulSubset
    have hYAtZFirst := hYAtUseful.restrictToSubset hZFirstSubset
    have hYAtZ := hYAtZFirst.restrictToSubset hZSubset
    exact (hYAtZ.restrictToSubset hZUsefulSubset).toSelf
  have hZFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .Z) := (hZGroup.restrictToSubset hZUsefulSubset).toSelf
  have hfinal : ∀ pivot,
      HasGroupUniqueLegFibers zUseful.support zUseful.support group pivot := by
    intro pivot
    have hpivot : sigma (sigma.symm pivot) = pivot := sigma.apply_symm_apply pivot
    generalize hlogical : sigma.symm pivot = logical at hpivot
    cases logical with
    | X =>
        have : sigma .X = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hXFinal
    | Y =>
        have : sigma .Y = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hYFinal
    | Z =>
        have : sigma .Z = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hZFinal
  let zeroWord : Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth :=
    fun _ ↦ 0
  let fallback : CWRecursiveCoarseAddress depth n := fun _c ↦ zeroWord
  let G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n) :=
    PartitionedTensor.LegGrouping.ofGroupUnique zUseful group fallback hfinal
  have hxClosed : IsProjectionClosed hashed.support xSupport {sigma .X} := by
    exact groupStableSupport_isProjectionClosed hashed.support group (sigma .X) xKeep
      hXHashed (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma hashed.support .X targets.xExact)
  have hyFirstClosed : IsProjectionClosed xUseful.support yFirst.support Finset.univ := by
    simpa [yFirst, cwRecursivePooledYFirstZeroOut] using
      PartitionedTensor.select_support_isProjectionClosed_univ xUseful
        (fun c label ↦ c ≠ sigma .Y ∨
          CWRecursivePooledAllLabelMatches partAt pooled.yAll label)
  have hyCompatibilityClosed : IsProjectionClosed yFirst.support ySupport {sigma .Y} :=
    groupCompatibilityIsolatedSupport_isProjectionClosed
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hyUsefulClosed : IsProjectionClosed yIsolated.support yUsefulSupport {sigma .Y} := by
    exact groupStableSupport_isProjectionClosed yIsolated.support group (sigma .Y) yKeep
      (by simpa [yIsolated] using hYGroupSelf)
      (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma yIsolated.support .Y targets.yExact)
  have hzFirstClosed : IsProjectionClosed yUseful.support zFirst.support Finset.univ := by
    simpa [zFirst, cwRecursivePooledZFirstZeroOut] using
      PartitionedTensor.select_support_isProjectionClosed_univ yUseful
        (fun c label ↦ c ≠ sigma .Z ∨
          CWRecursivePooledAllLabelMatches partAt pooled.zAll label)
  have hzCompatibilityClosed : IsProjectionClosed zFirst.support zSupport {sigma .Z} :=
    groupCompatibilityIsolatedSupport_isProjectionClosed
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulClosed : IsProjectionClosed zIsolated.support zUsefulSupport {sigma .Z} := by
    exact groupStableSupport_isProjectionClosed zIsolated.support group (sigma .Z) zKeep
      (by simpa [zIsolated] using hZGroupSelf)
      (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma zIsolated.support .Z targets.zExact)
  have hclosed : IsProjectionClosed hashed.support zUsefulSupport Finset.univ := by
    have hchain := (((((hxClosed.trans_union hyFirstClosed).trans_union
      hyCompatibilityClosed).trans_union hyUsefulClosed).trans_union
      hzFirstClosed).trans_union hzCompatibilityClosed).trans_union hzUsefulClosed
    simpa using hchain
  refine ⟨G, (fun _address ↦ rfl), hclosed,
    hxRestrict.trans (hyFirstRestrict.trans
      (hyCompatibilityRestrict.trans (hyUsefulRestrict.trans
        (hzFirstRestrict.trans (hzCompatibilityRestrict.trans
          (hzUsefulRestrict.trans ?_))))))⟩
  exact G.restricts_groupedIndexedDirectSum

/-- Every address in the final approximate-cleanup support realizes all three prescribed exact
profiles.  This is the public invariant needed by target-box clients; it is derived from the
three stable profile filters rather than accepted as a client hypothesis. -/
theorem cwRecursiveApproximate_orientedGroupedCleanup_finalMatchesExact
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :
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
    ∀ address ∈ zUsefulSupport, ∀ logicalLeg,
      model.MatchesExact (logicalAddress sigma address) logicalLeg
        (match logicalLeg with
          | .X => targets.xExact
          | .Y => targets.yExact
          | .Z => targets.zExact) := by
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
  change ∀ address ∈ zUsefulSupport, ∀ logicalLeg,
    model.MatchesExact (logicalAddress sigma address) logicalLeg
      (match logicalLeg with
        | .X => targets.xExact
        | .Y => targets.yExact
        | .Z => targets.zExact)
  intro address haddress logicalLeg
  have hzData : address ∈ zSupport ∧ zKeep address := by
    simpa [zUsefulSupport, zIsolated, groupStableSupport] using haddress
  have hzFirst : address ∈ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ hzData.1
  have hyUseful : address ∈ yUsefulSupport :=
    (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp hzFirst |>.1
  have hyData : address ∈ ySupport ∧ yKeep address := by
    simpa [yUsefulSupport, yIsolated, groupStableSupport] using hyUseful
  have hyFirst : address ∈ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY hyData.1
  have hxUseful : address ∈ xSupport :=
    (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirst |>.1
  have hxData : address ∈ hashed.support ∧ xKeep address := by
    simpa [xSupport, groupStableSupport] using hxUseful
  cases logicalLeg with
  | X => simpa [model, xKeep] using hxData.2
  | Y => simpa [model, yKeep] using hyData.2
  | Z => simpa [model, zKeep] using hzData.2

/-! ## Composition with relaxed marked hashing -/

/-- One relaxed marked X-only hash pass followed by the complete approximate-input grouped
compatibility cleanup.  The result starts at the approximate parent selector and constructs every
intermediate restriction internally. -/
theorem cwRecursiveApproximate_orientedMarkedXHashAndGroupedCleanup
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let parentApprox := cwSelectedApproximateInterfaceTerm K q
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon
    let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha
    let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
      term sigma alpha B seed
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
      yFirst.support (cwRecursiveChildGroup depth n) (sigma .Y) compatibleY
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
      zFirst.support (cwRecursiveChildGroup depth n) (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
          Restricts parentApprox.realize
            (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let parentApprox := cwSelectedApproximateInterfaceTerm K q
    (cwRecursiveSemanticParentTerm term hmultiplicity)
    (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon
  let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
    term sigma alpha B seed
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  have hMarginal : Restricts parentApprox.realize alphaSelected.realize := by
    simpa [parentApprox, alphaSelected] using
      cwSelectedApproximateInterfaceTerm_restricts_recursiveAlphaMarginals
        K q term hmultiplicity epsilon sigma alpha
  have hHash : Restricts alphaSelected.realize hashed.realize := by
    simpa [alphaSelected, coarseKept, fineAmbient, hashed] using
      cwRecursiveApproximateAlphaMarginalSelectedTerm_restricts_relaxedIsolatedFine
        encoding K q term hmultiplicity epsilon sigma alpha B hB seed
  have hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
      (coarseKept : Set _) := by
    simpa [coarseKept] using
      encoding.relaxedRecursiveX_injectiveOn_markedXIsolatedCoarseSupport
        term sigma alpha B seed
  obtain ⟨G, hgroup, hclosed, hcleanup⟩ :=
    cwRecursiveApproximate_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity epsilon sigma alpha targets pooled
        coarseKept hcoarseX
  exact ⟨G, hgroup, hclosed, hMarginal.trans (hHash.trans hcleanup)⟩

/-- Complete finite existence theorem for relaxed marked hashing followed by approximate-input
compatibility cleanup.  The exact count is for intended quotient targets; the grouped tensor
contains their present cleaned fine preimages. -/
theorem exists_seed_many_recursiveApproximateMarkedXHashAndGroupedCleanup
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ encoding.relaxedRecursiveMarkedTargets
        term sigma alpha,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha) triple).card ≤
          Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))),
      3 * Nat.multinomial Finset.univ alpha.count * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
            term sigma alpha B seed).card ∧
      let parentApprox := cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon
      let alphaSelected := cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha
      let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
        term sigma alpha B seed
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
        yFirst.support (cwRecursiveChildGroup depth n) (sigma .Y) compatibleY
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
        zFirst.support (cwRecursiveChildGroup depth n) (sigma .Z) compatibleZ
      let zIsolated := zFirst.withSupport zSupport
      let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
        model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
      let zUseful := zIsolated.withSupport zUsefulSupport
      ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
        (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
          IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
            Restricts parentApprox.realize
              (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  obtain ⟨seed, hcount, _hmarked, _hinjective⟩ :=
    encoding.exists_seed_many_relaxedRecursiveMarkedXIsolatedCoarseSupport
      term sigma alpha B hquarter
  refine ⟨seed, hcount, ?_⟩
  exact cwRecursiveApproximate_orientedMarkedXHashAndGroupedCleanup
    encoding K q partAt term hmultiplicity epsilon sigma alpha
      targets pooled B hB seed

end AlgebraicComplexity.Examples
