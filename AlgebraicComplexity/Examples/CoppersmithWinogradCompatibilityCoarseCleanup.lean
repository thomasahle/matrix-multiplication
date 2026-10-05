/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanup
import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing

/-!
# Compatibility cleanup inside coarse CW hashing fibers

This module connects the coarse hashing support to the fine complete-split cleanup.  Fine block
labels are required to determine a unique retained coarse address, but are not required to
determine a unique fine monomial.  The latter, stronger condition is not used by the paper.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Coarse address containing a fine exact-interface address. -/
def cwExactInterfaceCoarseGroup (depth n : ℕ) :
    BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) →
      BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) :=
  coarsenBlockAddress (cwExactInterfaceCoarsening depth n)

@[simp] theorem cwExactInterfaceCoarseGroup_apply (depth n : ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) (c : Leg) :
    cwExactInterfaceCoarseGroup depth n address c =
      cwOuterCoarseWord depth n (address c) :=
  rfl

/-- Fine support lying over a retained family of coarse addresses. -/
noncomputable def cwFineSupportOverCoarseSupport {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (coarse : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))) :
    Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  classical
  exact fine.filter fun address ↦ cwExactInterfaceCoarseGroup depth n address ∈ coarse

@[simp] theorem mem_cwFineSupportOverCoarseSupport {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (coarse : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    address ∈ cwFineSupportOverCoarseSupport fine coarse ↔
      address ∈ fine ∧ cwExactInterfaceCoarseGroup depth n address ∈ coarse := by
  classical
  simp [cwFineSupportOverCoarseSupport]

/-- Coarse injectivity on one leg means every fine label over the retained coarse family
determines its coarse address on that leg. -/
theorem cwFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
    {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (coarse : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))) (pivot : Leg)
    (hinjective : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (CWCoarseDigit depth) n) ↦ address pivot) coarse) :
    HasGroupUniqueLegFibers
      (cwFineSupportOverCoarseSupport fine coarse)
      (cwFineSupportOverCoarseSupport fine coarse)
      (cwExactInterfaceCoarseGroup depth n) pivot := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro selected hselected other hother hlabel
  have hselectedCoarse :=
    (mem_cwFineSupportOverCoarseSupport fine coarse selected).mp hselected |>.2
  have hotherCoarse :=
    (mem_cwFineSupportOverCoarseSupport fine coarse other).mp hother |>.2
  apply hinjective hotherCoarse hselectedCoarse
  change cwOuterCoarseWord depth n (other pivot) =
    cwOuterCoarseWord depth n (selected pivot)
  rw [hlabel]

/-- The logical model's coarse coordinate is exactly the corresponding physical coarse-group
digit after applying the region orientation. -/
theorem cwExactInterfaceCompatibilityModel_coarse_get_eq_group
    {Part : Type v} {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (sample : Fin (n + 1)) (logicalLeg : Leg) :
    ((cwExactInterfaceCompatibilityModel depth n partAt).coarse
      (logicalAddress sigma address) sample).get logicalLeg =
      (positiveWordEquiv (CWCoarseDigit depth) n
        (cwExactInterfaceCoarseGroup depth n address (sigma logicalLeg)) sample : ℕ) := by
  cases logicalLeg <;>
    simp [cwExactInterfaceCompatibilityModel, encodedPositiveWordCompatibilityModel,
      CoarseIndex.get, cwExactInterfaceCoarseGroup, cwExactInterfaceCoarsening,
      cwOuterCoarseWord, positiveWordEquiv_map, Function.comp_apply]

/-- The logical model's fine chunk on one leg depends only on the corresponding physical fine
label. -/
theorem cwExactInterfaceCompatibilityModel_chunks_logicalAddress
    {Part : Type v} {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (sample : Fin (n + 1)) (logicalLeg : Leg) :
    (cwExactInterfaceCompatibilityModel depth n partAt).chunks logicalLeg
        (logicalAddress sigma address logicalLeg) sample =
      cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (address (sigma logicalLeg)) sample) :=
  rfl

/-- Extensionality of a tagged coarse index through its part and three leg projections. -/
theorem coarseIndex_eq_of_part_eq_of_get_eq {Part : Type v}
    {left right : CoarseIndex Part} (hpart : left.part = right.part)
    (hget : ∀ c, left.get c = right.get c) : left = right := by
  cases left with
  | mk leftPart leftX leftY leftZ =>
      cases right with
      | mk rightPart rightX rightY rightZ =>
          have hx := hget .X
          have hy := hget .Y
          have hz := hget .Z
          simp only [CoarseIndex.get] at hx hy hz
          simp_all

/-- Exact usefulness is stable among fine addresses with the same physical label and the same
coarse constituent.  Therefore it can be imposed by an honest variable zero-out after grouped
compatibility isolation. -/
theorem cwMatchesExact_isGroupLabelStable
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ) :
    IsGroupLabelStable ambient (cwExactInterfaceCoarseGroup depth n)
      (sigma logicalLeg)
      (fun address ↦
        (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
          (logicalAddress sigma address) logicalLeg profile) := by
  intro left _hleft right _hright hlabel hgroup
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  have hcoarse : model.coarse (logicalAddress sigma left) =
      model.coarse (logicalAddress sigma right) := by
    funext sample
    apply coarseIndex_eq_of_part_eq_of_get_eq
    · rfl
    · intro c
      change
        ((cwExactInterfaceCompatibilityModel depth n partAt).coarse
          (logicalAddress sigma left) sample).get c =
        ((cwExactInterfaceCompatibilityModel depth n partAt).coarse
          (logicalAddress sigma right) sample).get c
      rw [cwExactInterfaceCompatibilityModel_coarse_get_eq_group,
        cwExactInterfaceCompatibilityModel_coarse_get_eq_group]
      exact congrArg
        (fun coarse ↦
          (positiveWordEquiv (CWCoarseDigit depth) n (coarse (sigma c)) sample : ℕ))
        hgroup
  have hchunks : model.chunks logicalLeg
      (logicalAddress sigma left logicalLeg) =
      model.chunks logicalLeg (logicalAddress sigma right logicalLeg) := by
    funext sample
    change cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (left (sigma logicalLeg)) sample) =
      cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (right (sigma logicalLeg)) sample)
    rw [hlabel]
  unfold CompatibilityModel.MatchesExact
  constructor <;> intro h q word
  · rw [← hcoarse, ← hchunks]
    exact h q word
  · rw [hcoarse, hchunks]
    exact h q word

/-! ## Complete grouped CW cleanup -/

/-- Paper-faithful compatibility and usefulness cleanup over an already hash-isolated coarse
support.  The result is an indexed direct sum over coarse addresses; each summand is the whole
surviving fine fiber over that address.

The only hashing input is injectivity of the retained coarse addresses on physical `sigma X`.
No injectivity of fine addresses is assumed. -/
theorem cwSelectedExactInterfaceTerm_orientedGroupedCleanup_withCoarseGroup
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X)) coarseKept) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let group := cwExactInterfaceCoarseGroup depth n
    let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
    let hashed := selected.withSupport fineAmbient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support group (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support group (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      (∀ address, G.group address = cwExactInterfaceCoarseGroup depth n address) ∧
        Restricts hashed.realize
          (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let group := cwExactInterfaceCoarseGroup depth n
  let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
  let hashed := selected.withSupport fineAmbient
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let xKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  let zUseful := zIsolated.withSupport zUsefulSupport

  have hXHashed : HasGroupUniqueLegFibers hashed.support hashed.support
      group (sigma .X) := by
    simpa [hashed, fineAmbient, group] using
      cwFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
        selected.support coarseKept (sigma .X) hcoarseX
  have hxSubset : xSupport ⊆ hashed.support :=
    groupStableSupport_subset hashed.support xKeep
  have hXYFirstSubset : yFirst.support ⊆ xSupport := by
    intro address haddress
    exact (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hYSubset : ySupport ⊆ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY
  have hYUsefulSubset : yUsefulSupport ⊆ ySupport := by
    change groupStableSupport ySupport yKeep ⊆ ySupport
    exact groupStableSupport_subset ySupport yKeep
  have hZFirstSubset : zFirst.support ⊆ yUsefulSupport := by
    intro address haddress
    exact (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hZSubset : zSupport ⊆ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ
  have hZUsefulSubset : zUsefulSupport ⊆ zSupport := by
    change groupStableSupport zSupport zKeep ⊆ zSupport
    exact groupStableSupport_subset zSupport zKeep

  have hYFirstSubsetSelected : yFirst.support ⊆ selected.support := by
    intro address haddress
    have hx := hXYFirstSubset haddress
    have hhash := hxSubset hx
    exact (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept address).mp hhash |>.1
  have hYProfiles : ∀ address ∈ yFirst.support,
      CWPooledAllYProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hfirst.1
    refine ⟨hxData.2, ?_⟩
    exact (cw_matchesYPooledAll_iff_labelMatches
      sigma partAt pooled.yAll address).mpr hfirst.2
  have hSoundY : IsCompatibilitySound yFirst.support (sigma .Y) compatibleY := by
    exact cwSelectedExactInterfaceTerm_orientedYCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled yFirst.support
        hYFirstSubsetSelected hYProfiles
  have hYGroup : HasGroupUniqueLegFibers yFirst.support ySupport
      group (sigma .Y) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hYGroupSelf : HasGroupUniqueLegFibers ySupport ySupport
      group (sigma .Y) := hYGroup.toSelf

  have hZFirstSubsetSelected : zFirst.support ⊆ selected.support := by
    intro address haddress
    exact hYFirstSubsetSelected
      (hYSubset (hYUsefulSubset (hZFirstSubset haddress)))
  have hZProfiles : ∀ address ∈ zFirst.support,
      CWPooledAllZProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress
    have hyData : address ∈ ySupport ∧ yKeep address := by
      simpa [yUseful, yUsefulSupport, yIsolated, groupStableSupport] using hfirst.1
    have hyFirstMem := hYSubset hyData.1
    have hyFirstData := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hyFirstData.1
    refine ⟨hxData.2, hyData.2, ?_⟩
    exact (cw_matchesZPooledAll_iff_labelMatches
      sigma partAt pooled.zAll address).mpr hfirst.2
  have hSoundZ : IsCompatibilitySound zFirst.support (sigma .Z) compatibleZ := by
    exact cwSelectedExactInterfaceTerm_orientedZCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled zFirst.support
        hZFirstSubsetSelected hZProfiles
  have hZGroup : HasGroupUniqueLegFibers zFirst.support zSupport
      group (sigma .Z) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hZGroupSelf : HasGroupUniqueLegFibers zSupport zSupport
      group (sigma .Z) := hZGroup.toSelf

  have hxRestrict : Restricts hashed.realize xUseful.realize := by
    simpa [xUseful, xSupport, xKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter hashed group (sigma .X) xKeep
        hXHashed (cwMatchesExact_isGroupLabelStable
          partAt sigma hashed.support .X targets.xExact)
  have hyFirstRestrict : Restricts xUseful.realize yFirst.realize :=
    cwPooledYFirstZeroOut_restricts xUseful sigma partAt pooled.yAll
  have hyCompatibilityRestrict : Restricts yFirst.realize yIsolated.realize := by
    simpa [yIsolated, ySupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        yFirst group (sigma .Y) compatibleY hSoundY
  have hyUsefulRestrict : Restricts yIsolated.realize yUseful.realize := by
    simpa [yUseful, yUsefulSupport, yKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter yIsolated group (sigma .Y) yKeep
        (by simpa [yIsolated] using hYGroupSelf)
        (cwMatchesExact_isGroupLabelStable
          partAt sigma yIsolated.support .Y targets.yExact)
  have hzFirstRestrict : Restricts yUseful.realize zFirst.realize :=
    cwPooledZFirstZeroOut_restricts yUseful sigma partAt pooled.zAll
  have hzCompatibilityRestrict : Restricts zFirst.realize zIsolated.realize := by
    simpa [zIsolated, zSupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        zFirst group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulRestrict : Restricts zIsolated.realize zUseful.realize := by
    simpa [zUseful, zUsefulSupport, zKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter zIsolated group (sigma .Z) zKeep
        (by simpa [zIsolated] using hZGroupSelf)
        (cwMatchesExact_isGroupLabelStable
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
  let zeroWord : PositiveWord (CWCoarseDigit depth) n :=
    (positiveWordEquiv (CWCoarseDigit depth) n).symm (fun _ ↦ 0)
  let fallback : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) :=
    fun _c ↦ zeroWord
  let G : zUseful.LegGrouping
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :=
    PartitionedTensor.LegGrouping.ofGroupUnique zUseful group fallback hfinal
  refine ⟨G, (fun _address ↦ rfl), hxRestrict.trans (hyFirstRestrict.trans
    (hyCompatibilityRestrict.trans (hyUsefulRestrict.trans
      (hzFirstRestrict.trans (hzCompatibilityRestrict.trans
        (hzUsefulRestrict.trans ?_))))))⟩
  exact G.restricts_groupedIndexedDirectSum

/-- Compatibility-preserving wrapper which keeps the original direct-sum-only API. -/
theorem cwSelectedExactInterfaceTerm_orientedGroupedCleanup_to_groupedIndexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X)) coarseKept) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let group := cwExactInterfaceCoarseGroup depth n
    let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
    let hashed := selected.withSupport fineAmbient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support group (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support group (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      Restricts hashed.realize
        (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  obtain ⟨G, _hgroup, hrestrict⟩ :=
    cwSelectedExactInterfaceTerm_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity sigma targets pooled coarseKept hcoarseX
  exact ⟨G, hrestrict⟩

end AlgebraicComplexity.Examples
