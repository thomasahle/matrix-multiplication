/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanup

/-!
# Finite compatibility-and-usefulness cleanup for CW interface terms

This module packages the complete one-letter cleanup pipeline used after hashing an oriented
Coppersmith--Winograd interface term.  Successive support restrictions impose the exact and pooled
profiles required on the three physical legs; compatibility isolation then makes the surviving
leg labels injective.  The main theorem converts those finite survivors into a genuine indexed
direct sum.  No asymptotic estimate or numerical certificate is assumed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Addresses selected from unique ambient fibers have pairwise distinct labels on the pivot
leg.  This turns compatibility isolation into the injectivity needed by a later usefulness
zero-out. -/
theorem hasUniqueLegFibers_injOn_selected
    {A : Leg → Type v} {ambient selected : Finset (BlockAddress A)} {pivot : Leg}
    (hunique : HasUniqueLegFibers ambient selected pivot) :
    Set.InjOn (fun address : BlockAddress A ↦ address pivot) selected := by
  intro left hleft right hright hlabel
  exact hunique.2 right hright left (hunique.1 hleft) hlabel

/-- The complete finite one-letter cleanup after hashing for one oriented selected CW term.

The only support-level input is an ambient subfamily isolated on physical `sigma X`.  The
successive variable zero-outs themselves enforce exact `X`, pooled-all `Y`, exact useful `Y`,
pooled-all `Z`, and exact useful `Z` profiles.  Compatibility isolation supplies injectivity on
physical `sigma Y` and `sigma Z`.  Consequently the survivors form a genuine indexed direct sum.
-/
theorem cwSelectedExactInterfaceTerm_orientedCompatibilityAndUsefulnessCleanup_to_indexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .X))
      ambient) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let hashed := selected.withSupport ambient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xUseful := hashed.withSupport
      (cwExactProfileSupport sigma model hashed.support .X targets.xExact)
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := compatibilityIsolatedSupport yFirst.support (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUseful := yIsolated.withSupport
      (cwExactProfileSupport sigma model yIsolated.support .Y targets.yExact)
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := compatibilityIsolatedSupport zFirst.support (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUseful := zIsolated.withSupport
      (cwExactProfileSupport sigma model zIsolated.support .Z targets.zExact)
    Restricts hashed.realize
      (indexedDirectSum
        (fun address : zUseful.support ↦ zUseful.constituent address.1)) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let hashed := selected.withSupport ambient
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let xUseful := hashed.withSupport
    (cwExactProfileSupport sigma model hashed.support .X targets.xExact)
  let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let ySupport := compatibilityIsolatedSupport yFirst.support (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yUseful := yIsolated.withSupport
    (cwExactProfileSupport sigma model yIsolated.support .Y targets.yExact)
  let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let zSupport := compatibilityIsolatedSupport zFirst.support (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zUseful := zIsolated.withSupport
    (cwExactProfileSupport sigma model zIsolated.support .Z targets.zExact)

  have hHashedSubset : hashed.support ⊆ selected.support := by
    simpa [hashed, selected] using hambient
  have hXHashed : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .X)) hashed.support := by
    simpa [hashed] using hX
  have hXUsefulSubset : xUseful.support ⊆ hashed.support := by
    simpa [xUseful] using
      cwExactProfileSupport_subset sigma model hashed.support .X targets.xExact
  have hYFirstSubset : yFirst.support ⊆ xUseful.support := by
    intro address haddress
    exact (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hYSupportSubset : ySupport ⊆ yFirst.support :=
    compatibilityIsolatedSupport_subset yFirst.support (sigma .Y) compatibleY
  have hYUsefulSubset : yUseful.support ⊆ ySupport := by
    simpa [yUseful, yIsolated] using
      cwExactProfileSupport_subset sigma model yIsolated.support .Y targets.yExact
  have hZFirstSubset : zFirst.support ⊆ yUseful.support := by
    intro address haddress
    exact (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hZSupportSubset : zSupport ⊆ zFirst.support :=
    compatibilityIsolatedSupport_subset zFirst.support (sigma .Z) compatibleZ
  have hZUsefulSubset : zUseful.support ⊆ zSupport := by
    simpa [zUseful, zIsolated] using
      cwExactProfileSupport_subset sigma model zIsolated.support .Z targets.zExact

  have hYFirstSubsetSelected : yFirst.support ⊆ selected.support :=
    hYFirstSubset.trans (hXUsefulSubset.trans hHashedSubset)
  have hYProfiles : ∀ address ∈ yFirst.support,
      CWPooledAllYProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress
    have hxmem : address ∈ cwExactProfileSupport
        sigma model hashed.support .X targets.xExact := by
      simpa [xUseful] using hfirst.1
    refine ⟨(mem_cwExactProfileSupport
      sigma model hashed.support .X targets.xExact address).mp hxmem |>.2, ?_⟩
    exact (cw_matchesYPooledAll_iff_labelMatches
      sigma partAt pooled.yAll address).mpr hfirst.2
  have hSoundY : IsCompatibilitySound yFirst.support (sigma .Y) compatibleY := by
    exact cwSelectedExactInterfaceTerm_orientedYCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled yFirst.support
        hYFirstSubsetSelected hYProfiles
  have hYUnique : HasUniqueLegFibers yFirst.support ySupport (sigma .Y) :=
    compatibilityIsolatedSupport_hasUniqueLegFibers
      yFirst.support (sigma .Y) compatibleY hSoundY
  have hYInjective : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .Y)) ySupport :=
    hasUniqueLegFibers_injOn_selected hYUnique

  have hZFirstSubsetSelected : zFirst.support ⊆ selected.support :=
    hZFirstSubset.trans (hYUsefulSubset.trans
      (hYSupportSubset.trans hYFirstSubsetSelected))
  have hZProfiles : ∀ address ∈ zFirst.support,
      CWPooledAllZProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress
    have hyMem : address ∈ cwExactProfileSupport
        sigma model yIsolated.support .Y targets.yExact := by
      simpa [yUseful] using hfirst.1
    have hyExact := (mem_cwExactProfileSupport
      sigma model yIsolated.support .Y targets.yExact address).mp hyMem |>.2
    have hyIsolatedMem := (mem_cwExactProfileSupport
      sigma model yIsolated.support .Y targets.yExact address).mp hyMem |>.1
    have hySupportMem : address ∈ ySupport := by simpa [yIsolated] using hyIsolatedMem
    have hyFirstMem := hYSupportSubset hySupportMem
    have hyFirstData := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem
    have hxMem : address ∈ cwExactProfileSupport
        sigma model hashed.support .X targets.xExact := by
      simpa [xUseful] using hyFirstData.1
    refine ⟨(mem_cwExactProfileSupport
      sigma model hashed.support .X targets.xExact address).mp hxMem |>.2,
      hyExact, ?_⟩
    exact (cw_matchesZPooledAll_iff_labelMatches
      sigma partAt pooled.zAll address).mpr hfirst.2
  have hSoundZ : IsCompatibilitySound zFirst.support (sigma .Z) compatibleZ := by
    exact cwSelectedExactInterfaceTerm_orientedZCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled zFirst.support
        hZFirstSubsetSelected hZProfiles
  have hZUnique : HasUniqueLegFibers zFirst.support zSupport (sigma .Z) :=
    compatibilityIsolatedSupport_hasUniqueLegFibers
      zFirst.support (sigma .Z) compatibleZ hSoundZ
  have hZInjective : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .Z)) zSupport :=
    hasUniqueLegFibers_injOn_selected hZUnique

  have hXFinal : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .X)) zUseful.support :=
    hXHashed.mono (hZUsefulSubset.trans (hZSupportSubset.trans
      (hZFirstSubset.trans (hYUsefulSubset.trans
        (hYSupportSubset.trans (hYFirstSubset.trans hXUsefulSubset))))))
  have hYFinal : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .Y)) zUseful.support :=
    hYInjective.mono (hZUsefulSubset.trans (hZSupportSubset.trans
      (hZFirstSubset.trans hYUsefulSubset)))
  have hZFinal : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .Z)) zUseful.support :=
    hZInjective.mono hZUsefulSubset
  have hFinal : IsLegwiseInjective zUseful.support := by
    intro pivot
    have hpivot : sigma (sigma.symm pivot) = pivot := sigma.apply_symm_apply pivot
    generalize hlogical : sigma.symm pivot = logical at hpivot
    cases logical with
    | X =>
        have : sigma .X = pivot := by simpa [hlogical] using hpivot
        intro left hleft right hright hlabel
        apply hXFinal hleft hright
        rw [this]
        exact hlabel
    | Y =>
        have : sigma .Y = pivot := by simpa [hlogical] using hpivot
        intro left hleft right hright hlabel
        apply hYFinal hleft hright
        rw [this]
        exact hlabel
    | Z =>
        have : sigma .Z = pivot := by simpa [hlogical] using hpivot
        intro left hleft right hright hlabel
        apply hZFinal hleft hright
        rw [this]
        exact hlabel

  have hRX : Restricts hashed.realize xUseful.realize := by
    simpa [xUseful] using
      cwExactProfileSupport_restricts_of_injective
        hashed sigma model .X targets.xExact hXHashed
  have hRYFirst : Restricts xUseful.realize yFirst.realize := by
    simpa [yFirst] using
      cwPooledYFirstZeroOut_restricts
        xUseful sigma partAt pooled.yAll
  have hRYIsolate : Restricts yFirst.realize yIsolated.realize := by
    simpa [yIsolated, ySupport] using
      Tensor.Restricts.partitionedCompatibilityIsolated
        yFirst (sigma .Y) compatibleY hSoundY
  have hRYUseful : Restricts yIsolated.realize yUseful.realize := by
    simpa [yUseful] using
      cwExactProfileSupport_restricts_of_injective
        yIsolated sigma model .Y targets.yExact
          (by simpa [yIsolated] using hYInjective)
  have hRZFirst : Restricts yUseful.realize zFirst.realize := by
    simpa [zFirst] using
      cwPooledZFirstZeroOut_restricts
        yUseful sigma partAt pooled.zAll
  have hRZIsolate : Restricts zFirst.realize zIsolated.realize := by
    simpa [zIsolated, zSupport] using
      Tensor.Restricts.partitionedCompatibilityIsolated
        zFirst (sigma .Z) compatibleZ hSoundZ
  have hRZUseful : Restricts zIsolated.realize zUseful.realize := by
    simpa [zUseful] using
      cwExactProfileSupport_restricts_of_injective
        zIsolated sigma model .Z targets.zExact
          (by simpa [zIsolated] using hZInjective)
  have hDirect : Restricts zUseful.realize
      (indexedDirectSum
        (fun address : zUseful.support ↦ zUseful.constituent address.1)) :=
    Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum zUseful hFinal
  exact hRX.trans (hRYFirst.trans (hRYIsolate.trans (hRYUseful.trans
    (hRZFirst.trans (hRZIsolate.trans (hRZUseful.trans hDirect))))))

end AlgebraicComplexity.Examples
