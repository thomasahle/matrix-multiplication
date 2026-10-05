/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityProfileFiber
import AlgebraicComplexity.Examples.CoppersmithWinogradOrientedFiniteCellCore
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore

/-!
# Target-specific CW compatibility fibers

The broad coarse fiber and the parent-profile fiber are useful intermediate boxes, but neither
is the alphabet on which the paper's compatibility repair acts.  The trusted alphabet also fixes
the exact complete-split table in every tagged coarse cell, separately on all three logical legs.

This module first gives a name to the final support of the ordinary one-letter cleanup and proves
that every surviving address satisfies all three exact tables.  It then records the full tagged,
oriented coarse-cell word.  Its tag includes the region `partAt`; this is essential because a
common position permutation used by repair must preserve regions as well as the three coarse
digits.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The final fine support after exact-`X`, compatible/useful-`Y`, and compatible/useful-`Z`
cleanup inside a hash-isolated coarse family.  This is the support underlying
`cwSelectedExactInterfaceTerm_orientedGroupedCleanup_withCoarseGroup`. -/
noncomputable def cwOrientedGroupedCleanupFinalSupport
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))) :
    Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  classical
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
  exact groupStableSupport zIsolated.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)

/-- Every address surviving the complete ordinary cleanup satisfies all three exact per-cell
target tables.  In particular, later repair arguments may use their intersection as the common
alphabet; no parent-profile or pooled-only relaxation remains here. -/
theorem mem_cwOrientedGroupedCleanupFinalSupport_allExact
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ cwOrientedGroupedCleanupFinalSupport
      K q partAt term hmultiplicity sigma targets pooled coarseKept) :
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact ∧
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact ∧
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact := by
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

  have hzData : address ∈ zIsolated.support ∧ zKeep address := by
    simpa [cwOrientedGroupedCleanupFinalSupport, selected, group, fineAmbient,
      hashed, model, xSupport, xUseful, yFirst, compatibleY, ySupport, yIsolated,
      yUsefulSupport, yUseful, zFirst, compatibleZ, zSupport, zIsolated, zKeep,
      zUsefulSupport, groupStableSupport] using haddress
  have hzSupport : address ∈ zSupport := by simpa [zIsolated] using hzData.1
  have hzFirst : address ∈ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ hzSupport
  have hyUseful : address ∈ yUsefulSupport :=
    (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).1 hzFirst |>.1
  have hyData : address ∈ yIsolated.support ∧ yKeep address := by
    simpa [yUsefulSupport, groupStableSupport] using hyUseful
  have hySupport : address ∈ ySupport := by simpa [yIsolated] using hyData.1
  have hyFirst : address ∈ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY hySupport
  have hxUseful : address ∈ xSupport :=
    (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).1 hyFirst |>.1
  have hxData : address ∈ hashed.support ∧ xKeep address := by
    simpa [xSupport, groupStableSupport] using hxUseful
  exact ⟨hxData.2, hyData.2, hzData.2⟩

/-- Logical-leg form of `mem_cwOrientedGroupedCleanupFinalSupport_allExact`. -/
theorem mem_cwOrientedGroupedCleanupFinalSupport_matchesExact
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ cwOrientedGroupedCleanupFinalSupport
      K q partAt term hmultiplicity sigma targets pooled coarseKept)
    (logicalLeg : Leg) :
    (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
      (logicalAddress sigma address) logicalLeg
      (targets.exactProfile logicalLeg) := by
  have h := mem_cwOrientedGroupedCleanupFinalSupport_allExact
    K q partAt term hmultiplicity sigma targets pooled coarseKept address haddress
  cases logicalLeg with
  | X => exact h.1
  | Y => exact h.2.1
  | Z => exact h.2.2

/-- The full cell seen by the logical compatibility model at a sample position.  Unlike the
older coarse-address sequence, this includes the region tag and applies the region orientation. -/
def cwOrientedCoarseIndexSequence {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Fin (n + 1) → CoarseIndex Part :=
  fun sample ↦
    { part := partAt sample
      x := positiveWordEquiv (CWCoarseDigit depth) n (address (sigma .X)) sample
      y := positiveWordEquiv (CWCoarseDigit depth) n (address (sigma .Y)) sample
      z := positiveWordEquiv (CWCoarseDigit depth) n (address (sigma .Z)) sample }

@[simp] theorem cwOrientedCoarseIndexSequence_part {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (sample : Fin (n + 1)) :
    (cwOrientedCoarseIndexSequence depth n partAt sigma address sample).part =
      partAt sample :=
  rfl

@[simp] theorem cwOrientedCoarseIndexSequence_get {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (sample : Fin (n + 1)) (logicalLeg : Leg) :
    (cwOrientedCoarseIndexSequence depth n partAt sigma address sample).get logicalLeg =
      (positiveWordEquiv (CWCoarseDigit depth) n
        (address (sigma logicalLeg)) sample : ℕ) := by
  cases logicalLeg <;> rfl

/-- The concrete compatibility model's cell word is exactly the full tagged/oriented cell word
of its physical coarse group. -/
theorem cwExactInterfaceCompatibilityModel_coarse_eq_orientedSequence
    {Part : Type v} {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    (cwExactInterfaceCompatibilityModel depth n partAt).coarse
        (logicalAddress sigma address) =
      cwOrientedCoarseIndexSequence depth n partAt sigma
        (cwExactInterfaceCoarseGroup depth n address) := by
  funext sample
  apply coarseIndex_eq_of_part_eq_of_get_eq
  · rfl
  · intro logicalLeg
    simpa using cwExactInterfaceCompatibilityModel_coarse_get_eq_group
      partAt sigma address sample logicalLeg

/-- Fine physical-leg labels in a fixed coarse constituent which realize the prescribed exact
table in every full tagged/oriented compatibility cell.  This is the target-specific repair
alphabet; it is intentionally smaller than both `cwIdealCoarseFiberParts` and
`cwExactProfileCoarseFiberParts`. -/
noncomputable def cwExactTargetCoarseFiberParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg) :
    Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) := by
  classical
  exact Finset.univ.filter fun fine ↦
    cwOuterCoarseWord depth n fine = coarse physicalLeg ∧
      ∀ cell word,
        cellMultiplicity
          (cwOrientedCoarseIndexSequence depth n partAt sigma coarse)
          (fun sample ↦ cwChunkSplitWord depth
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              fine sample)) cell word =
        targets.exactProfile (sigma.symm physicalLeg) cell word

@[simp] theorem mem_cwExactTargetCoarseFiberParts_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg)
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    fine ∈ cwExactTargetCoarseFiberParts partAt sigma targets coarse physicalLeg ↔
      cwOuterCoarseWord depth n fine = coarse physicalLeg ∧
        ∀ cell word,
          cellMultiplicity
            (cwOrientedCoarseIndexSequence depth n partAt sigma coarse)
            (fun sample ↦ cwChunkSplitWord depth
              (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
                fine sample)) cell word =
          targets.exactProfile (sigma.symm physicalLeg) cell word := by
  classical
  simp [cwExactTargetCoarseFiberParts]

/-- Each physical-leg alphabet of a grouped cleanup fiber lies in the exact target-specific
alphabet for its coarse constituent.  The sole semantic hypothesis is exactness of all three
logical target tables on the final support; the ordinary cleanup discharges it via
`mem_cwOrientedGroupedCleanupFinalSupport_matchesExact`. -/
theorem cwCleanedFiberParts_subset_exactTarget
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg) :
    G.fiberParts coarse physicalLeg ⊆
      cwExactTargetCoarseFiberParts partAt sigma targets coarse physicalLeg := by
  classical
  intro fine hfine
  obtain ⟨address, haddress, haddressGroup, hlabel⟩ :=
    (G.mem_fiberParts_iff coarse physicalLeg fine).1 hfine
  have hcoarse : cwExactInterfaceCoarseGroup depth n address = coarse := by
    calc
      cwExactInterfaceCoarseGroup depth n address = G.group address :=
        (hgroup address).symm
      _ = coarse := haddressGroup
  apply (mem_cwExactTargetCoarseFiberParts_iff
    partAt sigma targets coarse physicalLeg fine).2
  constructor
  · have hc := congrArg (fun address ↦ address physicalLeg) hcoarse
    simpa [cwExactInterfaceCoarseGroup_apply, hlabel] using hc
  · intro cell word
    let logicalLeg := sigma.symm physicalLeg
    have hmatch := hExact address haddress logicalLeg cell word
    have hmodelCoarse :
        (cwExactInterfaceCompatibilityModel depth n partAt).coarse
            (logicalAddress sigma address) =
          cwOrientedCoarseIndexSequence depth n partAt sigma coarse := by
      rw [cwExactInterfaceCompatibilityModel_coarse_eq_orientedSequence,
        hcoarse]
    have hchunks :
        (cwExactInterfaceCompatibilityModel depth n partAt).chunks logicalLeg
            (logicalAddress sigma address logicalLeg) =
          fun sample ↦ cwChunkSplitWord depth
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              fine sample) := by
      funext sample
      rw [cwExactInterfaceCompatibilityModel_chunks_logicalAddress]
      rw [show sigma logicalLeg = physicalLeg by
        exact sigma.apply_symm_apply physicalLeg]
      rw [hlabel]
    rw [hmodelCoarse, hchunks] at hmatch
    exact hmatch

/-! ## Full-cell fixed types and transport -/

/-- `cellMultiplicity` is ordinary word multiplicity on the joint `(cell, symbol)` alphabet. -/
theorem cellMultiplicity_eq_jointMultiplicity
    {samples : ℕ} {Cell Symbol : Type*}
    [Fintype Cell] [DecidableEq Cell] [Fintype Symbol] [DecidableEq Symbol]
    (cellOf : Fin samples → Cell) (word : Fin samples → Symbol)
    (cell : Cell) (symbol : Symbol) :
    cellMultiplicity cellOf word cell symbol =
      WordType.multiplicity (fun position ↦ (cellOf position, word position))
        (cell, symbol) := by
  classical
  unfold cellMultiplicity WordType.multiplicity
  congr 1
  ext position
  simp [Prod.ext_iff]

/-- Simultaneously reindexing cells and symbols preserves every cell multiplicity. -/
theorem cellMultiplicity_comp_perm
    {samples : ℕ} {Cell Symbol : Type*}
    [DecidableEq Cell] [DecidableEq Symbol]
    (cellOf : Fin samples → Cell) (word : Fin samples → Symbol)
    (tau : Equiv.Perm (Fin samples)) (cell : Cell) (symbol : Symbol) :
    cellMultiplicity (cellOf ∘ tau) (word ∘ tau) cell symbol =
      cellMultiplicity cellOf word cell symbol := by
  classical
  unfold cellMultiplicity
  apply Finset.card_bij (fun position _hposition ↦ tau position)
  · intro position hposition
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] at hposition ⊢
    exact hposition
  · intro left hleft right hright heq
    exact tau.injective heq
  · intro position hposition
    refine ⟨tau.symm position, ?_, ?_⟩
    · simpa [Function.comp_apply] using hposition
    · exact tau.apply_symm_apply position

/-- Read a coarse address as a word over the finite tagged/oriented cell alphabet. -/
def cwOrientedFiniteCellSequence {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Fin (n + 1) → CWOrientedCoarseCell Part depth :=
  fun sample ↦ ⟨partAt sample, fun logicalLeg ↦
    positiveWordEquiv (CWCoarseDigit depth) n
      (address (sigma logicalLeg)) sample⟩

@[simp] theorem cwOrientedCoarseCellToIndex_sequence
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    cwOrientedCoarseCellToIndex ∘
        cwOrientedFiniteCellSequence depth n partAt sigma address =
      cwOrientedCoarseIndexSequence depth n partAt sigma address := by
  funext sample
  rfl

/-- Canonical common position permutation between two coarse addresses having the same full
tagged/oriented cell type. -/
noncomputable def cwOrientedCellPositionPermOfSameMultiplicity
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma left) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma right)) :
    Equiv.Perm (Fin (n + 1)) :=
  WordType.positionPermOfSameMultiplicity
    (cwOrientedFiniteCellSequence depth n partAt sigma left)
    (cwOrientedFiniteCellSequence depth n partAt sigma right) h

/-- The chosen full-cell permutation sends the right cell word to the left cell word. -/
theorem cwOrientedCoarseIndexSequence_positionPermOfSameMultiplicity
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma left) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma right)) :
    cwOrientedFiniteCellSequence depth n partAt sigma right ∘
        cwOrientedCellPositionPermOfSameMultiplicity
          depth n partAt sigma left right h =
      cwOrientedFiniteCellSequence depth n partAt sigma left :=
  WordType.positionPermOfSameMultiplicity_map _ _ h

/-- A full-cell normalization permutation preserves the region assignment. -/
theorem partAt_comp_cwOrientedCellPositionPermOfSameMultiplicity
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma left) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma right)) :
    partAt ∘ cwOrientedCellPositionPermOfSameMultiplicity
        depth n partAt sigma left right h = partAt := by
  funext sample
  have hmap := congrFun
    (cwOrientedCoarseIndexSequence_positionPermOfSameMultiplicity
      depth n partAt sigma left right h) sample
  exact congrArg Prod.fst hmap

/-- The full-cell normalization permutation also sends the right physical coarse address to the
left physical coarse address. -/
theorem cwPositionRelabelCoarseAddress_orientedCellPositionPerm
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma left) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma right)) :
    cwPositionRelabelCoarseAddress depth n
        (cwOrientedCellPositionPermOfSameMultiplicity
          depth n partAt sigma left right h) right = left := by
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt sigma left right h
  have hmap := cwOrientedCoarseIndexSequence_positionPermOfSameMultiplicity
    depth n partAt sigma left right h
  funext physicalLeg
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  let logicalLeg := sigma.symm physicalLeg
  have hcell := congrArg (fun q ↦ q.2 logicalLeg) (congrFun hmap sample)
  change (positiveWordEquiv (CWCoarseDigit depth) n
      (right (sigma logicalLeg)) (tau sample)) =
    positiveWordEquiv (CWCoarseDigit depth) n
      (left (sigma logicalLeg)) sample at hcell
  rw [show sigma logicalLeg = physicalLeg by
    exact sigma.apply_symm_apply physicalLeg] at hcell
  simpa [cwPositionRelabelCoarseAddress, tau] using hcell

/-- Transport of a target-specific alphabet along a position permutation carrying one full cell
word to another. -/
theorem cwExactTargetCoarseFiberParts_positionRelabel
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (tau : Equiv.Perm (Fin (n + 1)))
    (hcells : cwOrientedCoarseIndexSequence depth n partAt sigma right ∘ tau =
      cwOrientedCoarseIndexSequence depth n partAt sigma left)
    (hcoarse : cwPositionRelabelCoarseAddress depth n tau right = left)
    (physicalLeg : Leg)
    {fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n}
    (hfine : fine ∈
      cwExactTargetCoarseFiberParts partAt sigma targets right physicalLeg) :
    positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n tau fine ∈
      cwExactTargetCoarseFiberParts partAt sigma targets left physicalLeg := by
  classical
  let moved := positiveWordPositionEquiv
    (PositiveWord CWBlock (2 ^ depth - 1)) n tau fine
  have hdata := (mem_cwExactTargetCoarseFiberParts_iff
    partAt sigma targets right physicalLeg fine).1 hfine
  apply (mem_cwExactTargetCoarseFiberParts_iff
    partAt sigma targets left physicalLeg moved).2
  constructor
  · calc
      cwOuterCoarseWord depth n moved =
          positiveWordPositionEquiv (CWCoarseDigit depth) n tau
            (cwOuterCoarseWord depth n fine) := by
        exact cwOuterCoarseWord_positionRelabel depth n tau fine
      _ = cwPositionRelabelCoarseAddress depth n tau right physicalLeg := by
        rw [hdata.1]
        rfl
      _ = left physicalLeg := congrFun hcoarse physicalLeg
  · intro cell word
    have hchunks :
        (fun sample ↦ cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            moved sample)) =
          (fun sample ↦ cwChunkSplitWord depth
            (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
              fine sample)) ∘ tau := by
      funext sample
      simp [moved, Function.comp_apply]
    rw [← hcells, hchunks, cellMultiplicity_comp_perm]
    exact hdata.2 cell word

end AlgebraicComplexity.Examples
