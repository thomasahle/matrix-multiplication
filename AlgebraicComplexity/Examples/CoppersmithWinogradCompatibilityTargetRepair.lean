/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetFiber
import AlgebraicComplexity.Combinatorics.TransitiveUniformity
import AlgebraicComplexity.MatrixMultiplication.GroupedVariableHoleRepair

/-!
# Finite repair of target-specific CW compatibility fibers

This module keeps the exact quantitative interface of the ordinary one-letter hole-repair step.
Coarse addresses are normalized only when their full finite cell words agree in multiplicity;
the cell word includes the region tag and the oriented coarse triple.  Every normalized cleaned
fiber is then a damaged box of the exact per-cell target alphabet.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Retained coarse addresses of the same full tagged/oriented cell type as `reference`. -/
noncomputable def cwFixedTargetCellTypeCoarseSupport
    {Part : Type v} [Fintype Part] [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) := by
  classical
  exact coarseKept.filter fun coarse ↦
    WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse)

@[simp] theorem mem_cwFixedTargetCellTypeCoarseSupport_iff
    {Part : Type v} [Fintype Part] [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    coarse ∈ cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma coarseKept reference ↔
      coarse ∈ coarseKept ∧
        WordType.multiplicity
            (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
          WordType.multiplicity
            (cwOrientedFiniteCellSequence depth n partAt sigma coarse) := by
  classical
  simp [cwFixedTargetCellTypeCoarseSupport]

/-- Surviving fine labels transported from one full-cell-type constituent to the reference. -/
noncomputable def cwTargetMovedCleanedFiberParts
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [Fintype Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse)) :
    ∀ _c : Leg,
      Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :=
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt sigma reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity tau
  relabelParts relabeling.partEquiv (G.fiberParts coarse)

/-- Normalized cleaned labels lie in the reference's exact target-specific alphabet. -/
theorem cwTargetMovedCleanedFiberParts_subset_reference
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
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
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse))
    (physicalLeg : Leg) :
    cwTargetMovedCleanedFiberParts K q partAt sigma term hmultiplicity
        G reference coarse hsame physicalLeg ⊆
      cwExactTargetCoarseFiberParts
        partAt sigma targets reference physicalLeg := by
  classical
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt sigma reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity tau
  intro fine hfine
  have horiginal : (relabeling.partEquiv physicalLeg).symm fine ∈
      G.fiberParts coarse physicalLeg := by
    simpa [cwTargetMovedCleanedFiberParts, tau, relabeling] using hfine
  have horiginalTarget := cwCleanedFiberParts_subset_exactTarget
    K q partAt term hmultiplicity sigma targets finalSupport hExact G hgroup
      coarse physicalLeg horiginal
  have hfiniteCells :=
    cwOrientedCoarseIndexSequence_positionPermOfSameMultiplicity
      depth n partAt sigma reference coarse hsame
  have hcells :
      cwOrientedCoarseIndexSequence depth n partAt sigma coarse ∘ tau =
        cwOrientedCoarseIndexSequence depth n partAt sigma reference := by
    funext sample
    have hsample := congrArg cwOrientedCoarseCellToIndex
      (congrFun hfiniteCells sample)
    change cwOrientedCoarseIndexSequence depth n partAt sigma coarse
        (tau sample) =
      cwOrientedCoarseIndexSequence depth n partAt sigma reference sample at hsample
    exact hsample
  have hcoarse : cwPositionRelabelCoarseAddress depth n tau coarse = reference :=
    cwPositionRelabelCoarseAddress_orientedCellPositionPerm
      depth n partAt sigma reference coarse hsame
  have hmoved := cwExactTargetCoarseFiberParts_positionRelabel
    partAt sigma targets reference coarse tau hcells hcoarse physicalLeg
      horiginalTarget
  have hpartEquiv : relabeling.partEquiv physicalLeg =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n tau :=
    cwSelectedExactInterfaceTermPositionRelabeling_partEquiv
      K q term hmultiplicity tau physicalLeg
  rw [hpartEquiv] at hmoved
  simpa using hmoved

/-- Target-specific compact holes in one transported cleaned fiber. -/
noncomputable def cwTargetCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [Fintype Part]
    [DecidableEq Part] {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) :=
  Finset.univ \ compactBoxSubparts
    (cwExactTargetCoarseFiberParts partAt sigma targets reference)
    (cwTargetMovedCleanedFiberParts K q partAt sigma term hmultiplicity
      G reference coarse hsame) physicalLeg

@[simp] theorem univ_sdiff_cwTargetCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [Fintype Part]
    [DecidableEq Part] {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse))
    (physicalLeg : Leg) :
    Finset.univ \ cwTargetCleanedFiberHoles K q partAt sigma targets term
        hmultiplicity G reference coarse hsame physicalLeg =
      compactBoxSubparts
        (cwExactTargetCoarseFiberParts partAt sigma targets reference)
        (cwTargetMovedCleanedFiberParts K q partAt sigma term hmultiplicity
          G reference coarse hsame) physicalLeg := by
  classical
  apply Finset.sdiff_sdiff_eq_self
  exact Finset.subset_univ _

/-- A full-cell-type cleaned fiber restricts to its damaged box inside the exact target-specific
compact reference tensor. -/
theorem cwCleanedFiber_restricts_compactTargetReferenceBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hcoarse : coarse ∈ coarseKept)
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse)) :
    Restricts (G.fiber coarse).realize
      ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwExactTargetCoarseFiberParts partAt sigma targets reference)).box
        (fun c ↦ Finset.univ \ cwTargetCleanedFiberHoles K q partAt sigma targets
          term hmultiplicity G reference coarse hsame c)).realize := by
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt sigma reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity tau
  let moved := cwTargetMovedCleanedFiberParts
    K q partAt sigma term hmultiplicity G reference coarse hsame
  have hfiber : G.fiber coarse = selected.box (G.fiberParts coarse) :=
    cwCleanedFiber_eq_selected_box_fiberParts K q term hmultiplicity
      coarseKept finalSupport hclosed G hgroup coarse hcoarse
  have hrelabel : Isomorphic (selected.box (G.fiberParts coarse)).realize
      (selected.box moved).realize := by
    simpa [moved, cwTargetMovedCleanedFiberParts, tau, relabeling] using
      relabeling.box_isomorphic (G.fiberParts coarse)
  have hsubset : ∀ c, moved c ⊆
      cwExactTargetCoarseFiberParts partAt sigma targets reference c := by
    intro c
    simpa [moved] using cwTargetMovedCleanedFiberParts_subset_reference
      K q partAt term hmultiplicity sigma targets finalSupport hExact G hgroup
        reference coarse hsame c
  have hcompact := Restricts.box_to_compactBox_box selected
    (cwExactTargetCoarseFiberParts partAt sigma targets reference) moved hsubset
  have hholes : (fun c ↦ Finset.univ \ cwTargetCleanedFiberHoles K q partAt
      sigma targets term hmultiplicity G reference coarse hsame c) =
      compactBoxSubparts
        (cwExactTargetCoarseFiberParts partAt sigma targets reference) moved := by
    funext c
    exact univ_sdiff_cwTargetCleanedFiberHoles K q partAt sigma targets term
      hmultiplicity G reference coarse hsame c
  rw [← hholes] at hcompact
  exact (Restricts.of_eq (congrArg PartitionedTensor.realize hfiber)).trans
    (hrelabel.restricts.trans hcompact)

/-- The exact target-specific damaged-fiber model over one retained full-cell type. -/
noncomputable def cwTargetCellTypeCleanedModel
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)) :
    HoleRepair.ModeledFiberFamily
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwExactTargetCoarseFiberParts partAt sigma targets reference))
      (fun coarse : cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma coarseKept reference ↦
        (G.fiber coarse.1).realize) where
  holes coarse := cwTargetCleanedFiberHoles K q partAt sigma targets term
    hmultiplicity G reference coarse.1
      ((mem_cwFixedTargetCellTypeCoarseSupport_iff
        depth n partAt sigma coarseKept reference coarse.1).1 coarse.2).2
  fiber_restricts coarse :=
    cwCleanedFiber_restricts_compactTargetReferenceBox K q partAt term
      hmultiplicity sigma targets coarseKept finalSupport hclosed hExact G hgroup
        reference coarse.1
        ((mem_cwFixedTargetCellTypeCoarseSupport_iff
          depth n partAt sigma coarseKept reference coarse.1).1 coarse.2).1
        ((mem_cwFixedTargetCellTypeCoarseSupport_iff
          depth n partAt sigma coarseKept reference coarse.1).1 coarse.2).2

/-! ## Common cell-stabilizer relabelings -/

/-- Position permutations preserving every full tagged/oriented cell of the reference. -/
def cwReferenceCellPermSubgroup
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Subgroup (Equiv.Perm (Fin (n + 1))) where
  carrier := {tau | cwOrientedFiniteCellSequence depth n partAt sigma reference ∘ tau =
    cwOrientedFiniteCellSequence depth n partAt sigma reference}
  one_mem' := by
    funext sample
    rfl
  mul_mem' := by
    intro left right hleft hright
    funext sample
    have hl := congrFun hleft (right sample)
    have hr := congrFun hright sample
    change cwOrientedFiniteCellSequence depth n partAt sigma reference
        (left (right sample)) =
      cwOrientedFiniteCellSequence depth n partAt sigma reference
        (right sample) at hl
    change cwOrientedFiniteCellSequence depth n partAt sigma reference
        (right sample) =
      cwOrientedFiniteCellSequence depth n partAt sigma reference sample at hr
    exact hl.trans hr
  inv_mem' := by
    intro tau htau
    funext sample
    have h := congrFun htau (tau.symm sample)
    simpa using h.symm

/-- A finite-cell-preserving position permutation fixes the physical coarse reference address. -/
theorem cwPositionRelabelCoarseAddress_eq_of_mem_referenceCellPermSubgroup
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (tau : cwReferenceCellPermSubgroup depth n partAt sigma reference) :
    cwPositionRelabelCoarseAddress depth n tau.1 reference = reference := by
  funext physicalLeg
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  let logicalLeg := sigma.symm physicalLeg
  have hcell := congrArg (fun q ↦ q.2 logicalLeg) (congrFun tau.2 sample)
  change positiveWordEquiv (CWCoarseDigit depth) n
      (reference (sigma logicalLeg)) (tau.1 sample) =
    positiveWordEquiv (CWCoarseDigit depth) n
      (reference (sigma logicalLeg)) sample at hcell
  rw [show sigma logicalLeg = physicalLeg by
    exact sigma.apply_symm_apply physicalLeg] at hcell
  simpa [cwPositionRelabelCoarseAddress] using hcell

/-- The exact target alphabet is invariant under the common cell stabilizer. -/
theorem cwExactTargetCoarseFiberParts_positionRelabel_iff
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (tau : cwReferenceCellPermSubgroup depth n partAt sigma reference)
    (physicalLeg : Leg)
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n tau.1 fine ∈
        cwExactTargetCoarseFiberParts partAt sigma targets reference physicalLeg ↔
      fine ∈ cwExactTargetCoarseFiberParts
        partAt sigma targets reference physicalLeg := by
  classical
  let indexSequence := cwOrientedCoarseIndexSequence
    depth n partAt sigma reference
  have hcells : indexSequence ∘ tau.1 = indexSequence := by
    funext sample
    have hsample := congrArg cwOrientedCoarseCellToIndex
      (congrFun tau.2 sample)
    change indexSequence (tau.1 sample) = indexSequence sample at hsample
    exact hsample
  have hcoarse := cwPositionRelabelCoarseAddress_eq_of_mem_referenceCellPermSubgroup
    depth n partAt sigma reference tau
  constructor
  · intro hmoved
    let tauInv : cwReferenceCellPermSubgroup depth n partAt sigma reference :=
      tau⁻¹
    have hcellsInv : indexSequence ∘ tauInv.1 = indexSequence := by
      funext sample
      have hsample := congrArg cwOrientedCoarseCellToIndex
        (congrFun tauInv.2 sample)
      change indexSequence (tauInv.1 sample) = indexSequence sample at hsample
      exact hsample
    have hcoarseInv :=
      cwPositionRelabelCoarseAddress_eq_of_mem_referenceCellPermSubgroup
        depth n partAt sigma reference tauInv
    have hback := cwExactTargetCoarseFiberParts_positionRelabel
      partAt sigma targets reference reference tauInv.1 hcellsInv hcoarseInv
        physicalLeg hmoved
    have hundo :
        positiveWordPositionEquiv
            (PositiveWord CWBlock (2 ^ depth - 1)) n tauInv.1
            (positiveWordPositionEquiv
              (PositiveWord CWBlock (2 ^ depth - 1)) n tau.1 fine) = fine := by
      apply (positiveWordEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n).injective
      simp [tauInv, Function.comp_def]
    rw [hundo] at hback
    exact hback
  · intro hfine
    exact cwExactTargetCoarseFiberParts_positionRelabel
      partAt sigma targets reference reference tau.1 hcells hcoarse
        physicalLeg hfine

/-- Permutation induced on one exact target-specific compact part alphabet. -/
noncomputable def cwExactTargetPartPositionEquiv
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (tau : cwReferenceCellPermSubgroup depth n partAt sigma reference)
    (physicalLeg : Leg) :
    Equiv.Perm (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) :=
  invariantFinsetSubtypePerm
    (positiveWordPositionEquiv
      (PositiveWord CWBlock (2 ^ depth - 1)) n tau.1)
    (cwExactTargetCoarseFiberParts partAt sigma targets reference physicalLeg)
    (fun fine ↦ (cwExactTargetCoarseFiberParts_positionRelabel_iff
      partAt sigma targets reference tau physicalLeg fine).symm)

@[simp] theorem cwExactTargetPartPositionEquiv_apply_val
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (tau : cwReferenceCellPermSubgroup depth n partAt sigma reference)
    (physicalLeg : Leg)
    (fine : BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) :
    (cwExactTargetPartPositionEquiv
      partAt sigma targets reference tau physicalLeg fine).1 =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n tau.1 fine.1 :=
  rfl

/-- The bounded-cell encoding into the compatibility model's natural-valued cells is injective. -/
theorem cwOrientedCoarseCellToIndex_injective
    {Part : Type v} {depth : ℕ} :
    Function.Injective (cwOrientedCoarseCellToIndex :
      CWOrientedCoarseCell Part depth → CoarseIndex Part) := by
  rintro ⟨leftPart, left⟩ ⟨rightPart, right⟩ h
  apply Prod.ext
  · exact congrArg CoarseIndex.part h
  · funext logicalLeg
    apply Fin.ext
    cases logicalLeg with
    | X => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.x h
    | Y => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.y h
    | Z => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.z h

/-- Multiplicity of a bounded `(cell, split-word)` pair is the corresponding compatibility-cell
multiplicity after embedding the cell into `CoarseIndex`. -/
theorem cwFiniteCellSplitMultiplicity_eq_cellMultiplicity
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    (cell : CWOrientedCoarseCell Part depth) (word : SplitWord depth) :
    WordType.multiplicity
        (fun sample ↦
          (cwOrientedFiniteCellSequence depth n partAt sigma reference sample,
            cwChunkSplitWord depth
              (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
                fine sample))) (cell, word) =
      cellMultiplicity
        (cwOrientedCoarseIndexSequence depth n partAt sigma reference)
        (fun sample ↦ cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            fine sample))
        (cwOrientedCoarseCellToIndex cell) word := by
  classical
  unfold WordType.multiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨hcell, hword⟩
    exact ⟨congrArg cwOrientedCoarseCellToIndex hcell, hword⟩
  · rintro ⟨hcell, hword⟩
    exact ⟨cwOrientedCoarseCellToIndex_injective hcell, hword⟩

/-- The opposite of the cell stabilizer acts by the advertised position permutations. -/
@[instance_reducible] noncomputable def cwExactTargetPartMulAction
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg) :
    MulAction
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ
      (BoxPart
        (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) where
  smul g fine := cwExactTargetPartPositionEquiv
    partAt sigma targets reference g.unop physicalLeg fine
  one_smul fine := by
    apply Subtype.ext
    change positiveWordPositionEquiv
      (PositiveWord CWBlock (2 ^ depth - 1)) n
        ((1 : cwReferenceCellPermSubgroup depth n partAt sigma reference) :
          Equiv.Perm (Fin (n + 1))) fine.1 = fine.1
    simp
  mul_smul left right fine := by
    apply Subtype.ext
    change positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n (right.unop.1 * left.unop.1) fine.1 =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n left.unop.1
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n right.unop.1 fine.1)
    exact congrArg (fun e : Equiv.Perm
      (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦ e fine.1)
        (positiveWordPositionEquiv_mul
          (PositiveWord CWBlock (2 ^ depth - 1)) n right.unop.1 left.unop.1)

/-- The common cell stabilizer is transitive on every exact target-specific leg alphabet. -/
theorem cwExactTargetPart_isPretransitive
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg) :
    letI := cwExactTargetPartMulAction
      partAt sigma targets reference physicalLeg
    MulAction.IsPretransitive
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ
      (BoxPart
        (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) := by
  letI := cwExactTargetPartMulAction
    partAt sigma targets reference physicalLeg
  constructor
  intro left right
  let cellSequence := cwOrientedFiniteCellSequence
    depth n partAt sigma reference
  let splitSequence := fun
      (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) sample ↦
    cwChunkSplitWord depth
      (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n fine sample)
  let jointSequence := fun
      (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) sample ↦
    (cellSequence sample, splitSequence fine sample)
  have hleft := (mem_cwExactTargetCoarseFiberParts_iff
    partAt sigma targets reference physicalLeg left.1).1 left.2
  have hright := (mem_cwExactTargetCoarseFiberParts_iff
    partAt sigma targets reference physicalLeg right.1).1 right.2
  have hjoint : WordType.multiplicity (jointSequence left.1) =
      WordType.multiplicity (jointSequence right.1) := by
    funext pair
    rcases pair with ⟨cell, word⟩
    change WordType.multiplicity
        (fun sample ↦
          (cwOrientedFiniteCellSequence depth n partAt sigma reference sample,
            cwChunkSplitWord depth
              (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
                left.1 sample))) (cell, word) =
      WordType.multiplicity
        (fun sample ↦
          (cwOrientedFiniteCellSequence depth n partAt sigma reference sample,
            cwChunkSplitWord depth
              (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
                right.1 sample))) (cell, word)
    rw [cwFiniteCellSplitMultiplicity_eq_cellMultiplicity,
      cwFiniteCellSplitMultiplicity_eq_cellMultiplicity]
    exact (hleft.2 (cwOrientedCoarseCellToIndex cell) word).trans
      (hright.2 (cwOrientedCoarseCellToIndex cell) word).symm
  let tau := WordType.positionPermOfSameMultiplicity
    (jointSequence right.1) (jointSequence left.1) hjoint.symm
  have hmap : jointSequence left.1 ∘ tau = jointSequence right.1 :=
    WordType.positionPermOfSameMultiplicity_map _ _ hjoint.symm
  have hcells : cellSequence ∘ tau = cellSequence := by
    funext sample
    exact congrArg Prod.fst (congrFun hmap sample)
  let stabilizerElement :
      cwReferenceCellPermSubgroup depth n partAt sigma reference :=
    ⟨tau, hcells⟩
  refine ⟨MulOpposite.op stabilizerElement, ?_⟩
  change cwExactTargetPartPositionEquiv partAt sigma targets reference
      stabilizerElement physicalLeg left = right
  apply Subtype.ext
  apply (positiveWordEquiv
    (PositiveWord CWBlock (2 ^ depth - 1)) n).injective
  funext sample
  rw [cwExactTargetPartPositionEquiv_apply_val,
    positiveWordEquiv_position_apply]
  apply cwChunkSplitWord_injective depth
  exact congrArg Prod.snd (congrFun hmap sample)

noncomputable local instance cwReferenceCellPermSubgroupFintype
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Fintype (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
  Fintype.ofFinite _

noncomputable local instance cwReferenceCellPermSubgroupDecidableEq
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    DecidableEq (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
  Classical.decEq _

/-- Exact uniform relabeling family on one target-specific physical leg. -/
noncomputable def cwExactTargetUniformOnParts
    {Part : Type v} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (physicalLeg : Leg) :
    letI : Fintype
        (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
      Fintype.ofFinite _
    letI : DecidableEq
        (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
      Classical.decEq _
    letI : Fintype
        (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ :=
      Fintype.ofEquiv
        (cwReferenceCellPermSubgroup depth n partAt sigma reference)
        MulOpposite.opEquiv
    letI : DecidableEq
        (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ :=
      Classical.decEq _
    HoleRepair.UniformOnParts
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ
      (BoxPart
        (cwExactTargetCoarseFiberParts partAt sigma targets reference) physicalLeg) := by
  letI : Fintype
      (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
    Fintype.ofFinite _
  letI : DecidableEq
      (cwReferenceCellPermSubgroup depth n partAt sigma reference) :=
    Classical.decEq _
  letI : Fintype
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ :=
    Fintype.ofEquiv
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)
      MulOpposite.opEquiv
  letI : DecidableEq
      (cwReferenceCellPermSubgroup depth n partAt sigma reference)ᵐᵒᵖ :=
    Classical.decEq _
  letI := cwExactTargetPartMulAction
    partAt sigma targets reference physicalLeg
  letI := cwExactTargetPart_isPretransitive
    partAt sigma targets reference physicalLeg
  exact HoleRepair.UniformOnParts.ofPretransitiveMulAction

/-- The exact finite cell stabilizer gives one simultaneous, structure-preserving, uniform
relabeling family on all three target-specific physical-leg alphabets. -/
noncomputable def cwExactTargetUniformStructureRelabelings
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    let CellPerm := cwReferenceCellPermSubgroup depth n partAt sigma reference
    letI : Fintype CellPerm := Fintype.ofFinite _
    letI : DecidableEq CellPerm := Classical.decEq _
    letI : Fintype CellPermᵐᵒᵖ :=
      Fintype.ofEquiv CellPerm MulOpposite.opEquiv
    letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
    HoleRepair.UniformStructureRelabelings
      (G := CellPermᵐᵒᵖ)
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwExactTargetCoarseFiberParts partAt sigma targets reference)) := by
  classical
  let CellPerm := cwReferenceCellPermSubgroup depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  let ambient (g : CellPermᵐᵒᵖ) :=
    cwSelectedExactInterfaceTermPositionRelabeling
      K q term hmultiplicity g.unop.1
  let invariant (g : CellPermᵐᵒᵖ) (c : Leg)
      (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
      fine ∈ cwExactTargetCoarseFiberParts partAt sigma targets reference c ↔
        (ambient g).partEquiv c fine ∈
          cwExactTargetCoarseFiberParts partAt sigma targets reference c := by
    rw [cwSelectedExactInterfaceTermPositionRelabeling_partEquiv]
    exact (cwExactTargetCoarseFiberParts_positionRelabel_iff
      partAt sigma targets reference g.unop c fine).symm
  let relabeling (g : CellPermᵐᵒᵖ) :=
    (ambient g).compactBox
      (cwExactTargetCoarseFiberParts partAt sigma targets reference)
      (invariant g)
  refine
    { relabeling := relabeling
      uniform := fun c ↦ cwExactTargetUniformOnParts
        partAt sigma targets reference c
      uniform_eq := ?_ }
  intro g c
  apply Equiv.ext
  intro fine
  apply Subtype.ext
  change positiveWordPositionEquiv
      (PositiveWord CWBlock (2 ^ depth - 1)) n g.unop.1 fine.1 =
    ((relabeling g).partEquiv c fine).1
  rw [PartitionedTensor.StructureRelabeling.compactBox_partEquiv_apply_val]
  change positiveWordPositionEquiv
      (PositiveWord CWBlock (2 ^ depth - 1)) n g.unop.1 fine.1 =
    (ambient g).partEquiv c fine.1
  rw [cwSelectedExactInterfaceTermPositionRelabeling_partEquiv]

/-! ## Exact sparse supply and repaired target copies -/

/-- Full-cell-type retained addresses satisfying the three literal target-alphabet hole bounds.
This is the finite set whose cardinality the quantitative type-counting layer must lower-bound. -/
noncomputable def cwSparseTargetCellTypeAddresses
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ) :
    Finset (cwFixedTargetCellTypeCoarseSupport
      depth n partAt sigma coarseKept reference) :=
  (cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma targets
    coarseKept finalSupport hclosed hExact G hgroup reference).sparseIndices base

/-- Membership in the target-specific repair supply is *definitionally equivalent* to the
paper-facing sparse-hole inequalities.  In particular the denominator is the exact intersection
of all prescribed per-cell split tables, not a relaxed parent-profile alphabet. -/
@[simp] theorem mem_cwSparseTargetCellTypeAddresses_iff
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ)
    (coarse : cwFixedTargetCellTypeCoarseSupport
      depth n partAt sigma coarseKept reference) :
    coarse ∈ cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base ↔
      ∀ c,
        base * (4 * (cwTargetCleanedFiberHoles K q partAt sigma targets term
          hmultiplicity G reference coarse.1
          ((mem_cwFixedTargetCellTypeCoarseSupport_iff
            depth n partAt sigma coarseKept reference coarse.1).1 coarse.2).2 c).card) ≤
          (cwExactTargetCoarseFiberParts
            partAt sigma targets reference c).card := by
  classical
  rw [cwSparseTargetCellTypeAddresses,
    HoleRepair.ModeledFiberFamily.mem_sparseIndices_iff]
  simp only [cwTargetCellTypeCleanedModel, Fintype_card_BoxPart]

/-- A single exact sparse-address count constructs all varying repair plans and an indexed direct
sum of intact target-specific boxes.  The relabeling hypothesis present in the generic repair
theorem has been completely discharged by the common full-cell stabilizer. -/
theorem exists_cwTargetCellType_repairPlans_of_sparse_count
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base).card) :
    ∃ plans : O → Tensor.RepairPlan
        (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwExactTargetCoarseFiberParts partAt sigma targets reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            (cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets coarseKept finalSupport hclosed hExact G hgroup reference).holes
                (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum
            (fun coarse : cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma coarseKept reference ↦
              (G.fiber coarse.1).realize))
          (Tensor.indexedDirectSum (fun _output : O ↦
            ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
              (cwExactTargetCoarseFiberParts partAt sigma targets reference)).box
                target).realize)) := by
  classical
  let CellPerm := cwReferenceCellPermSubgroup depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  exact (cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma targets
    coarseKept finalSupport hclosed hExact G hgroup reference
      ).exists_repairPlans_of_mul_budget_le_sparse
        (cwExactTargetUniformStructureRelabelings
          K q partAt sigma targets term hmultiplicity reference)
        hbase d target hdepth hcount

/-- The full grouped cleaned family restricts to its chosen full-cell-type subfamily. -/
theorem cwGroupedFibers_restricts_fixedTargetCellType
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)) :
    Restricts
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize))
      (Tensor.indexedDirectSum
        (fun coarse : cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference ↦
          (G.fiber coarse.1).realize)) := by
  exact Tensor.Restricts.indexedDirectSum_subfamily
    (fun coarse : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
        (G.fiber coarse).realize)
    (cwFixedTargetCellTypeCoarseSupport
      depth n partAt sigma coarseKept reference)

/-- End-to-end finite target-specific repair adapter.  Any source already restricted to the
grouped cleaned family restricts further to the requested number of intact exact target boxes.
All compatibility and relabeling semantics are proved above; only the displayed finite sparse
count and repair-depth inequalities remain quantitative inputs. -/
theorem exists_cwGroupedCleanup_repairedTargetCellType_of_sparse_count
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    (source : Tensor3 K S)
    (hsource : Restricts source
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize)))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base).card) :
    ∃ plans : O → Tensor.RepairPlan
        (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwExactTargetCoarseFiberParts partAt sigma targets reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            (cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets coarseKept finalSupport hclosed hExact G hgroup reference).holes
                (pick occurrence)) ∧
        Restricts source
          (Tensor.indexedDirectSum (fun _output : O ↦
            ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
              (cwExactTargetCoarseFiberParts partAt sigma targets reference)).box
                target).realize)) := by
  obtain ⟨plans, pick, hholes, hrepair⟩ :=
    exists_cwTargetCellType_repairPlans_of_sparse_count
      K q partAt term hmultiplicity sigma targets coarseKept finalSupport hclosed
        hExact G hgroup reference hbase d target hdepth hcount
  refine ⟨plans, pick, hholes, ?_⟩
  exact hsource.trans
    ((cwGroupedFibers_restricts_fixedTargetCellType K q partAt term
      hmultiplicity sigma G coarseKept reference).trans hrepair)

end AlgebraicComplexity.Examples
