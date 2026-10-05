/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseCleanup
import AlgebraicComplexity.MatrixMultiplication.GroupedVariableHoleRepair
import AlgebraicComplexity.Tensor.PartitionedBoxRetyping
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes

/-!
# Normalizing fixed-type CW coarse fibers

The paper selects coarse constituent words of one fixed joint multiplicity type.  Any two such
words differ by a common permutation of their sample positions.  Exact CW interface terms carry
that full symmetric-group action as genuine structure relabelings, so their ideal (pre-cleanup)
coarse fibers are tensor-isomorphic.

This module proves that finite normalization step.  It is independent of hashing, compatibility
counts, and hole-density estimates.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Read a three-leg coarse block address as a word of coarse constituent triples. -/
def cwCoarseAddressSequence (depth n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Fin (n + 1) → BlockAddress (fun _c ↦ CWCoarseDigit depth) :=
  fun sample c ↦
    positiveWordEquiv (CWCoarseDigit depth) n (address c) sample

/-- Apply one common sample-position permutation to all three coarse block words. -/
def cwPositionRelabelCoarseAddress (depth n : ℕ)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) :=
  fun c ↦ positiveWordPositionEquiv (CWCoarseDigit depth) n sigma (address c)

@[simp] theorem cwCoarseAddressSequence_positionRelabel
    (depth n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    cwCoarseAddressSequence depth n
        (cwPositionRelabelCoarseAddress depth n sigma address) =
      cwCoarseAddressSequence depth n address ∘ sigma := by
  funext sample c
  exact congrFun
    (positiveWordEquiv_position_apply sigma (address c)) sample

/-- Canonical common position permutation between two coarse addresses of the same joint type. -/
noncomputable def cwCoarsePositionPermOfSameMultiplicity
    (depth n : ℕ)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity (cwCoarseAddressSequence depth n left) =
      WordType.multiplicity (cwCoarseAddressSequence depth n right)) :
    Equiv.Perm (Fin (n + 1)) :=
  WordType.positionPermOfSameMultiplicity
    (cwCoarseAddressSequence depth n left)
    (cwCoarseAddressSequence depth n right) h

/-- The chosen common position permutation sends the right coarse address to the left one. -/
theorem cwPositionRelabelCoarseAddress_positionPermOfSameMultiplicity
    (depth n : ℕ)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity (cwCoarseAddressSequence depth n left) =
      WordType.multiplicity (cwCoarseAddressSequence depth n right)) :
    cwPositionRelabelCoarseAddress depth n
        (cwCoarsePositionPermOfSameMultiplicity depth n left right h) right = left := by
  let sigma := cwCoarsePositionPermOfSameMultiplicity depth n left right h
  have hsequence : cwCoarseAddressSequence depth n right ∘ sigma =
      cwCoarseAddressSequence depth n left := by
    exact WordType.positionPermOfSameMultiplicity_map
      (cwCoarseAddressSequence depth n left)
      (cwCoarseAddressSequence depth n right) h
  funext c
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  simpa [cwPositionRelabelCoarseAddress, cwCoarseAddressSequence,
    Function.comp_apply, sigma] using
      congrArg (fun coarse ↦ coarse c) (congrFun hsequence sample)

/-- Coarsening a fine block word commutes with a common sample-position permutation. -/
theorem cwOuterCoarseWord_positionRelabel
    (depth n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    cwOuterCoarseWord depth n
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n sigma word) =
      positiveWordPositionEquiv (CWCoarseDigit depth) n sigma
        (cwOuterCoarseWord depth n word) := by
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  rw [positiveWordEquiv_cwOuterCoarseWord,
    positiveWordEquiv_position_apply,
    positiveWordEquiv_position_apply,
    positiveWordEquiv_cwOuterCoarseWord]
  rfl

/-- Fine block labels belonging to one ideal, pre-cleanup coarse constituent. -/
noncomputable def cwIdealCoarseFiberParts (depth n : ℕ)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg) :
    Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) := by
  classical
  exact Finset.univ.filter fun fine ↦
    cwOuterCoarseWord depth n fine = coarse c

@[simp] theorem mem_cwIdealCoarseFiberParts_iff
    (depth n : ℕ)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg)
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    fine ∈ cwIdealCoarseFiberParts depth n coarse c ↔
      cwOuterCoarseWord depth n fine = coarse c := by
  classical
  simp [cwIdealCoarseFiberParts]

/-- Ideal pre-cleanup fine tensor lying over one coarse constituent address. -/
noncomputable def cwIdealCoarseFiber
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :=
  (cwSelectedExactInterfaceTerm K q term hmultiplicity).box
    (cwIdealCoarseFiberParts depth n coarse)

/-- The concrete CW exact-interface relabeling acts on block words by the advertised position
permutation. -/
@[simp] theorem cwSelectedExactInterfaceTermPositionRelabeling_partEquiv
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Equiv.Perm (Fin (n + 1))) (c : Leg) :
    (cwSelectedExactInterfaceTermPositionRelabeling
      K q term hmultiplicity sigma).partEquiv c =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n sigma := by
  unfold cwSelectedExactInterfaceTermPositionRelabeling
  exact Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
    (cwChunkPartitionedTensor K q depth) n sigma c

/-- Relabeling fine block words transports the ideal fiber parts to the correspondingly
permuted coarse address. -/
theorem relabelParts_cwIdealCoarseFiberParts
    (depth n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    relabelParts
        (fun _c ↦ positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n sigma)
        (cwIdealCoarseFiberParts depth n coarse) =
      cwIdealCoarseFiberParts depth n
        (cwPositionRelabelCoarseAddress depth n sigma coarse) := by
  classical
  funext c
  ext fine
  rw [mem_relabelParts, mem_cwIdealCoarseFiberParts_iff,
    mem_cwIdealCoarseFiberParts_iff]
  let fineEquiv := positiveWordPositionEquiv
    (PositiveWord CWBlock (2 ^ depth - 1)) n sigma
  let coarseEquiv := positiveWordPositionEquiv (CWCoarseDigit depth) n sigma
  have hequivariant (word : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
      cwOuterCoarseWord depth n (fineEquiv word) =
        coarseEquiv (cwOuterCoarseWord depth n word) := by
    exact cwOuterCoarseWord_positionRelabel depth n sigma word
  change cwOuterCoarseWord depth n (fineEquiv.symm fine) = coarse c ↔
    cwOuterCoarseWord depth n fine = coarseEquiv (coarse c)
  constructor
  · intro h
    calc
      cwOuterCoarseWord depth n fine =
          cwOuterCoarseWord depth n (fineEquiv (fineEquiv.symm fine)) := by
            rw [fineEquiv.apply_symm_apply]
      _ = coarseEquiv (cwOuterCoarseWord depth n (fineEquiv.symm fine)) :=
        hequivariant (fineEquiv.symm fine)
      _ = coarseEquiv (coarse c) := congrArg coarseEquiv h
  · intro h
    apply coarseEquiv.injective
    calc
      coarseEquiv (cwOuterCoarseWord depth n (fineEquiv.symm fine)) =
          cwOuterCoarseWord depth n (fineEquiv (fineEquiv.symm fine)) :=
        (hequivariant (fineEquiv.symm fine)).symm
      _ = cwOuterCoarseWord depth n fine := by rw [fineEquiv.apply_symm_apply]
      _ = coarseEquiv (coarse c) := h

/-- Ideal coarse fibers with the same joint multiplicity type are tensor-isomorphic.  This is
the fixed-type normalization used before interpreting compatibility deletions as holes in one
canonical child interface tensor. -/
theorem cwIdealCoarseFiber_isomorphic_of_sameJointMultiplicity
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (left right : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (h : WordType.multiplicity (cwCoarseAddressSequence depth n left) =
      WordType.multiplicity (cwCoarseAddressSequence depth n right)) :
    Isomorphic
      (cwIdealCoarseFiber K q term hmultiplicity right).realize
      (cwIdealCoarseFiber K q term hmultiplicity left).realize := by
  let sigma := cwCoarsePositionPermOfSameMultiplicity depth n left right h
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity sigma
  have hcoarse : cwPositionRelabelCoarseAddress depth n sigma right = left :=
    cwPositionRelabelCoarseAddress_positionPermOfSameMultiplicity
      depth n left right h
  have hparts : relabelParts relabeling.partEquiv
      (cwIdealCoarseFiberParts depth n right) =
        cwIdealCoarseFiberParts depth n left := by
    rw [show relabeling.partEquiv = fun _c ↦
        positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n sigma by
      funext c
      exact cwSelectedExactInterfaceTermPositionRelabeling_partEquiv
        K q term hmultiplicity sigma c]
    rw [relabelParts_cwIdealCoarseFiberParts, hcoarse]
  have hisomorphic := relabeling.box_isomorphic
    (cwIdealCoarseFiberParts depth n right)
  rw [hparts] at hisomorphic
  exact hisomorphic

/-! ## Cleaned coarse fibers as damaged ideal fibers -/

/-- A projection-closed cleanup fiber over a retained coarse address is exactly a Cartesian box
inside that address's ideal pre-cleanup coarse fiber.

The hypothesis `hgroup` is deliberately explicit: it is the paper-facing assertion that the
grouping returned by compatibility isolation is indexed by the actual coarse constituent, rather
than by an abstract copy of the index type. -/
theorem cwCleanedFiber_eq_idealCoarseFiber_box
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hcoarse : coarse ∈ coarseKept) :
    G.fiber coarse =
      (cwIdealCoarseFiber K q term hmultiplicity coarse).box
        (G.fiberParts coarse) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.LegGrouping.fiber,
      PartitionedTensor.withSupport_support,
      PartitionedTensor.LegGrouping.fiberSupport, Finset.mem_filter,
      PartitionedTensor.mem_box_support, cwIdealCoarseFiber,
      PartitionedTensor.box_box, Finset.mem_inter,
      mem_cwIdealCoarseFiberParts_iff]
    constructor
    · rintro ⟨hfinal, hG⟩
      have hambient := hclosed.1 hfinal
      have hselected : address ∈ selected.support :=
        (mem_cwFineSupportOverCoarseSupport
          selected.support coarseKept address).mp hambient |>.1
      refine ⟨hselected, fun c ↦ ⟨?_, ?_⟩⟩
      ·
        have hcoarseAddress : cwExactInterfaceCoarseGroup depth n address = coarse := by
          rw [← hgroup address]
          exact hG
        exact congrFun hcoarseAddress c
      ·
        exact (G.mem_fiberParts_iff coarse c (address c)).2
          ⟨address, hfinal, hG, rfl⟩
    · rintro ⟨hselected, hparts⟩
      have hcoarseAddress :
          cwExactInterfaceCoarseGroup depth n address = coarse := by
        funext c
        exact (hparts c).1
      have hambient : address ∈ cwFineSupportOverCoarseSupport
          selected.support coarseKept := by
        apply (mem_cwFineSupportOverCoarseSupport
          selected.support coarseKept address).mpr
        exact ⟨hselected, hcoarseAddress.symm ▸ hcoarse⟩
      have hfinal : address ∈ finalSupport := by
        apply hclosed.2 address hambient
        intro c _hc
        obtain ⟨witness, hwitness, _hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff coarse c (address c)).1 (hparts c).2
        exact ⟨witness, hwitness, hwitnessLabel.symm⟩
      refine ⟨hfinal, ?_⟩
      rw [hgroup address, hcoarseAddress]
  · rfl

/-- Every fine label occurring in a cleaned coarse fiber belongs to the corresponding ideal
coarse-fiber alphabet. -/
theorem cwCleanedFiberParts_subset_idealCoarseFiberParts
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg) :
    G.fiberParts coarse c ⊆ cwIdealCoarseFiberParts depth n coarse c := by
  classical
  intro label hlabel
  obtain ⟨address, _haddress, haddressGroup, haddressLabel⟩ :=
    (G.mem_fiberParts_iff coarse c label).1 hlabel
  apply (mem_cwIdealCoarseFiberParts_iff depth n coarse c label).2
  have hcoarseAddress : cwExactInterfaceCoarseGroup depth n address = coarse := by
    rw [← hgroup address]
    exact haddressGroup
  calc
    cwOuterCoarseWord depth n label =
        cwOuterCoarseWord depth n (address c) := by rw [haddressLabel]
    _ = cwExactInterfaceCoarseGroup depth n address c := rfl
    _ = coarse c := congrFun hcoarseAddress c

/-- Restriction-facing form of a cleaned coarse fiber before canonical type transport: it is the
box of exactly its surviving fine labels in the original selected interface tensor. -/
theorem cwCleanedFiber_eq_selected_box_fiberParts
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hcoarse : coarse ∈ coarseKept) :
    G.fiber coarse =
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).box
        (G.fiberParts coarse) := by
  rw [cwCleanedFiber_eq_idealCoarseFiber_box K q term hmultiplicity
    coarseKept finalSupport hclosed G hgroup coarse hcoarse,
    cwIdealCoarseFiber, PartitionedTensor.box_box]
  congr 1
  funext c
  exact Finset.inter_eq_right.mpr
    (cwCleanedFiberParts_subset_idealCoarseFiberParts
      K q term hmultiplicity finalSupport G hgroup coarse c)

/-- Surviving fine labels transported from one coarse constituent to a fixed same-type reference
constituent. -/
noncomputable def cwMovedCleanedFiberParts
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse)) :
    ∀ _c : Leg, Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :=
  let sigma := cwCoarsePositionPermOfSameMultiplicity
    depth n reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity sigma
  relabelParts relabeling.partEquiv (G.fiberParts coarse)

/-- After same-type position transport, the surviving labels lie in the reference ideal
coarse-fiber alphabet. -/
theorem cwMovedCleanedFiberParts_subset_reference
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse))
    (c : Leg) :
    cwMovedCleanedFiberParts K q term hmultiplicity G reference coarse hsame c ⊆
      cwIdealCoarseFiberParts depth n reference c := by
  classical
  let sigma := cwCoarsePositionPermOfSameMultiplicity
    depth n reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity sigma
  have hcoarse : cwPositionRelabelCoarseAddress depth n sigma coarse = reference :=
    cwPositionRelabelCoarseAddress_positionPermOfSameMultiplicity
      depth n reference coarse hsame
  have hideal : relabelParts relabeling.partEquiv
      (cwIdealCoarseFiberParts depth n coarse) =
        cwIdealCoarseFiberParts depth n reference := by
    rw [show relabeling.partEquiv = fun _c ↦
        positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n sigma by
      funext d
      exact cwSelectedExactInterfaceTermPositionRelabeling_partEquiv
        K q term hmultiplicity sigma d]
    rw [relabelParts_cwIdealCoarseFiberParts, hcoarse]
  intro label hlabel
  change label ∈ relabelParts relabeling.partEquiv (G.fiberParts coarse) c at hlabel
  rw [← congrFun hideal c, mem_relabelParts] at ⊢
  rw [mem_relabelParts] at hlabel
  exact cwCleanedFiberParts_subset_idealCoarseFiberParts
    K q term hmultiplicity finalSupport G hgroup coarse c hlabel

/-- Central fixed-type semantic adapter: a cleaned fiber over `coarse` restricts to a damaged box
of one compact, honestly-sized ideal fiber over `reference` whenever the two coarse words have the
same joint type. -/
theorem cwCleanedFiber_restricts_compactReferenceBox
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hcoarse : coarse ∈ coarseKept)
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse)) :
    Restricts (G.fiber coarse).realize
      ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwIdealCoarseFiberParts depth n reference)).box
        (compactBoxSubparts
          (cwIdealCoarseFiberParts depth n reference)
          (cwMovedCleanedFiberParts
            K q term hmultiplicity G reference coarse hsame))).realize := by
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let sigma := cwCoarsePositionPermOfSameMultiplicity
    depth n reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity sigma
  let moved := cwMovedCleanedFiberParts
    K q term hmultiplicity G reference coarse hsame
  have hfiber : G.fiber coarse = selected.box (G.fiberParts coarse) :=
    cwCleanedFiber_eq_selected_box_fiberParts K q term hmultiplicity
      coarseKept finalSupport hclosed G hgroup coarse hcoarse
  have hrelabel : Isomorphic (selected.box (G.fiberParts coarse)).realize
      (selected.box moved).realize := by
    simpa [moved, cwMovedCleanedFiberParts, sigma, relabeling] using
      relabeling.box_isomorphic (G.fiberParts coarse)
  have hsubset : ∀ c,
      moved c ⊆ cwIdealCoarseFiberParts depth n reference c := by
    intro c
    simpa [moved] using cwMovedCleanedFiberParts_subset_reference
      K q term hmultiplicity G hgroup reference coarse hsame c
  exact (Restricts.of_eq (congrArg PartitionedTensor.realize hfiber)).trans
    (hrelabel.restricts.trans
      (Restricts.box_to_compactBox_box selected
        (cwIdealCoarseFiberParts depth n reference) moved hsubset))

/-- Canonical compact holes of one cleaned fixed-type fiber. -/
noncomputable def cwFixedTypeCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse))
    (c : Leg) : Finset (BoxPart (cwIdealCoarseFiberParts depth n reference) c) :=
  Finset.univ \ compactBoxSubparts
    (cwIdealCoarseFiberParts depth n reference)
    (cwMovedCleanedFiberParts
      K q term hmultiplicity G reference coarse hsame) c

@[simp] theorem univ_sdiff_cwFixedTypeCleanedFiberHoles
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse))
    (c : Leg) :
    Finset.univ \ cwFixedTypeCleanedFiberHoles
        K q term hmultiplicity G reference coarse hsame c =
      compactBoxSubparts
        (cwIdealCoarseFiberParts depth n reference)
        (cwMovedCleanedFiberParts
          K q term hmultiplicity G reference coarse hsame) c := by
  classical
  apply Finset.sdiff_sdiff_eq_self
  exact Finset.subset_univ _

/-- A retained finite family of coarse constituents of one joint type is now a genuine
`ModeledFiberFamily` over one common compact ideal tensor.  Consequently the generic varying-hole
repair theorem applies directly; its only numerical input is the cardinality of the sparse
indices of this model. -/
noncomputable def cwFixedTypeCleanedModeledFiberFamily
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coarseAt : Index → BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (hcoarseAt : ∀ i, coarseAt i ∈ coarseKept)
    (hsameAt : ∀ i,
      WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
        WordType.multiplicity (cwCoarseAddressSequence depth n (coarseAt i))) :
    HoleRepair.ModeledFiberFamily
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwIdealCoarseFiberParts depth n reference))
      (fun i ↦ (G.fiber (coarseAt i)).realize) where
  holes i := cwFixedTypeCleanedFiberHoles
    K q term hmultiplicity G reference (coarseAt i) (hsameAt i)
  fiber_restricts i := by
    have h := cwCleanedFiber_restricts_compactReferenceBox
      K q term hmultiplicity coarseKept finalSupport hclosed G hgroup
        reference (coarseAt i) (hcoarseAt i) (hsameAt i)
    simpa only [univ_sdiff_cwFixedTypeCleanedFiberHoles] using h

end AlgebraicComplexity.Examples
