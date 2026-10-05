/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFiberNormalization

/-!
# Exact-profile CW coarse fibers

The coarse preimage of a constituent contains fine words of many complete-split types.  It is a
valid structural box, but it is too large for the transitive relabeling and hole-density argument.
This module intersects that coarse preimage with the exact leg profile already selected by the
interface term.  Cleaned fixed-type fibers restrict to damaged boxes of this smaller, faithful
conditional type class.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Fine block labels in one coarse constituent which also have the exact complete-split profile
prescribed by the selected interface term. -/
noncomputable def cwExactProfileCoarseFiberParts
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg) :
    Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) := by
  classical
  exact Finset.univ.filter fun fine ↦
    cwOuterCoarseWord depth n fine = coarse c ∧
      (term.positivePowerProfile hmultiplicity c).MatchesEncodedPositiveWord
        (cwChunkSplitWord depth) fine

@[simp] theorem mem_cwExactProfileCoarseFiberParts_iff
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg)
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    fine ∈ cwExactProfileCoarseFiberParts term hmultiplicity coarse c ↔
      cwOuterCoarseWord depth n fine = coarse c ∧
        (term.positivePowerProfile hmultiplicity c).MatchesEncodedPositiveWord
          (cwChunkSplitWord depth) fine := by
  classical
  simp [cwExactProfileCoarseFiberParts]

/-- The profile-consistent conditional alphabet is a subfamily of the broad coarse preimage. -/
theorem cwExactProfileCoarseFiberParts_subset_ideal
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg) :
    cwExactProfileCoarseFiberParts term hmultiplicity coarse c ⊆
      cwIdealCoarseFiberParts depth n coarse c := by
  intro fine hfine
  exact (mem_cwIdealCoarseFiberParts_iff depth n coarse c fine).2
    ((mem_cwExactProfileCoarseFiberParts_iff
      term hmultiplicity coarse c fine).1 hfine).1

/-- Every label occurring in a cleaned fiber still has the exact profile selected in the source
interface tensor. -/
theorem cwCleanedFiberParts_matchesExactProfile
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
    (coarse : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (c : Leg)
    {fine : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n}
    (hfine : fine ∈ G.fiberParts coarse c) :
    (term.positivePowerProfile hmultiplicity c).MatchesEncodedPositiveWord
      (cwChunkSplitWord depth) fine := by
  obtain ⟨address, haddress, _hgroup, hlabel⟩ :=
    (G.mem_fiberParts_iff coarse c fine).1 hfine
  have hfinal : address ∈ finalSupport := haddress
  have hambient := hclosed.1 hfinal
  have hselected := (mem_cwFineSupportOverCoarseSupport
    (cwSelectedExactInterfaceTerm K q term hmultiplicity).support
      coarseKept address).1 hambient |>.1
  change address ∈
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun d ↦ term.positivePowerProfile hmultiplicity d)).support at hselected
  have hdata :=
    ((cwChunkPartitionedTensor K q depth).mem_selectEncodedCompleteSplitProfiles_support
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun d ↦ term.positivePowerProfile hmultiplicity d) address).1
        hselected
  have hconsistent := hdata.2 c
  subst fine
  exact (CompleteSplitProfile.matchesEncodedPositiveWord_iff
    (term.positivePowerProfile hmultiplicity c)
      (cwChunkSplitWord depth) (address c)).2 hconsistent

/-- After transporting a same-joint-type cleaned fiber to the reference coarse address, every
surviving label belongs to the exact conditional type class, not merely the broad coarse
preimage. -/
theorem cwMovedCleanedFiberParts_subset_exactProfileReference
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
    (hsame : WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse))
    (c : Leg) :
    cwMovedCleanedFiberParts K q term hmultiplicity G reference coarse hsame c ⊆
      cwExactProfileCoarseFiberParts term hmultiplicity reference c := by
  classical
  let sigma := cwCoarsePositionPermOfSameMultiplicity
    depth n reference coarse hsame
  let relabeling := cwSelectedExactInterfaceTermPositionRelabeling
    K q term hmultiplicity sigma
  intro fine hfine
  have hcoarse : fine ∈ cwIdealCoarseFiberParts depth n reference c :=
    cwMovedCleanedFiberParts_subset_reference
      K q term hmultiplicity G hgroup reference coarse hsame c hfine
  have horiginal : (relabeling.partEquiv c).symm fine ∈ G.fiberParts coarse c := by
    simpa [cwMovedCleanedFiberParts, sigma, relabeling] using hfine
  have hprofileOriginal := cwCleanedFiberParts_matchesExactProfile
    K q term hmultiplicity coarseKept finalSupport hclosed G coarse c horiginal
  have hpartEquiv : relabeling.partEquiv c =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ depth - 1)) n sigma :=
    cwSelectedExactInterfaceTermPositionRelabeling_partEquiv
      K q term hmultiplicity sigma c
  have hprofile :
      (term.positivePowerProfile hmultiplicity c).MatchesEncodedPositiveWord
        (cwChunkSplitWord depth) fine := by
    have hinvariant :=
      (CompleteSplitProfile.matchesEncodedPositiveWord_positionEquiv_iff
        (term.positivePowerProfile hmultiplicity c)
        (cwChunkSplitWord depth) ((relabeling.partEquiv c).symm fine) sigma).2
          hprofileOriginal
    rw [hpartEquiv] at hinvariant
    simpa using hinvariant
  exact (mem_cwExactProfileCoarseFiberParts_iff
    term hmultiplicity reference c fine).2
      ⟨(mem_cwIdealCoarseFiberParts_iff depth n reference c fine).1 hcoarse,
        hprofile⟩

/-- Faithful fixed-type semantic adapter: the cleaned fiber restricts to a damaged box whose
part types are the exact profile-consistent conditional classes over the reference constituent. -/
theorem cwCleanedFiber_restricts_compactExactProfileReferenceBox
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
          (cwExactProfileCoarseFiberParts term hmultiplicity reference)).box
        (compactBoxSubparts
          (cwExactProfileCoarseFiberParts term hmultiplicity reference)
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
      moved c ⊆ cwExactProfileCoarseFiberParts term hmultiplicity reference c := by
    intro c
    simpa [moved] using cwMovedCleanedFiberParts_subset_exactProfileReference
      K q term hmultiplicity coarseKept finalSupport hclosed G hgroup
        reference coarse hsame c
  exact (Restricts.of_eq (congrArg PartitionedTensor.realize hfiber)).trans
    (hrelabel.restricts.trans
      (Restricts.box_to_compactBox_box selected
        (cwExactProfileCoarseFiberParts term hmultiplicity reference) moved hsubset))

/-- Missing exact-profile parts in one transported cleaned fiber. -/
noncomputable def cwExactProfileCleanedFiberHoles
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
    Finset (BoxPart
      (cwExactProfileCoarseFiberParts term hmultiplicity reference) c) :=
  Finset.univ \ compactBoxSubparts
    (cwExactProfileCoarseFiberParts term hmultiplicity reference)
    (cwMovedCleanedFiberParts
      K q term hmultiplicity G reference coarse hsame) c

@[simp] theorem univ_sdiff_cwExactProfileCleanedFiberHoles
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
    Finset.univ \ cwExactProfileCleanedFiberHoles
        K q term hmultiplicity G reference coarse hsame c =
      compactBoxSubparts
        (cwExactProfileCoarseFiberParts term hmultiplicity reference)
        (cwMovedCleanedFiberParts
          K q term hmultiplicity G reference coarse hsame) c := by
  classical
  apply Finset.sdiff_sdiff_eq_self
  exact Finset.subset_univ _

/-- A retained same-joint-type family modeled over the faithful exact-profile compact tensor. -/
noncomputable def cwExactProfileCleanedModeledFiberFamily
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
        (cwExactProfileCoarseFiberParts term hmultiplicity reference))
      (fun i ↦ (G.fiber (coarseAt i)).realize) where
  holes i := cwExactProfileCleanedFiberHoles
    K q term hmultiplicity G reference (coarseAt i) (hsameAt i)
  fiber_restricts i := by
    have h := cwCleanedFiber_restricts_compactExactProfileReferenceBox
      K q term hmultiplicity coarseKept finalSupport hclosed G hgroup
        reference (coarseAt i) (hcoarseAt i) (hsameAt i)
    simpa only [univ_sdiff_cwExactProfileCleanedFiberHoles] using h

end AlgebraicComplexity.Examples
