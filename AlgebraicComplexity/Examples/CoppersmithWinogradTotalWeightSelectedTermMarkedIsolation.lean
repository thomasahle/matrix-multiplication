/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseExtraction
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionExtraction

/-!
# Marked coarse isolation on a selected CW interface term

Marked affine hashing is performed on the coarse total-weight words of an exact-interface term,
while a division leaf retains the underlying fine complete-split words.  The independent hash
filter must therefore be pulled back to fine labels before coarse-group isolation is used.

This file supplies the two exact client facts for that order.  First, the selected fine term
restricts to the full fine preimage of the actually present hash-filtered coarse support.  Second,
the present marked `X/Y`-isolated support has its coarse group readable from the fine `X` label
inside that filtered fine ambient.  In particular, the second theorem deliberately does not claim
group readability inside the unfiltered selected support.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

noncomputable section

/-- Pulling the independent coarse hash filter back along the total-weight coarsening is a genuine
fine-label zero-out of the selected exact-interface term. -/
theorem cwSelectedExactInterfaceTerm_restricts_presentHashFilteredFine
    {R : Type v} [Field R]
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (hmodeled :
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support ⊆
        H.modeledAddresses n (H.legalTargets n ambientWords)) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let coarse := cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity
    let filteredCoarse :=
      H.presentHashFilteredPowerAddresses ambientWords B seed coarse
    let filteredFine :=
      cwFineSupportOverCoarseSupport selected.support filteredCoarse
    Restricts selected.realize (selected.withSupport filteredFine).realize := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let coarse := cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity
  let fineKeep : ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n → Prop :=
    fun c word ↦ H.hashKeepBlock n B seed c (cwOuterCoarseWord depth n word)
  let filteredCoarse :=
    H.presentHashFilteredPowerAddresses ambientWords B seed coarse
  let filteredFine :=
    cwFineSupportOverCoarseSupport selected.support filteredCoarse
  have hsupport : (selected.select fineKeep).support = filteredFine := by
    ext address
    constructor
    · intro haddress
      have hdata := (PartitionedTensor.mem_select_support
        selected fineKeep address).mp haddress
      apply (mem_cwFineSupportOverCoarseSupport
        selected.support filteredCoarse address).mpr
      refine ⟨hdata.1, ?_⟩
      apply Finset.mem_inter.mpr
      let source : {address // address ∈ selected.support} := ⟨address, hdata.1⟩
      have hcoarse : cwExactInterfaceCoarseGroup depth n address ∈ coarse.support := by
        simpa [coarse, source] using
          (cwCoarseSourceOfFine K q term hmultiplicity source).2
      refine ⟨hcoarse, ?_⟩
      rw [← H.filter_modeledAddresses_hashKeepBlock_eq n ambientWords B seed]
      apply Finset.mem_filter.mpr
      refine ⟨hmodeled hcoarse, ?_⟩
      intro c
      simpa [fineKeep, cwExactInterfaceCoarseGroup_apply] using hdata.2 c
    · intro haddress
      have hdata := (mem_cwFineSupportOverCoarseSupport
        selected.support filteredCoarse address).mp haddress
      apply (PartitionedTensor.mem_select_support
        selected fineKeep address).mpr
      refine ⟨hdata.1, ?_⟩
      have hfiltered : cwExactInterfaceCoarseGroup depth n address ∈
          H.filteredPowerAddresses n ambientWords B seed :=
        (Finset.mem_inter.mp hdata.2).2
      rw [← H.filter_modeledAddresses_hashKeepBlock_eq n ambientWords B seed] at hfiltered
      have hkeep := (Finset.mem_filter.mp hfiltered).2
      intro c
      simpa [fineKeep, cwExactInterfaceCoarseGroup_apply] using hkeep c
  have hselect : Restricts selected.realize (selected.select fineKeep).realize :=
    Tensor.Restricts.partitionedSelect selected fineKeep
  exact hselect.trans (Restricts.of_eq (by
    apply PartitionedTensor.realize_eq_of_support_eq
    · exact hsupport
    · intro address _haddress
      rfl))

/-- Present marked `X/Y` isolation makes the coarse address readable from the fine `X` label, once
the ambient has first been restricted by the independent hash filter. -/
theorem cwSelectedExactInterfaceTerm_presentMarkedXYIsolatedFine_hasGroupUniqueLegFibers
    {R : Type v} [Field R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let coarse := cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity
    let filteredCoarse :=
      H.presentHashFilteredPowerAddresses ambientWords B seed coarse
    let coarseKept := H.presentMarkedXYIsolatedPowerAddresses
      ambientWords markedWords B seed coarse
    let filteredFine :=
      cwFineSupportOverCoarseSupport selected.support filteredCoarse
    let isolatedFine :=
      cwFineSupportOverCoarseSupport selected.support coarseKept
    HasGroupUniqueLegFibers filteredFine isolatedFine
      (cwExactInterfaceCoarseGroup depth n) .X := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let coarse := cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity
  let filteredCoarse :=
    H.presentHashFilteredPowerAddresses ambientWords B seed coarse
  let coarseKept := H.presentMarkedXYIsolatedPowerAddresses
    ambientWords markedWords B seed coarse
  let filteredFine :=
    cwFineSupportOverCoarseSupport selected.support filteredCoarse
  let isolatedFine :=
    cwFineSupportOverCoarseSupport selected.support coarseKept
  have hcoarseUnique : HasUniqueLegFibers filteredCoarse coarseKept .X := by
    simpa [filteredCoarse, coarseKept] using
      H.presentMarkedXYIsolatedPowerAddresses_hasUniqueXFibers
        ambientWords markedWords hwords B hB seed coarse
  refine ⟨?_, ?_⟩
  · intro address haddress
    have hdata := (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept address).mp haddress
    apply (mem_cwFineSupportOverCoarseSupport
      selected.support filteredCoarse address).mpr
    exact ⟨hdata.1, hcoarseUnique.1 hdata.2⟩
  · intro kept hkept other hother hlabel
    have hkeptData := (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept kept).mp hkept
    have hotherData := (mem_cwFineSupportOverCoarseSupport
      selected.support filteredCoarse other).mp hother
    apply hcoarseUnique.2
      (cwExactInterfaceCoarseGroup depth n kept) hkeptData.2
      (cwExactInterfaceCoarseGroup depth n other) hotherData.2
    change cwOuterCoarseWord depth n (other .X) =
      cwOuterCoarseWord depth n (kept .X)
    rw [hlabel]

end

end AlgebraicComplexity.Examples
