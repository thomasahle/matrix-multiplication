/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalFeatureTypeCountingGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCompetitorClassification

set_option autoImplicit false

/-!
# Visible-feature competitor counting for the CW total-weight quotient

Compatibility fixes the empirical profile of the pivot word against the compatibility cell of
the tested quotient atom.  It does not fix the complete joint type of the tested atom.  This file
therefore counts competitors in the correct order:

1. recover the complete tagged supported atom word, so the encoding remains injective;
2. expose only its `Y`- or `Z`-compatibility cell as the counted feature;
3. inject every competitor into the resulting conditional visible-feature class; and
4. leave the hidden full joint type to the generic polynomial-union/maximum-entropy theorem.

This removes the full-joint-type premise of the exact pushed-profile encodings.  The latter remain
useful when a certificate really does prescribe one full joint type, but are not required for the
quotient version of the compatibility count.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## Finite compatibility-cell features -/

/-- Coarse constituent index carried by one complete tagged total-weight atom. -/
def cwTotalWeightTaggedAtomCoarseIndex
    {depth : ℕ} {Part : Type}
    (atom : CWTotalWeightTaggedAtom depth Part) : CoarseIndex Part where
  part := atom.1
  x := atom.2 .X
  y := atom.2 .Y
  z := atom.2 .Z

/-- The recovered atom-level index agrees with the concrete feature model at every sample. -/
theorem cwTotalWeightTaggedAtomCoarseIndex_atomWord
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (sample : Fin (n + 1)) :
    cwTotalWeightTaggedAtomCoarseIndex
        (cwTotalWeightTaggedAtomWord K q depth n partAt address haddress sample) =
      (cwTotalWeightFeatureCompatibilityModel depth n partAt).coarse address sample := by
  have hx := cwTotalWeightTaggedAtomWord_address_apply
    K q depth n partAt address haddress sample .X
  have hy := cwTotalWeightTaggedAtomWord_address_apply
    K q depth n partAt address haddress sample .Y
  have hz := cwTotalWeightTaggedAtomWord_address_apply
    K q depth n partAt address haddress sample .Z
  change CoarseIndex.mk (partAt sample)
      ((cwTotalWeightTaggedAtomWord K q depth n partAt address haddress sample).2 .X)
      ((cwTotalWeightTaggedAtomWord K q depth n partAt address haddress sample).2 .Y)
      ((cwTotalWeightTaggedAtomWord K q depth n partAt address haddress sample).2 .Z) =
    CoarseIndex.mk (partAt sample)
      (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample)
      (positiveWordEquiv (CWCoarseDigit depth) n (address .Y) sample)
      (positiveWordEquiv (CWCoarseDigit depth) n (address .Z) sample)
  rw [hx, hy, hz]

/-- The `Y` compatibility-cell feature of a complete tagged total-weight atom. -/
def cwTotalWeightYCellOfTaggedAtom
    (depth : ℕ) {Part : Type} [DecidableEq Part] :
    CWTotalWeightTaggedAtom depth Part → YCompatibilityCell Part :=
  yCompatibilityCell ∘ cwTotalWeightTaggedAtomCoarseIndex

/-- The `Z` compatibility-cell feature of a complete tagged total-weight atom. -/
def cwTotalWeightZCellOfTaggedAtom
    (depth : ℕ) {Part : Type} [DecidableEq Part] :
    CWTotalWeightTaggedAtom depth Part → ZCompatibilityCell Part :=
  zCompatibilityCell ∘ cwTotalWeightTaggedAtomCoarseIndex

/-- Finite alphabet of `Y` cells actually realized by tagged total-weight atoms. -/
noncomputable def cwTotalWeightYCellAlphabet
    (depth : ℕ) (Part : Type) [Fintype Part] [DecidableEq Part] :
    Finset (YCompatibilityCell Part) := by
  classical
  exact Finset.univ.image (cwTotalWeightYCellOfTaggedAtom depth)

/-- Finite subtype of realized total-weight `Y` cells. -/
abbrev CWTotalWeightYCell
    (depth : ℕ) (Part : Type) [Fintype Part] [DecidableEq Part] :=
  {cell // cell ∈ cwTotalWeightYCellAlphabet depth Part}

/-- Canonical finite `Y`-cell feature of every tagged atom. -/
noncomputable def cwTotalWeightYFiniteCellOfTaggedAtom
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (atom : CWTotalWeightTaggedAtom depth Part) :
    CWTotalWeightYCell depth Part := by
  classical
  exact ⟨cwTotalWeightYCellOfTaggedAtom depth atom,
    Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, rfl⟩⟩

/-- Finite alphabet of `Z` cells actually realized by tagged total-weight atoms. -/
noncomputable def cwTotalWeightZCellAlphabet
    (depth : ℕ) (Part : Type) [Fintype Part] [DecidableEq Part] :
    Finset (ZCompatibilityCell Part) := by
  classical
  exact Finset.univ.image (cwTotalWeightZCellOfTaggedAtom depth)

/-- Finite subtype of realized total-weight `Z` cells. -/
abbrev CWTotalWeightZCell
    (depth : ℕ) (Part : Type) [Fintype Part] [DecidableEq Part] :=
  {cell // cell ∈ cwTotalWeightZCellAlphabet depth Part}

/-- Canonical finite `Z`-cell feature of every tagged atom. -/
noncomputable def cwTotalWeightZFiniteCellOfTaggedAtom
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (atom : CWTotalWeightTaggedAtom depth Part) :
    CWTotalWeightZCell depth Part := by
  classical
  exact ⟨cwTotalWeightZCellOfTaggedAtom depth atom,
    Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, rfl⟩⟩

/-! ## Evaluator-visible joint profiles -/

/-- Joint `(fixed symbol, Y-cell)` profile prescribed by the quotient evaluator. -/
noncomputable def cwTotalWeightYEvaluatorJointType
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth) :
    CWCoarseDigit depth × CWTotalWeightYCell depth Part → ℕ :=
  fun pair ↦
    (cwTotalWeightPushforwardTargets rawTargets).yCellProfile pair.2.1 pair.1

/-- Joint `(fixed symbol, Z-cell)` profile prescribed by the quotient evaluator. -/
noncomputable def cwTotalWeightZEvaluatorJointType
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth) :
    CWCoarseDigit depth × CWTotalWeightZCell depth Part → ℕ :=
  fun pair ↦
    (cwTotalWeightPushforwardTargets rawTargets).zCellProfile pair.2.1 pair.1

private theorem cwTotalWeight_multiplicity_jointWord_eq_cellMultiplicity
    {samples : ℕ} {Symbol Cell : Type*}
    [Fintype Symbol] [DecidableEq Symbol] [Fintype Cell] [DecidableEq Cell]
    (symbols : Fin samples → Symbol) (cells : Fin samples → Cell)
    (symbol : Symbol) (cell : Cell) :
    WordType.multiplicity (WordType.jointWord symbols cells) (symbol, cell) =
      cellMultiplicity cells symbols cell symbol := by
  classical
  unfold WordType.multiplicity WordType.jointWord cellMultiplicity
  congr 1
  ext sample
  simp [Prod.ext_iff, and_comm]

private theorem cwTotalWeight_cellMultiplicity_subtype_val
    {samples : ℕ} {Cell Symbol : Type*}
    [DecidableEq Cell] [DecidableEq Symbol]
    {cells : Finset Cell} (cellWord : Fin samples → {cell // cell ∈ cells})
    (symbols : Fin samples → Symbol) (cell : {cell // cell ∈ cells})
    (symbol : Symbol) :
    cellMultiplicity cellWord symbols cell symbol =
      cellMultiplicity (fun sample ↦ (cellWord sample).1) symbols cell.1 symbol := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp

/-! ## Exact competitor injections -/

/-- Full tagged quotient-atom words having the visible `Y` profile required by compatibility. -/
noncomputable def cwTotalWeightYCompetitorFeatureClass
    (depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (label : PositiveWord (CWCoarseDigit depth) n) :
    Finset (Fin (n + 1) → CWTotalWeightTaggedAtom depth Part) :=
  WordType.conditionalFeatureTypeClass
    (positiveWordEquiv (CWCoarseDigit depth) n label)
    (cwTotalWeightYFiniteCellOfTaggedAtom depth)
    (cwTotalWeightYEvaluatorJointType depth rawTargets)

/-- Full tagged quotient-atom words having the visible `Z` profile required by compatibility. -/
noncomputable def cwTotalWeightZCompetitorFeatureClass
    (depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (label : PositiveWord (CWCoarseDigit depth) n) :
    Finset (Fin (n + 1) → CWTotalWeightTaggedAtom depth Part) :=
  WordType.conditionalFeatureTypeClass
    (positiveWordEquiv (CWCoarseDigit depth) n label)
    (cwTotalWeightZFiniteCellOfTaggedAtom depth)
    (cwTotalWeightZEvaluatorJointType depth rawTargets)

/-- Every total-weight `Y` competitor injects into the exact visible-feature class dictated by
the compatibility equations.  No full hidden joint type is assumed. -/
theorem cwTotalWeight_card_compatibilityCompetitorsY_le_featureClass
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    (compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets) address).card ≤
      (cwTotalWeightYCompetitorFeatureClass depth n rawTargets (address .Y)).card := by
  classical
  let competitors := compatibilityCompetitors ambient .Y
    (cwTotalWeightCompatibilityY depth n partAt rawTargets) address
  let targetClass := cwTotalWeightYCompetitorFeatureClass
    depth n rawTargets (address .Y)
  let refinement : {other // other ∈ competitors} →
      Fin (n + 1) → CWTotalWeightTaggedAtom depth Part := fun other ↦
    cwTotalWeightTaggedAtomWord K q depth n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address other.1).1 other.2).1))
  have hrefinement_mem (other : {other // other ∈ competitors}) :
      refinement other ∈ targetClass := by
    have hmem := (mem_compatibilityCompetitors ambient .Y
      (cwTotalWeightCompatibilityY depth n partAt rawTargets)
      address other.1).1 other.2
    have hcompatible := hmem.2.2
    change refinement other ∈
      WordType.conditionalFeatureTypeClass
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Y))
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
    rw [WordType.mem_conditionalFeatureTypeClass]
    funext pair
    obtain ⟨symbol, cell⟩ := pair
    rw [cwTotalWeight_multiplicity_jointWord_eq_cellMultiplicity,
      cwTotalWeight_cellMultiplicity_subtype_val]
    have hcells :
        (fun sample ↦
          ((cwTotalWeightYFiniteCellOfTaggedAtom depth ∘ refinement other) sample).1) =
        (fun sample ↦ yCompatibilityCell
          ((cwTotalWeightFeatureCompatibilityModel depth n partAt).coarse
            other.1 sample)) := by
      funext sample
      change yCompatibilityCell
          (cwTotalWeightTaggedAtomCoarseIndex
            (cwTotalWeightTaggedAtomWord K q depth n partAt other.1
              (hambient hmem.1) sample)) = _
      rw [cwTotalWeightTaggedAtomCoarseIndex_atomWord]
    rw [hcells]
    exact hcompatible cell.1 symbol
  let f : {other // other ∈ competitors} → {word // word ∈ targetClass} :=
    fun other ↦ ⟨refinement other, hrefinement_mem other⟩
  have hf : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply cwTotalWeightTaggedAtomWord_injective K q depth n partAt
      (hambient ((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address left.1).1 left.2).1)
      (hambient ((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address right.1).1 right.2).1)
    exact congrArg Subtype.val h
  simpa only [competitors, targetClass, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Every total-weight `Z` competitor injects into its exact visible-feature class. -/
theorem cwTotalWeight_card_compatibilityCompetitorsZ_le_featureClass
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    (compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets) address).card ≤
      (cwTotalWeightZCompetitorFeatureClass depth n rawTargets (address .Z)).card := by
  classical
  let competitors := compatibilityCompetitors ambient .Z
    (cwTotalWeightCompatibilityZ depth n partAt rawTargets) address
  let targetClass := cwTotalWeightZCompetitorFeatureClass
    depth n rawTargets (address .Z)
  let refinement : {other // other ∈ competitors} →
      Fin (n + 1) → CWTotalWeightTaggedAtom depth Part := fun other ↦
    cwTotalWeightTaggedAtomWord K q depth n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address other.1).1 other.2).1))
  have hrefinement_mem (other : {other // other ∈ competitors}) :
      refinement other ∈ targetClass := by
    have hmem := (mem_compatibilityCompetitors ambient .Z
      (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
      address other.1).1 other.2
    have hcompatible := hmem.2.2
    change refinement other ∈
      WordType.conditionalFeatureTypeClass
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Z))
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
    rw [WordType.mem_conditionalFeatureTypeClass]
    funext pair
    obtain ⟨symbol, cell⟩ := pair
    rw [cwTotalWeight_multiplicity_jointWord_eq_cellMultiplicity,
      cwTotalWeight_cellMultiplicity_subtype_val]
    have hcells :
        (fun sample ↦
          ((cwTotalWeightZFiniteCellOfTaggedAtom depth ∘ refinement other) sample).1) =
        (fun sample ↦ zCompatibilityCell
          ((cwTotalWeightFeatureCompatibilityModel depth n partAt).coarse
            other.1 sample)) := by
      funext sample
      change zCompatibilityCell
          (cwTotalWeightTaggedAtomCoarseIndex
            (cwTotalWeightTaggedAtomWord K q depth n partAt other.1
              (hambient hmem.1) sample)) = _
      rw [cwTotalWeightTaggedAtomCoarseIndex_atomWord]
    rw [hcells]
    exact hcompatible cell.1 symbol
  let f : {other // other ∈ competitors} → {word // word ∈ targetClass} :=
    fun other ↦ ⟨refinement other, hrefinement_mem other⟩
  have hf : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply cwTotalWeightTaggedAtomWord_injective K q depth n partAt
      (hambient ((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address left.1).1 left.2).1)
      (hambient ((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address right.1).1 right.2).1)
    exact congrArg Subtype.val h
  simpa only [competitors, targetClass, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-! ## Exact aggregate cleanup count -/

/-- The exact no-hole cleanup count with no assumed full competitor type.  Each directed
competitor incidence is bounded by a concrete visible-feature class, whose hidden full types can
then be handled by the generic maximum-entropy theorem. -/
theorem cwTotalWeight_card_ambient_le_card_YZIsolatedSupport_add_featureTypeCounts
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    ambient.card ≤
      (cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient).card +
        (∑ address ∈ ambient,
          (cwTotalWeightYCompetitorFeatureClass
            depth n rawTargets (address .Y)).card) +
        (∑ address ∈ cwTotalWeightYIsolatedSupport
            depth n partAt rawTargets ambient,
          (cwTotalWeightZCompetitorFeatureClass
            depth n rawTargets (address .Z)).card) := by
  have hbase := cwTotalWeight_card_ambient_le_card_YZIsolatedSupport_add_incidences
    depth n partAt rawTargets ambient
  refine hbase.trans ?_
  unfold cwTotalWeightYCompetitorIncidence cwTotalWeightZCompetitorIncidence
    compatibilityCompetitorIncidence
  gcongr with address haddress
  · exact cwTotalWeight_card_compatibilityCompetitorsY_le_featureClass
      K q depth n partAt rawTargets ambient hambient address
  · exact cwTotalWeight_card_compatibilityCompetitorsZ_le_featureClass
      K q depth n partAt rawTargets
      (cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient)
      ((compatibilityIsolatedSupport_subset ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)).trans hambient)
      address

end AlgebraicComplexity.Examples
