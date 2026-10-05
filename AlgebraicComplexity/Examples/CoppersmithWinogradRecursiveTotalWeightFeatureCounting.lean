/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MarkedCompatibilityHashingIsolation
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTotalWeightHashRelation
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightFeatureCompetitorCounting

set_option autoImplicit false

/-!
# Visible-feature counts on the relaxed recursive CW family

The relaxed recursive hash family is indexed by abstract ordered child-shape words, not by fine
tensor preimages.  Each ambient legal target nevertheless determines a unique complete doubled
coarse address.  Reading that address occurrence by occurrence gives a word over the existing
finite alphabet of tagged total-weight atoms.

This module proves that the recovered tagged word is injective in the ambient target and that
coarse-semantic logical-`Z` competitors lie in the evaluator's exact conditional visible-feature
class.  Consequently the affine collision-proxy family is bounded by that class.  The sample
index remains literally `Fin ((n+1)+(n+1))`; no positive-word reindexing and no fine-preimage
union is used.

All results are finite.  Entropy bounds, asymptotics, tensor restrictions, and certificate data
remain downstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Complete finite tagged total-weight atom word recovered from one relaxed ambient target. -/
noncomputable def cwRecursiveTotalWeightTaggedAtomWord
    {R : Type v} [Field R] {Part : Type} {depth n : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha) :
    Fin ((n + 1) + (n + 1)) → CWTotalWeightTaggedAtom depth Part :=
  cwRecursiveOrientedFiniteCellSequence depth n partAt sigma
    (cwRecursiveTotalWeightCoarseOfAmbientTarget
      encoding term sigma alpha target htarget)

/-- The complete tagged atom at an occurrence has exactly the coarse index read by the doubled
feature model. -/
@[simp] theorem cwTotalWeightTaggedAtomCoarseIndex_recursiveTaggedAtomWord
    {R : Type v} [Field R] {Part : Type} {depth n : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    cwTotalWeightTaggedAtomCoarseIndex
        (cwRecursiveTotalWeightTaggedAtomWord
          encoding term sigma alpha partAt target htarget occurrence) =
      (cwRecursiveTotalWeightFeatureCompatibilityModel
        depth n partAt sigma).coarse
          (cwRecursiveTotalWeightCoarseOfAmbientTarget
            encoding term sigma alpha target htarget) occurrence := by
  rfl

/-- Complete tagged atom words lose no relaxed ambient legal target. -/
theorem cwRecursiveTotalWeightTaggedAtomWord_injective
    {R : Type v} [Field R] {Part : Type} {depth n : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part) :
    Function.Injective (fun target : {target // target ∈
        encoding.relaxedRecursiveAmbientTargets term sigma alpha} ↦
      cwRecursiveTotalWeightTaggedAtomWord
        encoding term sigma alpha partAt target.1 target.2) := by
  intro left right hword
  apply Subtype.ext
  have hleg (logicalLeg : Leg) :
      left.1.legIndex logicalLeg = right.1.legIndex logicalLeg := by
    calc
      left.1.legIndex logicalLeg =
          encoding.encode ∘
            (cwRecursiveTotalWeightCoarseOfAmbientTarget
              encoding term sigma alpha left.1 left.2) (sigma logicalLeg) :=
        (encode_comp_cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha left.1 left.2 logicalLeg).symm
      _ = encoding.encode ∘
            (cwRecursiveTotalWeightCoarseOfAmbientTarget
              encoding term sigma alpha right.1 right.2) (sigma logicalLeg) := by
        funext occurrence
        exact congrArg
          (fun atom : CWTotalWeightTaggedAtom depth Part ↦
            encoding.encode (atom.2 logicalLeg))
          (congrFun hword occurrence)
      _ = right.1.legIndex logicalLeg :=
        encode_comp_cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha right.1 right.2 logicalLeg
  exact ProgressionHash.LegalTriple.ext (hleg .X) (hleg .Y) (hleg .Z)

/-- The evaluator-visible conditional class for one fixed relaxed target's logical-`Z` word. -/
noncomputable def cwRecursiveTotalWeightZCompetitorFeatureClass
    {R : Type v} [Field R] {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (_partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target : {target // target ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha}) :
    Finset (Fin ((n + 1) + (n + 1)) → CWTotalWeightTaggedAtom depth Part) :=
  WordType.conditionalFeatureTypeClass
    ((cwRecursiveTotalWeightCoarseOfAmbientTarget
      encoding term sigma alpha target.1 target.2) (sigma .Z))
    (cwTotalWeightZFiniteCellOfTaggedAtom depth)
    (cwTotalWeightZEvaluatorJointType depth rawTargets)

/-- A coarse-semantic `Z` competitor's complete tagged word belongs to the exact visible-feature
class of the tested target. -/
theorem cwRecursiveTotalWeightTaggedAtomWord_mem_ZCompetitorFeatureClass
    {R : Type v} [Field R] {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target other : {target // target ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha})
    (hcompatible : cwRecursiveTotalWeightZCompatible
      encoding term sigma alpha partAt rawTargets target.1 other.1) :
    cwRecursiveTotalWeightTaggedAtomWord
        encoding term sigma alpha partAt other.1 other.2 ∈
      cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets target := by
  classical
  rcases hcompatible with ⟨htarget, hother, hcompatible⟩
  have htargetProof : htarget = target.2 := Subsingleton.elim _ _
  have hotherProof : hother = other.2 := Subsingleton.elim _ _
  let source : Fin ((n + 1) + (n + 1)) → CWCoarseDigit depth :=
    fun occurrence ↦
      (cwRecursiveTotalWeightCoarseOfAmbientTarget
        encoding term sigma alpha target.1 target.2) (sigma .Z) occurrence
  change cwRecursiveTotalWeightTaggedAtomWord
      encoding term sigma alpha partAt other.1 other.2 ∈
    WordType.conditionalFeatureTypeClass
      source
      (cwTotalWeightZFiniteCellOfTaggedAtom depth)
      (cwTotalWeightZEvaluatorJointType depth rawTargets)
  rw [WordType.mem_conditionalFeatureTypeClass]
  funext pair
  obtain ⟨symbol, cell⟩ := pair
  rw [MoreAsymmetryCompatibility.multiplicity_jointWord_eq_cellMultiplicity,
    MoreAsymmetryCompatibility.cellMultiplicity_subtype_val]
  have hcells :
      (fun occurrence ↦
        ((cwTotalWeightZFiniteCellOfTaggedAtom depth ∘
          cwRecursiveTotalWeightTaggedAtomWord
            encoding term sigma alpha partAt other.1 other.2) occurrence).1) =
      (fun occurrence ↦ zCompatibilityCell
        ((cwRecursiveTotalWeightFeatureCompatibilityModel
          depth n partAt sigma).coarse
            (cwRecursiveTotalWeightCoarseOfAmbientTarget
              encoding term sigma alpha other.1 other.2) occurrence)) := by
    funext occurrence
    rfl
  have htargetWord :
      (fun occurrence ↦
        (cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha target.1 target.2) (sigma .Z) occurrence) =
        (cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha target.1 htarget) (sigma .Z) := by
    funext occurrence
    rw [← htargetProof]
  have hotherCells :
      (fun occurrence ↦ zCompatibilityCell
        ((cwRecursiveTotalWeightFeatureCompatibilityModel
          depth n partAt sigma).coarse
            (cwRecursiveTotalWeightCoarseOfAmbientTarget
              encoding term sigma alpha other.1 other.2) occurrence)) =
        (fun occurrence ↦ zCompatibilityCell
          ((cwRecursiveTotalWeightFeatureCompatibilityModel
            depth n partAt sigma).coarse
              (cwRecursiveTotalWeightCoarseOfAmbientTarget
                encoding term sigma alpha other.1 hother) occurrence)) := by
    funext occurrence
    rw [← hotherProof]
  rw [hcells]
  rw [hotherCells]
  simp only [source]
  rw [htargetWord]
  change cellMultiplicity
      (fun sample ↦ zCompatibilityCell
        ((cwRecursiveTotalWeightFeatureCompatibilityModel
          depth n partAt sigma).coarse
            (cwRecursiveTotalWeightCoarseOfAmbientTarget
              encoding term sigma alpha other.1 hother) sample))
      ((cwRecursiveTotalWeightCoarseOfAmbientTarget
        encoding term sigma alpha target.1 htarget) (sigma .Z))
      cell.1 symbol =
    (cwTotalWeightPushforwardTargets rawTargets).zCellProfile cell.1 symbol
  exact hcompatible cell.1 symbol

/-- Ambient targets satisfying the guarded coarse-semantic `Z` predicate with one fixed target. -/
noncomputable def cwRecursiveTotalWeightZCompatibleTargets
    {R : Type v} [Field R] {Part : Type} [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) :
    Finset (ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) := by
  classical
  exact (encoding.relaxedRecursiveAmbientTargets term sigma alpha).filter
    (cwRecursiveTotalWeightZCompatible
      encoding term sigma alpha partAt rawTargets target)

/-- The complete coarse-semantic `Z` competitor family injects into one exact doubled-occurrence
visible-feature class. -/
theorem card_cwRecursiveTotalWeightZCompatibleTargets_le_featureClass
    {R : Type v} [Field R] {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target : {target // target ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha}) :
    (cwRecursiveTotalWeightZCompatibleTargets
        encoding term sigma alpha partAt rawTargets target.1).card ≤
      (cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets target).card := by
  classical
  let competitors := cwRecursiveTotalWeightZCompatibleTargets
    encoding term sigma alpha partAt rawTargets target.1
  let asAmbient : {other // other ∈ competitors} →
      {other // other ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha} :=
    fun other ↦ ⟨other.1, (Finset.mem_filter.mp other.2).1⟩
  let refinement : {other // other ∈ competitors} →
      Fin ((n + 1) + (n + 1)) → CWTotalWeightTaggedAtom depth Part :=
    fun other ↦ cwRecursiveTotalWeightTaggedAtomWord
      encoding term sigma alpha partAt (asAmbient other).1 (asAmbient other).2
  have hrefinement_mem (other : {other // other ∈ competitors}) :
      refinement other ∈ cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets target := by
    apply cwRecursiveTotalWeightTaggedAtomWord_mem_ZCompetitorFeatureClass
    exact (Finset.mem_filter.mp other.2).2
  let f : {other // other ∈ competitors} →
      {word // word ∈ cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets target} :=
    fun other ↦ ⟨refinement other, hrefinement_mem other⟩
  have hf : Function.Injective f := by
    intro left right heq
    apply Subtype.ext
    have hambient : asAmbient left = asAmbient right :=
      cwRecursiveTotalWeightTaggedAtomWord_injective
        encoding term sigma alpha partAt (congrArg Subtype.val heq)
    exact congrArg
      (fun ambient : {other // other ∈
        encoding.relaxedRecursiveAmbientTargets term sigma alpha} ↦ ambient.1)
      hambient
  simpa only [competitors, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- The collision-proxy family for coarse-semantic `Z` compatibility is bounded by the same
visible-feature class. -/
theorem card_cwRecursiveTotalWeightZAlternativeIndices_le_featureClass
    {R : Type v} [Field R] {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
        (cwRecursiveTotalWeightZCompatible
          encoding term sigma alpha partAt rawTargets)
        ProgressionHash.LegalTriple.collisionProxy target).card ≤
      (cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets ⟨target, htarget⟩).card := by
  classical
  have hsubset :
      ProgressionHash.Seed.compatibilityAlternativeTargets
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
          (cwRecursiveTotalWeightZCompatible
            encoding term sigma alpha partAt rawTargets) target ⊆
        cwRecursiveTotalWeightZCompatibleTargets
          encoding term sigma alpha partAt rawTargets target := by
    intro other hother
    unfold ProgressionHash.Seed.compatibilityAlternativeTargets at hother
    have hdata := Finset.mem_filter.mp hother
    have hambient := (Finset.mem_erase.mp hdata.1).2
    exact Finset.mem_filter.mpr ⟨hambient, hdata.2⟩
  calc
    _ ≤ (ProgressionHash.Seed.compatibilityAlternativeTargets
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
          (cwRecursiveTotalWeightZCompatible
            encoding term sigma alpha partAt rawTargets) target).card :=
      ProgressionHash.Seed.card_compatibilityAlternativeIndices_le _ _ _ _
    _ ≤ (cwRecursiveTotalWeightZCompatibleTargets
          encoding term sigma alpha partAt rawTargets target).card :=
      Finset.card_le_card hsubset
    _ ≤ (cwRecursiveTotalWeightZCompetitorFeatureClass
          encoding term sigma alpha partAt rawTargets ⟨target, htarget⟩).card :=
      card_cwRecursiveTotalWeightZCompatibleTargets_le_featureClass
        encoding term sigma alpha partAt rawTargets ⟨target, htarget⟩

/-- The single-pass combined proxy count is at most the ordinary `X/Y` proxy count plus one
doubled-occurrence visible-feature class. -/
theorem card_cwRecursiveTotalWeightHashRelation_alternatives_le
    {R : Type v} [Field R] {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
        (cwRecursiveTotalWeightHashRelation
          encoding term sigma alpha partAt rawTargets)
        ProgressionHash.LegalTriple.collisionProxy target).card ≤
      (ProgressionHash.LegalTriple.xyCompetitorYIndices
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha) target).card +
      (cwRecursiveTotalWeightZCompetitorFeatureClass
        encoding term sigma alpha partAt rawTargets ⟨target, htarget⟩).card := by
  classical
  unfold cwRecursiveTotalWeightHashRelation
  have hsplit := ProgressionHash.Seed.card_compatibilityAlternativeIndices_or_le_add
    (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
    ProgressionHash.LegalTriple.SharesXY
    (cwRecursiveTotalWeightZCompatible
      encoding term sigma alpha partAt rawTargets)
    ProgressionHash.LegalTriple.collisionProxy target
  have hz := card_cwRecursiveTotalWeightZAlternativeIndices_le_featureClass
    encoding term sigma alpha partAt rawTargets target htarget
  calc
    _ ≤ (ProgressionHash.LegalTriple.xyCompetitorYIndices
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha) target).card +
        (ProgressionHash.Seed.compatibilityAlternativeIndices
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
          (cwRecursiveTotalWeightZCompatible
            encoding term sigma alpha partAt rawTargets)
          ProgressionHash.LegalTriple.collisionProxy target).card := by
      simpa only [
        ProgressionHash.LegalTriple.compatibilityAlternativeIndices_sharesXY_eq_xyCompetitorYIndices]
        using hsplit
    _ ≤ _ := Nat.add_le_add_left hz _

end AlgebraicComplexity.Examples
