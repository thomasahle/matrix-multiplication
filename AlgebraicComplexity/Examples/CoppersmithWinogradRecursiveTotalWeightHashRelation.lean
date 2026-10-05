/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TwoLegHashingExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCompatibilityContainment
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTotalWeightFeature

set_option autoImplicit false

/-!
# Total-weight compatibility on the relaxed recursive hash family

Affine hashing for a recursive Coppersmith--Winograd constituent is performed on the full
abstract marginal-word family.  This module defines the semantic relation needed for a
single-pass `X/Y`-or-total-weight-`Z` isolation directly on that family.

The `Z` branch is guarded by proofs that both legal triples belong to the relaxed ambient family.
Those proofs let us recover their unique abstract marginal words, rebuild their complete doubled
coarse addresses, and test total-weight feature compatibility without choosing a fine tensor
preimage.  Supported feature compatibility forces equality of the complete encoded `Z` hash
word.  Actual approximate-input fine `Y` and `Z` compatibility edges enter the corresponding
branches of the relation.

Everything here is finite and semantic.  No competitor bound, hashing seed, tensor restriction,
asymptotic estimate, certificate datum, or fixed-cell selection is assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Recover the complete doubled quotient address represented by one relaxed ambient legal
triple.  The ambient membership proof is data only for the inverse equivalence; proof
irrelevance makes the resulting address independent of its presentation. -/
noncomputable def cwRecursiveTotalWeightCoarseOfAmbientTarget
    {R : Type v} [Field R] {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha) :
    CWRecursiveCoarseAddress depth n :=
  cwRecursiveCoarseAddressOfLeftShapeWord term sigma
    (encoding.relaxedRecursiveAmbientSourceOfTarget
      term sigma alpha ⟨target, htarget⟩).1

/-- Recovering the coarse address of a legal triple constructed from an ambient marginal word
returns the address built from that word. -/
theorem cwRecursiveTotalWeightCoarseOfAmbientTarget_of_source
    {R : Type v} [Field R] {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {word // word ∈ alpha.marginalWords})
    (hsource : encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1 ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha) :
    cwRecursiveTotalWeightCoarseOfAmbientTarget encoding term sigma alpha
        (encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1) hsource =
      cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1 := by
  apply congrArg (cwRecursiveCoarseAddressOfLeftShapeWord term sigma)
  apply encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma
  exact encoding.relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
    term sigma alpha
      ⟨encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1, hsource⟩

/-- Encoding one logical leg of the recovered coarse address gives exactly the corresponding
leg index of the ambient legal triple. -/
theorem encode_comp_cwRecursiveTotalWeightCoarseOfAmbientTarget
    {R : Type v} [Field R] {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target)
    (htarget : target ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha)
    (logicalLeg : Leg) :
    encoding.encode ∘
        (cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha target htarget) (sigma logicalLeg) =
      target.legIndex logicalLeg := by
  have htriple :=
    encoding.relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
      term sigma alpha ⟨target, htarget⟩
  have hindex := congrArg
    (fun triple ↦ triple.legIndex logicalLeg) htriple
  funext occurrence
  change encoding.encode
      ((cwRecursiveTotalWeightCoarseOfAmbientTarget
        encoding term sigma alpha target htarget) (sigma logicalLeg) occurrence) =
    target.legIndex logicalLeg occurrence
  cases logicalLeg <;>
    simpa [cwRecursiveTotalWeightCoarseOfAmbientTarget,
      CWCoarseFieldEncoding.relaxedRecursiveOrientedLegalTriple] using
        congrFun hindex occurrence

/-- Total-weight `Z` compatibility between two uniquely decoded relaxed ambient quotient
addresses.  The predicate is false when either legal triple lies outside the ambient family. -/
noncomputable def cwRecursiveTotalWeightZCompatible
    {R : Type v} [Field R] {Part : Type u} [DecidableEq Part]
    {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (left right : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) : Prop :=
  ∃ (hleft : left ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha)
    (hright : right ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha),
    (cwRecursiveTotalWeightFeatureCompatibilityModel
      depth n partAt sigma).FeatureCompatibleZ
        (cwTotalWeightPushforwardTargets rawTargets)
        ((cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha left hleft) (sigma .Z))
        (cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha right hright)

/-- The semantic relation used by the relaxed single-pass hash: ordinary `X/Y` sharing, or the
guarded total-weight `Z` predicate. -/
noncomputable def cwRecursiveTotalWeightHashRelation
    {R : Type v} [Field R] {Part : Type u} [DecidableEq Part]
    {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (left right : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) : Prop :=
  ProgressionHash.LegalTriple.SharesXY left right ∨
    cwRecursiveTotalWeightZCompatible
      encoding term sigma alpha partAt rawTargets left right

/-- Every pair in the relaxed total-weight relation shares an actual affine-hash leg. -/
theorem cwRecursiveTotalWeightHashRelation_sharesLeg
    {R : Type v} [Field R] {Part : Type u} [DecidableEq Part]
    {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ} (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    {left right : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target}
    (hrelated : cwRecursiveTotalWeightHashRelation
      encoding term sigma alpha partAt rawTargets left right) :
    ProgressionHash.LegalTriple.SharesLeg left right := by
  rcases hrelated with hxy | hz
  · rcases hxy with hx | hy
    · exact ⟨.X, hx⟩
    · exact ⟨.Y, hy⟩
  · rcases hz with ⟨hleft, hright, hz⟩
    let leftCoarse := cwRecursiveTotalWeightCoarseOfAmbientTarget
      encoding term sigma alpha left hleft
    let rightCoarse := cwRecursiveTotalWeightCoarseOfAmbientTarget
      encoding term sigma alpha right hright
    have hword : leftCoarse (sigma .Z) = rightCoarse (sigma .Z) :=
      cwRecursiveTotalWeight_label_eq_Z_of_featureCompatibleZ
        partAt sigma rawTargets hsupported
          (leftCoarse (sigma .Z)) rightCoarse hz
    refine ⟨.Z, ?_⟩
    rw [← encode_comp_cwRecursiveTotalWeightCoarseOfAmbientTarget
        encoding term sigma alpha left hleft .Z,
      ← encode_comp_cwRecursiveTotalWeightCoarseOfAmbientTarget
        encoding term sigma alpha right hright .Z]
    exact congrArg (fun word ↦ encoding.encode ∘ word) hword

/-- A raw logical-`Y` compatibility edge between actual approximate-input addresses enters the
ordinary `Y`-sharing branch of the relaxed semantic relation. -/
theorem cwRecursiveApproximate_compatibleY_to_totalWeightHashRelation
    {R : Type v} [Field R] {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support})
    (hcompatible : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) rawTargets
      (target.1 (sigma .Y)) other.1) :
    cwRecursiveTotalWeightHashRelation encoding term sigma alpha partAt rawTargets
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha target).1)
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha other).1) := by
  apply Or.inl
  apply Or.inr
  change
    (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha target).1).legIndex .Y =
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha other).1).legIndex .Y
  rw [encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha target .Y,
    encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha other .Y]
  simpa only [cwRecursiveChildGroup_apply] using congrArg
    (fun word ↦ encoding.encode ∘ word)
    (cwRecursiveChildGroup_Y_eq_of_orientedCompatibleY
      partAt sigma rawTargets hsupported target.1 other.1 hcompatible)

/-- A raw logical-`Z` compatibility edge between actual approximate-input addresses enters the
guarded total-weight feature branch of the relaxed semantic relation. -/
theorem cwRecursiveApproximate_compatibleZ_to_totalWeightHashRelation
    {R : Type v} [Field R] {depth : ℕ}
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support})
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) rawTargets
      (target.1 (sigma .Z)) other.1) :
    cwRecursiveTotalWeightHashRelation encoding term sigma alpha partAt rawTargets
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha target).1)
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha other).1) := by
  classical
  let targetSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha target
  let otherSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha other
  let targetTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma targetSource.1
  let otherTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma otherSource.1
  have htargetAmbient : targetTriple ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha := by
    exact Finset.mem_image.mpr ⟨targetSource.1, targetSource.2, rfl⟩
  have hotherAmbient : otherTriple ∈
      encoding.relaxedRecursiveAmbientTargets term sigma alpha := by
    exact Finset.mem_image.mpr ⟨otherSource.1, otherSource.2, rfl⟩
  apply Or.inr
  refine ⟨htargetAmbient, hotherAmbient, ?_⟩
  have htargetCoarse :
      cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha targetTriple htargetAmbient =
        cwRecursiveChildGroup depth n target.1 := by
    calc
      _ = cwRecursiveCoarseAddressOfLeftShapeWord term sigma targetSource.1 :=
        cwRecursiveTotalWeightCoarseOfAmbientTarget_of_source
          encoding term sigma alpha targetSource htargetAmbient
      _ = cwRecursiveChildGroup depth n target.1 := by
        simpa only [targetSource] using
          cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha target
  have hotherCoarse :
      cwRecursiveTotalWeightCoarseOfAmbientTarget
          encoding term sigma alpha otherTriple hotherAmbient =
        cwRecursiveChildGroup depth n other.1 := by
    calc
      _ = cwRecursiveCoarseAddressOfLeftShapeWord term sigma otherSource.1 :=
        cwRecursiveTotalWeightCoarseOfAmbientTarget_of_source
          encoding term sigma alpha otherSource hotherAmbient
      _ = cwRecursiveChildGroup depth n other.1 := by
        simpa only [otherSource] using
          cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha other
  rw [htargetCoarse, hotherCoarse]
  exact cwRecursive_orientedCompatibleZ_to_totalWeightFeatureCompatibleZ
    partAt sigma rawTargets target.1 other.1 hcompatible

end AlgebraicComplexity.Examples
