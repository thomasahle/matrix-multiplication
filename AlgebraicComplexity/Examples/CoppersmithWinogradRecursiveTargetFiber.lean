/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveFiberNormalization
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCleanup
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiberCore

/-!
# Exact target alphabets inside recursive CW cleanup fibers

Compatibility cleanup is performed on fine parent labels while the hash quotient records only
the weights of their two labelled children.  Sparse repair must use the smaller intact alphabet
whose members have both the fixed quotient word and the prescribed complete-split table in every
tagged child cell.

The dependency-light core module defines that alphabet. This module proves its transport under a
common parent-position permutation. It does not assume that the target alphabet is nonempty, that
a whole target box survives, or that the cleaned fiber has few holes.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The compatibility model's coarse word is exactly the tagged logical presentation of the
recursive hash group. -/
theorem cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence
    {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    (cwRecursiveChildCompatibilityModel depth n partAt).coarse
        (logicalAddress sigma address) =
      cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma
        (cwRecursiveChildGroup depth n address) := by
  funext occurrence
  apply CoarseIndex.ext
  · rfl
  · exact cwRecursiveChildCompatibilityModel_coarse_get_eq_group
      partAt sigma address occurrence .X
  · exact cwRecursiveChildCompatibilityModel_coarse_get_eq_group
      partAt sigma address occurrence .Y
  · exact cwRecursiveChildCompatibilityModel_coarse_get_eq_group
      partAt sigma address occurrence .Z

/-- Splitting parent chunks into labelled children commutes with a common parent-position
permutation, viewed on the doubled occurrence index. -/
theorem positiveWordLabelledChildren_positionRelabel_eq_comp
    {A : Type u} {depth n : ℕ}
    (encode : A → SplitWord (depth + 1))
    (tau : Equiv.Perm (Fin (n + 1))) (word : PositiveWord A n) :
  positiveWordLabelledChildren encode
        (positiveWordPositionEquiv A n tau word) =
      positiveWordLabelledChildren encode word ∘
        cwRecursiveOccurrencePositionEquiv tau := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp [Function.comp_apply]
  · simp only [positiveWordLabelledChildren_right, Function.comp_apply,
      cwRecursiveOccurrencePositionEquiv_natAdd,
      positiveWordEquiv_position_apply]

/-- A paired position relabelling transports the tagged logical coarse-index sequence. -/
theorem cwRecursiveOrientedCoarseIndexSequence_positionRelabel
    {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (tau : Equiv.Perm (Fin (n + 1)))
    (hpart : partAt ∘ tau = partAt)
    (coarse : CWRecursiveCoarseAddress depth n) :
    cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma
        (cwRecursivePositionRelabelCoarseAddress depth n tau coarse) =
      cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma coarse ∘
        cwRecursiveOccurrencePositionEquiv tau := by
  funext occurrence
  apply CoarseIndex.ext
  · refine Fin.addCases ?_ ?_ occurrence <;> intro sample
    · simpa only [cwRecursiveOrientedCoarseIndexSequence_part,
        Function.comp_apply, cwRecursiveOccurrencePositionEquiv_castAdd,
        labelledChildParts_left] using (congrFun hpart sample).symm
    · simpa only [cwRecursiveOrientedCoarseIndexSequence_part,
        Function.comp_apply, cwRecursiveOccurrencePositionEquiv_natAdd,
        labelledChildParts_right] using (congrFun hpart sample).symm
  · simpa only [cwRecursiveOrientedCoarseIndexSequence,
      Function.comp_apply] using congrArg
      (fun digit : CWRecursiveChildDigit depth ↦ (digit : ℕ))
      (congrFun (cwRecursivePositionRelabelCoarseAddress_apply_eq_comp
        depth n tau coarse (sigma .X)) occurrence)
  · simpa only [cwRecursiveOrientedCoarseIndexSequence,
      Function.comp_apply] using congrArg
      (fun digit : CWRecursiveChildDigit depth ↦ (digit : ℕ))
      (congrFun (cwRecursivePositionRelabelCoarseAddress_apply_eq_comp
        depth n tau coarse (sigma .Y)) occurrence)
  · simpa only [cwRecursiveOrientedCoarseIndexSequence,
      Function.comp_apply] using congrArg
      (fun digit : CWRecursiveChildDigit depth ↦ (digit : ℕ))
      (congrFun (cwRecursivePositionRelabelCoarseAddress_apply_eq_comp
        depth n tau coarse (sigma .Z)) occurrence)

/-- Transport of an exact recursive target alphabet along a paired parent-position permutation. -/
theorem cwRecursiveExactTargetFiberParts_positionRelabel
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (left right : CWRecursiveCoarseAddress depth n)
    (tau : Equiv.Perm (Fin (n + 1)))
    (hpart : partAt ∘ tau = partAt)
    (hcoarse : cwRecursivePositionRelabelCoarseAddress
      depth n tau right = left)
    (physicalLeg : Leg)
    {fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n}
    (hfine : fine ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets right physicalLeg) :
    positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau fine ∈
      cwRecursiveExactTargetFiberParts
        partAt sigma targets left physicalLeg := by
  classical
  let moved := positiveWordPositionEquiv
    (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau fine
  let rho := cwRecursiveOccurrencePositionEquiv tau
  have hdata := (mem_cwRecursiveExactTargetFiberParts_iff
    partAt sigma targets right physicalLeg fine).1 hfine
  apply (mem_cwRecursiveExactTargetFiberParts_iff
    partAt sigma targets left physicalLeg moved).2
  constructor
  · calc
      cwRecursiveLabelledChildWord depth n moved =
          cwRecursiveLabelledChildWord depth n fine ∘ rho := by
            simpa [moved, rho] using
              cwRecursiveLabelledChildWord_positionRelabel_eq_comp
                depth n tau fine
      _ = right physicalLeg ∘ rho := by rw [hdata.1]
      _ = cwRecursivePositionRelabelCoarseAddress
          depth n tau right physicalLeg := by
            exact (cwRecursivePositionRelabelCoarseAddress_apply_eq_comp
              depth n tau right physicalLeg).symm
      _ = left physicalLeg := congrFun hcoarse physicalLeg
  · intro cell word
    have hcells :
        cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma left =
          cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma right ∘ rho := by
      calc
        cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma left =
            cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma
              (cwRecursivePositionRelabelCoarseAddress depth n tau right) := by
                rw [hcoarse]
        _ = cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma right ∘ rho := by
              simpa [rho] using
                cwRecursiveOrientedCoarseIndexSequence_positionRelabel
                  partAt sigma tau hpart right
    have hchunks :
        positiveWordLabelledChildren
            (cwChunkSplitWord (depth + 1)) moved =
          positiveWordLabelledChildren
            (cwChunkSplitWord (depth + 1)) fine ∘ rho := by
      simpa [moved, rho] using
        positiveWordLabelledChildren_positionRelabel_eq_comp
          (cwChunkSplitWord (depth + 1)) tau fine
    rw [hcells, hchunks, cellMultiplicity_comp_perm]
    exact hdata.2 cell word

/-- Every physical-leg label occurring in a final recursively cleaned group fiber belongs to the
exact target alphabet for that quotient address.

The hypothesis `hExact` is local and checkable on the explicitly constructed final support.  It
does not assert a restriction, a survivor count, or the existence of an intact target box. -/
theorem cwRecursiveCleanedFiberParts_subset_exactTarget
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).withSupport finalSupport).LegGrouping
        (CWRecursiveCoarseAddress depth n))
    (hgroup : ∀ address,
      G.group address = cwRecursiveChildGroup depth n address)
    (coarse : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    G.fiberParts coarse physicalLeg ⊆
      cwRecursiveExactTargetFiberParts
        partAt sigma targets coarse physicalLeg := by
  classical
  intro fine hfine
  obtain ⟨address, haddress, haddressGroup, hlabel⟩ :=
    (G.mem_fiberParts_iff coarse physicalLeg fine).1 hfine
  have hcoarse : cwRecursiveChildGroup depth n address = coarse := by
    calc
      cwRecursiveChildGroup depth n address = G.group address :=
        (hgroup address).symm
      _ = coarse := haddressGroup
  apply (mem_cwRecursiveExactTargetFiberParts_iff
    partAt sigma targets coarse physicalLeg fine).2
  constructor
  · calc
      cwRecursiveLabelledChildWord depth n fine =
          cwRecursiveLabelledChildWord depth n (address physicalLeg) := by
            rw [hlabel]
      _ = cwRecursiveChildGroup depth n address physicalLeg := rfl
      _ = coarse physicalLeg := congrFun hcoarse physicalLeg
  · intro cell word
    let logicalLeg := sigma.symm physicalLeg
    have hphysical : sigma logicalLeg = physicalLeg :=
      sigma.apply_symm_apply physicalLeg
    have hmatch := hExact address haddress logicalLeg cell word
    have hcoarseModel :
        (cwRecursiveChildCompatibilityModel depth n partAt).coarse
            (logicalAddress sigma address) =
          cwRecursiveOrientedCoarseIndexSequence
            depth n partAt sigma coarse := by
      rw [cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence,
        hcoarse]
    have hchunks :
        (cwRecursiveChildCompatibilityModel depth n partAt).chunks logicalLeg
            (logicalAddress sigma address logicalLeg) =
          positiveWordLabelledChildren
            (cwChunkSplitWord (depth + 1)) fine := by
      funext occurrence
      change positiveWordLabelledChildren
          (cwChunkSplitWord (depth + 1)) (address (sigma logicalLeg)) occurrence =
        positiveWordLabelledChildren
          (cwChunkSplitWord (depth + 1)) fine occurrence
      rw [hphysical, hlabel]
    rw [hcoarseModel, hchunks] at hmatch
    exact hmatch

end AlgebraicComplexity.Examples
