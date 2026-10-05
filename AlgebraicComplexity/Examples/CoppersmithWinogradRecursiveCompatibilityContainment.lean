/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveHashExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateHashExtraction
import AlgebraicComplexity.MatrixMultiplication.CompleteSplitCompatibilityContainment
import AlgebraicComplexity.MatrixMultiplication.GroupedCompatibilityCounting

/-!
# Recursive compatibility forces affine hash-leg containment

The recursive constituent proof calls a fine logical-`Y` or logical-`Z` label compatible with a
tested parent address when its complete-split profile agrees with the prescribed compatibility
cells.  The affine hash, however, is applied to the full labelled-child *weight word*.  This file
closes the semantic gap between those two formulations.

Once the reconstructed target tables satisfy their structural weight-support invariant, raw
complete-split compatibility forces equality of the candidate label's full weight word and the
tested address's corresponding recursive child group.  Consequently every cross-group
competitor gives two distinct legal affine-hashing triples sharing the relevant `Y` or `Z` leg.

This is a containment/catchability theorem only.  It does not estimate how many competitors map
to one collision witness, prove an aggregate sparse-hole budget, or identify the intact target
box with the heterogeneous product of child interfaces.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## Compatibility determines the complete recursive hash leg -/

private theorem coe_cwRecursiveLabelledChildWord_eq_splitWordWeight_chunks
    {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (logicalLeg : Leg)
    (label : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    ((cwRecursiveLabelledChildWord depth n label occurrence :
        CWRecursiveChildDigit depth) : ℕ) =
      splitWordWeight
        ((cwRecursiveChildCompatibilityModel depth n partAt).chunks
          logicalLeg label occurrence) := by
  simp only [cwRecursiveChildCompatibilityModel_chunks]
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    rw [cwRecursiveLabelledChildWord_left,
      positiveWordLabelledChildren_left]
    rfl
  · intro sample
    rw [cwRecursiveLabelledChildWord, Fin.append_right,
      positiveWordLabelledChildren_right]

/-- A recursively compatible logical-`Y` label has exactly the tested address's full labelled
child weight word on physical leg `sigma Y`. -/
theorem cwRecursiveLabelledChildWord_eq_group_Y_of_orientedCompatibleY
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (label : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hcompatible : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets label address) :
    cwRecursiveLabelledChildWord depth n label =
      cwRecursiveChildGroup depth n address (sigma .Y) := by
  funext occurrence
  apply Fin.ext
  calc
    ((cwRecursiveLabelledChildWord depth n label occurrence :
        CWRecursiveChildDigit depth) : ℕ) =
        splitWordWeight
          ((cwRecursiveChildCompatibilityModel depth n partAt).chunks
            .Y label occurrence) :=
      coe_cwRecursiveLabelledChildWord_eq_splitWordWeight_chunks
        partAt .Y label occurrence
    _ = ((cwRecursiveChildGroup depth n address (sigma .Y) occurrence :
        CWRecursiveChildDigit depth) : ℕ) := by
      rw [← cwRecursiveChildCompatibilityModel_coarse_get_eq_group
        partAt sigma address occurrence .Y]
      exact MoreAsymmetryCompatibility.CompatibilityModel.splitWordWeight_eq_coarseY_of_compatibleY
          (cwRecursiveChildCompatibilityModel depth n partAt) targets hsupported label
          (logicalAddress sigma address) hcompatible occurrence

/-- Logical-`Z` analogue of
`cwRecursiveLabelledChildWord_eq_group_Y_of_orientedCompatibleY`. -/
theorem cwRecursiveLabelledChildWord_eq_group_Z_of_orientedCompatibleZ
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (label : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets label address) :
    cwRecursiveLabelledChildWord depth n label =
      cwRecursiveChildGroup depth n address (sigma .Z) := by
  funext occurrence
  apply Fin.ext
  calc
    ((cwRecursiveLabelledChildWord depth n label occurrence :
        CWRecursiveChildDigit depth) : ℕ) =
        splitWordWeight
          ((cwRecursiveChildCompatibilityModel depth n partAt).chunks
            .Z label occurrence) :=
      coe_cwRecursiveLabelledChildWord_eq_splitWordWeight_chunks
        partAt .Z label occurrence
    _ = ((cwRecursiveChildGroup depth n address (sigma .Z) occurrence :
        CWRecursiveChildDigit depth) : ℕ) := by
      rw [← cwRecursiveChildCompatibilityModel_coarse_get_eq_group
        partAt sigma address occurrence .Z]
      exact MoreAsymmetryCompatibility.CompatibilityModel.splitWordWeight_eq_coarseZ_of_compatibleZ
          (cwRecursiveChildCompatibilityModel depth n partAt) targets hsupported label
          (logicalAddress sigma address) hcompatible occurrence

/-- Using the target's own logical-`Y` label as the compatibility pivot forces the target and
competitor to have the same recursive logical-`Y` hash group. -/
theorem cwRecursiveChildGroup_Y_eq_of_orientedCompatibleY
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (target other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hcompatible : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target (sigma .Y)) other) :
    cwRecursiveChildGroup depth n target (sigma .Y) =
      cwRecursiveChildGroup depth n other (sigma .Y) := by
  exact cwRecursiveLabelledChildWord_eq_group_Y_of_orientedCompatibleY
    partAt sigma targets hsupported (target (sigma .Y)) other hcompatible

/-- Logical-`Z` analogue of `cwRecursiveChildGroup_Y_eq_of_orientedCompatibleY`. -/
theorem cwRecursiveChildGroup_Z_eq_of_orientedCompatibleZ
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (target other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target (sigma .Z)) other) :
    cwRecursiveChildGroup depth n target (sigma .Z) =
      cwRecursiveChildGroup depth n other (sigma .Z) := by
  exact cwRecursiveLabelledChildWord_eq_group_Z_of_orientedCompatibleZ
    partAt sigma targets hsupported (target (sigma .Z)) other hcompatible

/-! ## Compatibility competitors become shared-leg affine collisions -/

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- Two supported fine recursive addresses related by logical-`Y` compatibility produce legal
affine-hashing triples sharing their `Y` word. -/
theorem recursiveOrientedLegalTriple_sharesY_of_compatibleY
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support})
    (hcompatible : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target.1 (sigma .Y)) other.1) :
    ProgressionHash.LegalTriple.SharesLeg
      (encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
        (cwRecursiveCoarseSourceOfFine K q term hmultiplicity sigma alpha target))
      (encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
        (cwRecursiveCoarseSourceOfFine K q term hmultiplicity sigma alpha other)) := by
  refine ⟨.Y, ?_⟩
  change (fun occurrence ↦ encoding.encode
      (cwRecursiveChildGroup depth n target.1 (sigma .Y) occurrence)) =
    fun occurrence ↦ encoding.encode
      (cwRecursiveChildGroup depth n other.1 (sigma .Y) occurrence)
  exact congrArg (fun word ↦ encoding.encode ∘ word)
    (cwRecursiveChildGroup_Y_eq_of_orientedCompatibleY
      partAt sigma targets hsupported target.1 other.1 hcompatible)

/-- Logical-`Z` analogue of `recursiveOrientedLegalTriple_sharesY_of_compatibleY`. -/
theorem recursiveOrientedLegalTriple_sharesZ_of_compatibleZ
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support})
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target.1 (sigma .Z)) other.1) :
    ProgressionHash.LegalTriple.SharesLeg
      (encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
        (cwRecursiveCoarseSourceOfFine K q term hmultiplicity sigma alpha target))
      (encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
        (cwRecursiveCoarseSourceOfFine K q term hmultiplicity sigma alpha other)) := by
  refine ⟨.Z, ?_⟩
  change (fun occurrence ↦ encoding.encode
      (cwRecursiveChildGroup depth n target.1 (sigma .Z) occurrence)) =
    fun occurrence ↦ encoding.encode
      (cwRecursiveChildGroup depth n other.1 (sigma .Z) occurrence)
  exact congrArg (fun word ↦ encoding.encode ∘ word)
    (cwRecursiveChildGroup_Z_eq_of_orientedCompatibleZ
      partAt sigma targets hsupported target.1 other.1 hcompatible)

/-! ## Direct adapter from grouped cleanup competitors -/

/-- Every grouped logical-`Y` competitor in a support contained in the actual selected recursive
term yields distinct legal triples sharing their `Y` affine-hash leg. -/
theorem recursiveY_groupCompetitor_distinct_and_sharesLeg
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆ (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).support)
    (target : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (htarget : target ∈ (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).support)
    (other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hother : other ∈ Tensor.groupCompatibilityCompetitors ambient
      (cwRecursiveChildGroup depth n) (sigma .Y)
      (OrientedCompatibleY (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets) target) :
    let targetSource := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha ⟨target, htarget⟩
    let otherSource := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha ⟨other,
        hambient ((Tensor.mem_groupCompatibilityCompetitors
          ambient (cwRecursiveChildGroup depth n) (sigma .Y)
          (OrientedCompatibleY (A := fun _c ↦
            PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
            (cwRecursiveChildCompatibilityModel depth n partAt) targets)
          target other).mp hother).1⟩
    let targetTriple := encoding.recursiveOrientedLegalTriple
      K q term hmultiplicity sigma alpha targetSource
    let otherTriple := encoding.recursiveOrientedLegalTriple
      K q term hmultiplicity sigma alpha otherSource
    targetTriple ≠ otherTriple ∧
      ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple := by
  classical
  have hdata := (Tensor.mem_groupCompatibilityCompetitors
    ambient (cwRecursiveChildGroup depth n) (sigma .Y)
    (OrientedCompatibleY (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets)
    target other).mp hother
  let targetFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support} := ⟨target, htarget⟩
  let otherFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support} :=
    ⟨other, hambient hdata.1⟩
  let targetSource := cwRecursiveCoarseSourceOfFine
    K q term hmultiplicity sigma alpha targetFine
  let otherSource := cwRecursiveCoarseSourceOfFine
    K q term hmultiplicity sigma alpha otherFine
  let targetTriple := encoding.recursiveOrientedLegalTriple
    K q term hmultiplicity sigma alpha targetSource
  let otherTriple := encoding.recursiveOrientedLegalTriple
    K q term hmultiplicity sigma alpha otherSource
  have hsourceNe : targetSource ≠ otherSource := by
    intro heq
    apply hdata.2.2.2
    exact congrArg Subtype.val heq |>.symm
  have htripleNe : targetTriple ≠ otherTriple := by
    intro heq
    exact hsourceNe (encoding.recursiveOrientedLegalTriple_injective
      K q term hmultiplicity sigma alpha heq)
  have hshares : ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple :=
    encoding.recursiveOrientedLegalTriple_sharesY_of_compatibleY
      K q term hmultiplicity sigma alpha partAt targets hsupported
      targetFine otherFine hdata.2.2.1
  exact ⟨htripleNe, hshares⟩

/-- Logical-`Z` analogue of `recursiveY_groupCompetitor_distinct_and_sharesLeg`. -/
theorem recursiveZ_groupCompetitor_distinct_and_sharesLeg
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆ (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).support)
    (target : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (htarget : target ∈ (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).support)
    (other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hother : other ∈ Tensor.groupCompatibilityCompetitors ambient
      (cwRecursiveChildGroup depth n) (sigma .Z)
      (OrientedCompatibleZ (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets) target) :
    let targetSource := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha ⟨target, htarget⟩
    let otherSource := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha ⟨other,
        hambient ((Tensor.mem_groupCompatibilityCompetitors
          ambient (cwRecursiveChildGroup depth n) (sigma .Z)
          (OrientedCompatibleZ (A := fun _c ↦
            PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
            (cwRecursiveChildCompatibilityModel depth n partAt) targets)
          target other).mp hother).1⟩
    let targetTriple := encoding.recursiveOrientedLegalTriple
      K q term hmultiplicity sigma alpha targetSource
    let otherTriple := encoding.recursiveOrientedLegalTriple
      K q term hmultiplicity sigma alpha otherSource
    targetTriple ≠ otherTriple ∧
      ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple := by
  classical
  have hdata := (Tensor.mem_groupCompatibilityCompetitors
    ambient (cwRecursiveChildGroup depth n) (sigma .Z)
    (OrientedCompatibleZ (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets)
    target other).mp hother
  let targetFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support} := ⟨target, htarget⟩
  let otherFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support} :=
    ⟨other, hambient hdata.1⟩
  let targetSource := cwRecursiveCoarseSourceOfFine
    K q term hmultiplicity sigma alpha targetFine
  let otherSource := cwRecursiveCoarseSourceOfFine
    K q term hmultiplicity sigma alpha otherFine
  let targetTriple := encoding.recursiveOrientedLegalTriple
    K q term hmultiplicity sigma alpha targetSource
  let otherTriple := encoding.recursiveOrientedLegalTriple
    K q term hmultiplicity sigma alpha otherSource
  have hsourceNe : targetSource ≠ otherSource := by
    intro heq
    apply hdata.2.2.2
    exact congrArg Subtype.val heq |>.symm
  have htripleNe : targetTriple ≠ otherTriple := by
    intro heq
    exact hsourceNe (encoding.recursiveOrientedLegalTriple_injective
      K q term hmultiplicity sigma alpha heq)
  have hshares : ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple :=
    encoding.recursiveOrientedLegalTriple_sharesZ_of_compatibleZ
      K q term hmultiplicity sigma alpha partAt targets hsupported
      targetFine otherFine hdata.2.2.1
  exact ⟨htripleNe, hshares⟩

/-! ## Catchability on the approximate-input support used by cleanup -/

/-- Two addresses in the actual approximate-input support related by logical-`Y` compatibility
produce relaxed legal triples sharing their `Y` hash leg.  Unlike the older exact-input adapter,
this statement applies directly to the ambient support on which recursive cleanup runs. -/
theorem relaxedRecursiveOrientedLegalTriple_sharesY_of_approximateCompatibleY
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support})
    (hcompatible : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target.1 (sigma .Y)) other.1) :
    ProgressionHash.LegalTriple.SharesLeg
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha target).1)
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha other).1) := by
  refine ⟨.Y, ?_⟩
  rw [encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha target .Y,
    encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha other .Y]
  simpa only [cwRecursiveChildGroup_apply] using congrArg
    (fun word ↦ encoding.encode ∘ word)
    (cwRecursiveChildGroup_Y_eq_of_orientedCompatibleY
      partAt sigma targets hsupported target.1 other.1 hcompatible)

/-- Logical-`Z` analogue of
`relaxedRecursiveOrientedLegalTriple_sharesY_of_approximateCompatibleY`. -/
theorem relaxedRecursiveOrientedLegalTriple_sharesZ_of_approximateCompatibleZ
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (target other : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support})
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
      (target.1 (sigma .Z)) other.1) :
    ProgressionHash.LegalTriple.SharesLeg
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha target).1)
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha other).1) := by
  refine ⟨.Z, ?_⟩
  rw [encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha target .Z,
    encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
      K q term hmultiplicity epsilon sigma alpha other .Z]
  simpa only [cwRecursiveChildGroup_apply] using congrArg
    (fun word ↦ encoding.encode ∘ word)
    (cwRecursiveChildGroup_Z_eq_of_orientedCompatibleZ
      partAt sigma targets hsupported target.1 other.1 hcompatible)

/-- Every grouped logical-`Y` competitor in an approximate-input ambient support gives two
distinct relaxed legal triples sharing the `Y` hash leg.  This is the catchability statement for
the literal `yFirst.support` cleanup ambient. -/
theorem approximateRecursiveY_groupCompetitor_distinct_and_sharesLeg
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆ (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).support)
    (target : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (htarget : target ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).support)
    (other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hother : other ∈ Tensor.groupCompatibilityCompetitors ambient
      (cwRecursiveChildGroup depth n) (sigma .Y)
      (OrientedCompatibleY (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets) target) :
    let targetFine := ⟨target, htarget⟩
    let otherFine := ⟨other,
      hambient ((Tensor.mem_groupCompatibilityCompetitors
        ambient (cwRecursiveChildGroup depth n) (sigma .Y)
        (OrientedCompatibleY (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
          (cwRecursiveChildCompatibilityModel depth n partAt) targets)
        target other).mp hother).1⟩
    let targetSource := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha targetFine
    let otherSource := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha otherFine
    let targetTriple := encoding.relaxedRecursiveOrientedLegalTriple
      term sigma targetSource.1
    let otherTriple := encoding.relaxedRecursiveOrientedLegalTriple
      term sigma otherSource.1
    targetTriple ≠ otherTriple ∧
      ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple := by
  classical
  have hdata := (Tensor.mem_groupCompatibilityCompetitors
    ambient (cwRecursiveChildGroup depth n) (sigma .Y)
    (OrientedCompatibleY (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets)
    target other).mp hother
  let targetFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support} := ⟨target, htarget⟩
  let otherFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support} :=
    ⟨other, hambient hdata.1⟩
  let targetSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha targetFine
  let otherSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha otherFine
  let targetTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma targetSource.1
  let otherTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma otherSource.1
  have hsourceNe : targetSource.1 ≠ otherSource.1 := by
    intro heq
    apply hdata.2.2.2
    calc
      cwRecursiveChildGroup depth n other =
          cwRecursiveCoarseAddressOfLeftShapeWord term sigma otherSource.1 := by
        simpa only [otherSource, otherFine] using
          (cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha otherFine).symm
      _ = cwRecursiveCoarseAddressOfLeftShapeWord term sigma targetSource.1 :=
        congrArg _ heq.symm
      _ = cwRecursiveChildGroup depth n target := by
        simpa only [targetSource, targetFine] using
          cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha targetFine
  have htripleNe : targetTriple ≠ otherTriple := by
    intro heq
    exact hsourceNe
      (encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma heq)
  have hshares : ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple :=
    encoding.relaxedRecursiveOrientedLegalTriple_sharesY_of_approximateCompatibleY
      K q term hmultiplicity epsilon sigma alpha partAt targets hsupported
      targetFine otherFine hdata.2.2.1
  exact ⟨htripleNe, hshares⟩

/-- Logical-`Z` analogue of
`approximateRecursiveY_groupCompetitor_distinct_and_sharesLeg`; it applies to the literal
`zFirst.support` cleanup ambient. -/
theorem approximateRecursiveZ_groupCompetitor_distinct_and_sharesLeg
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆ (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).support)
    (target : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (htarget : target ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).support)
    (other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hother : other ∈ Tensor.groupCompatibilityCompetitors ambient
      (cwRecursiveChildGroup depth n) (sigma .Z)
      (OrientedCompatibleZ (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets) target) :
    let targetFine := ⟨target, htarget⟩
    let otherFine := ⟨other,
      hambient ((Tensor.mem_groupCompatibilityCompetitors
        ambient (cwRecursiveChildGroup depth n) (sigma .Z)
        (OrientedCompatibleZ (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
          (cwRecursiveChildCompatibilityModel depth n partAt) targets)
        target other).mp hother).1⟩
    let targetSource := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha targetFine
    let otherSource := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha otherFine
    let targetTriple := encoding.relaxedRecursiveOrientedLegalTriple
      term sigma targetSource.1
    let otherTriple := encoding.relaxedRecursiveOrientedLegalTriple
      term sigma otherSource.1
    targetTriple ≠ otherTriple ∧
      ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple := by
  classical
  have hdata := (Tensor.mem_groupCompatibilityCompetitors
    ambient (cwRecursiveChildGroup depth n) (sigma .Z)
    (OrientedCompatibleZ (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets)
    target other).mp hother
  let targetFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support} := ⟨target, htarget⟩
  let otherFine : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support} :=
    ⟨other, hambient hdata.1⟩
  let targetSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha targetFine
  let otherSource := cwRecursiveApproximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha otherFine
  let targetTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma targetSource.1
  let otherTriple := encoding.relaxedRecursiveOrientedLegalTriple
    term sigma otherSource.1
  have hsourceNe : targetSource.1 ≠ otherSource.1 := by
    intro heq
    apply hdata.2.2.2
    calc
      cwRecursiveChildGroup depth n other =
          cwRecursiveCoarseAddressOfLeftShapeWord term sigma otherSource.1 := by
        simpa only [otherSource, otherFine] using
          (cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha otherFine).symm
      _ = cwRecursiveCoarseAddressOfLeftShapeWord term sigma targetSource.1 :=
        congrArg _ heq.symm
      _ = cwRecursiveChildGroup depth n target := by
        simpa only [targetSource, targetFine] using
          cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha targetFine
  have htripleNe : targetTriple ≠ otherTriple := by
    intro heq
    exact hsourceNe
      (encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma heq)
  have hshares : ProgressionHash.LegalTriple.SharesLeg targetTriple otherTriple :=
    encoding.relaxedRecursiveOrientedLegalTriple_sharesZ_of_approximateCompatibleZ
      K q term hmultiplicity epsilon sigma alpha partAt targets hsupported
      targetFine otherFine hdata.2.2.1
  exact ⟨htripleNe, hshares⟩

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
