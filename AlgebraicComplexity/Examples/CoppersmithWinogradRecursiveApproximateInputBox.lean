/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputHoles

set_option autoImplicit false

/-!
# The approximate recursive CW source inside an exact target box

This module records the finite support identity used at the input of the recursive constituent
argument in Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou, *More Asymmetry Yields Faster Matrix
Multiplication*, [alman2025more].  It formalizes the selector step described in
`papers/sources/2404.16349/constituent.tex`, lines 138--147, 338--348, and 473--479, and the
input-hole discussion in `better_bound/paper.tex`, lines 908--1138.

Fix a coarse labelled-child address whose ordered-left joint type is exactly `alpha`.  Every label
in its exact target alphabet then has the corresponding `alpha` marginal.  Consequently, boxing
the approximately selected parent tensor by that target alphabet is exactly the same as boxing the
full parent power by those exact target labels which pass the approximate parent-input predicate.

This is an equality of finite partitioned tensors.  It neither replaces the approximate parent law
by one exact empirical law nor asserts that every independently assembled target label is present.
The absent labels are precisely the input-profile holes treated downstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- An exact target label over an exact-`alpha` coarse address has the prescribed ordered-left
marginal on its physical leg.

**Proof sketch.** Exact-target membership says that the label's full labelled-child word is the
chosen coarse word.  Restricting this equality to left-child positions identifies its ordered-left
coordinate word with the appropriate logical coordinate of the coarse address.  The joint
`alpha`-type hypothesis gives that coordinate word the required marginal multiplicity. -/
theorem CWRecursiveKeepsAlphaMarginal_of_mem_cwRecursiveExactTargetFiberParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n)
    (hcoarse : CWRecursiveMatchesAlpha sigma alpha coarse)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (hfine : fine ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets coarse physicalLeg) :
    CWRecursiveKeepsAlphaMarginal sigma alpha physicalLeg fine := by
  have hlabel :=
    (mem_cwRecursiveExactTargetFiberParts_iff
      partAt sigma targets coarse physicalLeg fine).1 hfine |>.1
  have hmarginal :=
    multiplicity_cwRecursiveLogicalLeftCoordinateWord_eq_marginalCount
      sigma alpha coarse hcoarse (sigma.symm physicalLeg)
  unfold CWRecursiveKeepsAlphaMarginal
  rw [← hmarginal]
  apply congrArg WordType.multiplicity
  funext sample
  have hcoordinate := congrFun hlabel (Fin.castAdd (n + 1) sample)
  simpa only [cwRecursiveLabelledChildWord_left,
    cwRecursiveLogicalLeftCoordinateWord, Equiv.apply_symm_apply] using hcoordinate

/-- Over an exact-`alpha` coarse address, exact-target boxing of the approximately selected source
is the full parent power boxed by the approximate-input target alphabet.

In symbols, if `coarse` has ordered-left joint type `alpha`, then
`approxSelected.box exactTargets = fullPower.box approximateInputTargets`.

**Proof sketch.** Expand support membership on both sides.  The approximate selector contributes
the full-power support condition and the legwise approximate parent predicates; the exact target
box contributes exact-target membership.  Conversely, exact-target membership supplies every
ordered-left marginal selector by the preceding theorem.  Both constructions retain the same
constituent function definitionally. -/
theorem cwRecursiveApproximateSelected_box_exactTarget_eq_inputTargetBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n)
    (hcoarse : CWRecursiveMatchesAlpha sigma alpha coarse) :
    (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).box
        (cwRecursiveExactTargetFiberParts partAt sigma targets coarse) =
      ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets coarse) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.mem_box_support]
    constructor
    · rintro ⟨hselected, htargets⟩
      have hselectedData :=
        (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
          K q term hmultiplicity epsilon sigma alpha address).1 hselected
      have hparent := hselectedData.1
      change address ∈
        ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
          (fun _c ↦ cwChunkSplitWord (depth + 1))
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon).support at hparent
      have hparentData :=
        (Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
          (cwChunkPartitionedTensor K q (depth + 1))
          (fun _c ↦ cwChunkSplitWord (depth + 1))
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon address).1 hparent
      refine ⟨hparentData.1, ?_⟩
      intro physicalLeg
      apply (mem_cwRecursiveApproximateInputTargetParts_iff
        partAt sigma term hmultiplicity epsilon targets coarse
          physicalLeg (address physicalLeg)).2
      refine ⟨htargets physicalLeg, ?_⟩
      simpa only [cwRecursiveParentLabelApproximatelyMatches,
        CompleteSplitDistribution.MatchesEncodedPositiveWordApproximately] using
          hparentData.2 physicalLeg
    · rintro ⟨hfull, hinput⟩
      have htargets : ∀ physicalLeg,
          address physicalLeg ∈ cwRecursiveExactTargetFiberParts
            partAt sigma targets coarse physicalLeg := by
        intro physicalLeg
        exact ((mem_cwRecursiveApproximateInputTargetParts_iff
          partAt sigma term hmultiplicity epsilon targets coarse
            physicalLeg (address physicalLeg)).1 (hinput physicalLeg)).1
      have hparent : address ∈
          (cwSelectedApproximateInterfaceTerm K q
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon).support := by
        change address ∈
          ((cwChunkPartitionedTensor K q (depth + 1)).selectEncodedApproximateInterfaceTerm
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (cwRecursiveSemanticParentTerm term hmultiplicity)
            (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
            epsilon).support
        apply (Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
          (cwChunkPartitionedTensor K q (depth + 1))
          (fun _c ↦ cwChunkSplitWord (depth + 1))
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon address).2
        refine ⟨hfull, ?_⟩
        intro physicalLeg
        have happroximatelyMatches :=
          ((mem_cwRecursiveApproximateInputTargetParts_iff
            partAt sigma term hmultiplicity epsilon targets coarse
              physicalLeg (address physicalLeg)).1 (hinput physicalLeg)).2
        simpa only [cwRecursiveParentLabelApproximatelyMatches,
          CompleteSplitDistribution.MatchesEncodedPositiveWordApproximately] using
            happroximatelyMatches
      refine ⟨?_, htargets⟩
      apply (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
        K q term hmultiplicity epsilon sigma alpha address).2
      refine ⟨hparent, ?_⟩
      intro physicalLeg
      simpa only [CWRecursiveKeepsAlphaMarginal] using
        (CWRecursiveKeepsAlphaMarginal_of_mem_cwRecursiveExactTargetFiberParts
          partAt term sigma alpha targets coarse hcoarse physicalLeg
            (address physicalLeg) (htargets physicalLeg))
  · rfl

end AlgebraicComplexity.Examples
