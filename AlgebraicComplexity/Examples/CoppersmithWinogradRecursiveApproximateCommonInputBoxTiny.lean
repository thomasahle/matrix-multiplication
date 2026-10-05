/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateCommonInputBox
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypedLeaf

set_option autoImplicit false

/-!
# A genuine one-sample client of the recursive common-input box

This module is a satisfiability and composition regression for the finite common-box step of the
Total-Weight manuscript, Corollary `cor:recursive-common-input-box`,
`better_bound/paper.tex:1085-1124`.  It also follows the exact recursive constituent selectors in
Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou, *More Asymmetry Yields Faster Matrix
Multiplication* [alman2025more],
`papers/sources/2404.16349/constituent.tex:338-348,473-479`.

At recursion depth zero, outer word depth zero, `q = 1`, and coefficient ring `ℚ`, the
construction starts with the actual supported chunk `cwChunkSupportWitness ℚ 1 1`.  Its three
encoded split words define an exact one-sample interface term.  The ordered left-child word of
that same address defines `alpha`, and its labelled-child cell multiplicities define the exact
compatibility targets.  Thus no independently inhabited profile, coarse address, or target table
is postulated.

The public theorem retains the fine and coarse witnesses.  It proves exact and approximate source
membership, relaxed-ambient membership, the full joint `alpha` law, nonempty approximate-input
parts on every leg, nonempty support of the compact exact-alphabet target box, and an actual
application of the common-box restriction with the source itself as reference.  It is only a
small-model regression: it asserts no counting rate, cleanup estimate, or asymptotic endpoint.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

private abbrev tinyOrientation : Orientation := Equiv.refl Leg

private abbrev TinyPart : Type := PUnit

private def tinyPartAt : Fin 1 → TinyPart :=
  fun _sample ↦ PUnit.unit

/-- The native supported depth-one chunk from which every other tiny datum is reconstructed. -/
private noncomputable def tinyChunk :
    (cwChunkPartitionedTensor ℚ 1 1).support :=
  cwChunkSupportWitness ℚ 1 1

/-- At outer word depth zero, a fine address is definitionally one native chunk address. -/
private noncomputable def tinyFine :
    BlockAddress (fun _physicalLeg ↦ PositiveWord (PositiveWord CWBlock 1) 0) :=
  tinyChunk.1

private theorem tinyFine_mem_positivePower :
    tinyFine ∈ ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0).support := by
  change tinyChunk.1 ∈ (cwChunkPartitionedTensor ℚ 1 1).support
  exact tinyChunk.2

/-- Parent constituent weights read from the actual three encoded chunk words. -/
private noncomputable def tinyIndex : LevelConstituentIndex 1 where
  count physicalLeg := splitWordWeight (cwChunkSplitWord 1 (tinyFine physicalLeg))
  total := by
    have hlegal :=
      cwChunkPartitionedTensor_isEncodedFineLegalOnSupport ℚ 1 1 tinyChunk.1 tinyChunk.2
    change (∑ physicalLeg : Leg,
      splitWordWeight (cwChunkSplitWord 1 (tinyFine physicalLeg))) = 2 ^ (1 + 1)
    unfold splitWordWeight
    rw [Finset.sum_comm]
    calc
      (∑ position : Fin (2 ^ 1), ∑ physicalLeg : Leg,
          ((cwChunkSplitWord 1 (tinyFine physicalLeg) position : SplitDigit) : ℕ)) =
          ∑ _position : Fin (2 ^ 1), 2 := by
            apply Finset.sum_congr rfl
            intro position _hposition
            simpa only [tinyFine, Tensor.sum_leg] using hlegal position
      _ = 2 ^ (1 + 1) := by norm_num

/-- The one-sample exact profile on each leg is concentrated at the chunk actually present. -/
private noncomputable def tinyTerm : ExactInterfaceTermParameters 1 where
  multiplicity := 1
  index := tinyIndex
  split physicalLeg := CompleteSplitProfile.singleton
    (cwChunkSplitWord 1 (tinyFine physicalLeg)) rfl

private theorem tinyFine_mem_exact :
    tinyFine ∈ (cwSelectedExactInterfaceTerm ℚ 1 tinyTerm rfl).support := by
  change tinyFine ∈
    ((cwChunkPartitionedTensor ℚ 1 1).selectEncodedCompleteSplitProfiles
      (fun _physicalLeg ↦ cwChunkSplitWord 1) tinyTerm.index
      (fun physicalLeg ↦ tinyTerm.positivePowerProfile rfl physicalLeg)).support
  rw [Tensor.PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support]
  refine ⟨tinyFine_mem_positivePower, ?_⟩
  intro physicalLeg
  change (CompleteSplitProfile.singleton
      (cwChunkSplitWord 1 (tinyFine physicalLeg)) rfl).IsConsistent
    (cwChunkSplitWord 1 ∘
      positiveWordEquiv (PositiveWord CWBlock 1) 0 (tinyFine physicalLeg))
  rw [show
    cwChunkSplitWord 1 ∘
        positiveWordEquiv (PositiveWord CWBlock 1) 0 (tinyFine physicalLeg) =
      fun _sample : Fin 1 ↦ cwChunkSplitWord 1 (tinyFine physicalLeg) by
    funext sample
    exact congrArg (cwChunkSplitWord 1)
      (congrFun (positiveWordEquiv_zero_apply
        (PositiveWord CWBlock 1) (tinyFine physicalLeg)) sample)]
  exact (CompleteSplitProfile.singleton_isConsistent_const_iff
    (cwChunkSplitWord 1 (tinyFine physicalLeg))
    (cwChunkSplitWord 1 (tinyFine physicalLeg)) rfl).2 rfl

/-- The exact ordered left-child word of the actual fine address. -/
private noncomputable def tinyLeftShapeWord :
    Fin 1 → RecursiveChildShape
      (cwRecursiveLogicalParent tinyTerm tinyOrientation) (coarseTotal 0) :=
  cwRecursiveOrientedLeftChildShapeWord
    ℚ 1 (tinyPartAt 0) tinyTerm rfl tinyOrientation tinyFine tinyFine_mem_exact

/-- The full exact split type is the empirical type of `tinyLeftShapeWord`. -/
private noncomputable def tinyAlpha :
    ExactRecursiveSplitType
      (cwRecursiveLogicalParent tinyTerm tinyOrientation) (coarseTotal 0) 1 where
  count := WordType.multiplicity tinyLeftShapeWord
  total := WordType.sum_multiplicity tinyLeftShapeWord

/-- The labelled-child quotient of the actual fine address. -/
private noncomputable def tinyCoarse : CWRecursiveCoarseAddress 0 0 :=
  cwRecursiveChildGroup 0 0 tinyFine

private theorem tinyCoarse_matchesAlpha :
    CWRecursiveMatchesAlpha tinyOrientation tinyAlpha tinyCoarse := by
  apply (cwRecursiveMatchesAlpha_coarsenBlockAddress_iff
    ℚ 1 tinyTerm rfl tinyOrientation tinyAlpha tinyFine tinyFine_mem_exact).2
  rfl

private theorem tinyFine_mem_approximateInterface :
    tinyFine ∈
      (cwSelectedApproximateInterfaceTerm ℚ 1
        (cwRecursiveSemanticParentTerm tinyTerm rfl)
        (cwRecursiveSemanticParentTerm_multiplicity tinyTerm rfl) 0).support := by
  simpa only [cwRecursiveSemanticParentTerm] using
    cwSelectedExactInterfaceTerm_support_subset_approximate
      ℚ 1 tinyTerm rfl (epsilon := 0) (by norm_num) tinyFine_mem_exact

private theorem tinyFine_mem_approximateAlphaMarginals :
    tinyFine ∈
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        ℚ 1 tinyTerm rfl 0 tinyOrientation tinyAlpha).support := by
  apply (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
    ℚ 1 tinyTerm rfl 0 tinyOrientation tinyAlpha tinyFine).2
  refine ⟨tinyFine_mem_approximateInterface, ?_⟩
  intro physicalLeg
  have hword :
      cwRecursiveLogicalLeftCoordinateWord tinyOrientation tinyCoarse
          (tinyOrientation.symm physicalLeg) =
        cwRecursiveLeftChildWord 0 0 (tinyFine physicalLeg) := by
    funext sample
    simp only [cwRecursiveLogicalLeftCoordinateWord, tinyCoarse,
      cwRecursiveChildGroup, coarsenBlockAddress_apply,
      cwRecursiveChildCoarsening, cwRecursiveLabelledChildWord_left]
    exact congrArg
      (fun leg ↦ cwRecursiveLeftChildWord 0 0 (tinyFine leg) sample)
      (tinyOrientation.apply_symm_apply physicalLeg)
  rw [← hword]
  exact multiplicity_cwRecursiveLogicalLeftCoordinateWord_eq_marginalCount
    tinyOrientation tinyAlpha tinyCoarse tinyCoarse_matchesAlpha
      (tinyOrientation.symm physicalLeg)

private theorem tinyCoarse_mem_actual :
    tinyCoarse ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        ℚ 1 tinyTerm rfl 0 tinyOrientation tinyAlpha).support := by
  change tinyCoarse ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      ℚ 1 tinyTerm rfl 0 tinyOrientation tinyAlpha).coarsen
        (cwRecursiveChildCoarsening 0 0)).support
  rw [PartitionedTensor.coarsen_support, Finset.mem_image]
  exact ⟨tinyFine, tinyFine_mem_approximateAlphaMarginals, rfl⟩

private theorem tinyCoarse_mem_ambient :
    tinyCoarse ∈ cwRecursiveRelaxedAmbientCoarseSupport
      tinyTerm tinyOrientation tinyAlpha :=
  cwRecursiveApproximateCoarsened_support_subset_relaxedAmbient
    ℚ 1 tinyTerm rfl 0 tinyOrientation tinyAlpha tinyCoarse_mem_actual

private abbrev tinyModel :=
  cwRecursiveChildCompatibilityModel 0 0 tinyPartAt

private theorem tinyFine_isFineLegal : tinyModel.IsFineLegal tinyFine :=
  cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_selected_support
    ℚ 1 tinyPartAt tinyTerm rfl tinyFine tinyFine_mem_exact

private theorem tinyFine_hasCoarseWeights : tinyModel.HasCoarseWeights tinyFine := by
  dsimp only [tinyModel, cwRecursiveChildCompatibilityModel]
  exact recursiveChildCompatibilityModel_hasCoarseWeights
    (fun _physicalLeg ↦ cwChunkSplitWord 1) tinyPartAt tinyFine

/-- Exact compatibility rows are the three empirical labelled-child tables of the witness.
The pooled rows are immaterial to the exact target box and are set to zero. -/
private noncomputable def tinyTargets : CompatibilityTargets TinyPart 0 where
  xExact cell word :=
    cellMultiplicity (tinyModel.coarse tinyFine)
      (tinyModel.chunks .X (tinyFine .X)) cell word
  yExact cell word :=
    cellMultiplicity (tinyModel.coarse tinyFine)
      (tinyModel.chunks .Y (tinyFine .Y)) cell word
  zExact cell word :=
    cellMultiplicity (tinyModel.coarse tinyFine)
      (tinyModel.chunks .Z (tinyFine .Z)) cell word
  yPooled := fun _part _total _word ↦ 0
  zPooled := fun _part _total _word ↦ 0
  yBoundary := by
    intro cell hz word
    apply cellMultiplicity_complement
    intro sample hsample
    apply tinyModel.y_eq_complement_x_of_z_eq_zero
      tinyFine tinyFine_isFineLegal tinyFine_hasCoarseWeights sample
    rw [hsample]
    exact hz
  zBoundaryOfX := by
    intro cell hy word
    apply cellMultiplicity_complement
    intro sample hsample
    apply tinyModel.z_eq_complement_x_of_y_eq_zero
      tinyFine tinyFine_isFineLegal tinyFine_hasCoarseWeights sample
    rw [hsample]
    exact hy
  zBoundaryOfY := by
    intro cell hx word
    apply cellMultiplicity_complement
    intro sample hsample
    apply tinyModel.z_eq_complement_y_of_x_eq_zero
      tinyFine tinyFine_isFineLegal tinyFine_hasCoarseWeights sample
    rw [hsample]
    exact hx

private theorem tinyModel_coarse_eq_orientedSequence :
    tinyModel.coarse tinyFine =
      cwRecursiveOrientedCoarseIndexSequence
        0 0 tinyPartAt tinyOrientation tinyCoarse := by
  have h := cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence
    (depth := 0) (n := 0) tinyPartAt tinyOrientation tinyFine
  rw [show logicalAddress tinyOrientation tinyFine = tinyFine by
    funext physicalLeg
    simp only [logicalAddress_apply, tinyOrientation, Equiv.refl_apply]] at h
  simpa only [tinyModel, tinyCoarse] using h

private theorem tinyFine_mem_exactTarget (physicalLeg : Leg) :
    tinyFine physicalLeg ∈ cwRecursiveExactTargetFiberParts
      tinyPartAt tinyOrientation tinyTargets tinyCoarse physicalLeg := by
  apply (mem_cwRecursiveExactTargetFiberParts_iff
    tinyPartAt tinyOrientation tinyTargets tinyCoarse
      physicalLeg (tinyFine physicalLeg)).2
  refine ⟨?_, ?_⟩
  · rfl
  · intro cell word
    rw [← tinyModel_coarse_eq_orientedSequence]
    cases physicalLeg <;> rfl

private theorem tinyFine_parentApproximatelyMatches (physicalLeg : Leg) :
    cwRecursiveParentLabelApproximatelyMatches
      tinyTerm rfl 0 physicalLeg (tinyFine physicalLeg) := by
  have hdata :=
    (Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
      (cwChunkPartitionedTensor ℚ 1 1)
      (fun _physicalLeg ↦ cwChunkSplitWord 1)
      (cwRecursiveSemanticParentTerm tinyTerm rfl)
      (cwRecursiveSemanticParentTerm_multiplicity tinyTerm rfl)
      0 tinyFine).1 tinyFine_mem_approximateInterface
  simpa only [cwRecursiveParentLabelApproximatelyMatches,
    CompleteSplitDistribution.MatchesEncodedPositiveWordApproximately] using
      hdata.2 physicalLeg

private theorem tinyFine_mem_inputTargetPart (physicalLeg : Leg) :
    tinyFine physicalLeg ∈ cwRecursiveApproximateInputTargetParts
      tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse physicalLeg := by
  apply (mem_cwRecursiveApproximateInputTargetParts_iff
    tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse
      physicalLeg (tinyFine physicalLeg)).2
  exact ⟨tinyFine_mem_exactTarget physicalLeg,
    tinyFine_parentApproximatelyMatches physicalLeg⟩

private theorem tinyInputTarget_subset_exactTarget (physicalLeg : Leg) :
    cwRecursiveApproximateInputTargetParts
        tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse physicalLeg ⊆
      cwRecursiveExactTargetFiberParts
        tinyPartAt tinyOrientation tinyTargets tinyCoarse physicalLeg := by
  intro fine hfine
  exact (mem_cwRecursiveApproximateInputTargetParts_iff
    tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse
      physicalLeg fine).1 hfine |>.1

private theorem tinyFine_mem_ambientInputBox :
    tinyFine ∈
      (((cwChunkPartitionedTensor ℚ 1 1).positivePower 0).box
        (cwRecursiveApproximateInputTargetParts
          tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse)).support := by
  apply (PartitionedTensor.mem_box_support
    ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0)
    (cwRecursiveApproximateInputTargetParts
      tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse) tinyFine).2
  exact ⟨tinyFine_mem_positivePower, tinyFine_mem_inputTargetPart⟩

private theorem tinyTargetBox_nonempty :
    ((compactBox
        ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0)
        (cwRecursiveExactTargetFiberParts
          tinyPartAt tinyOrientation tinyTargets tinyCoarse)).box
      (compactBoxSubparts
        (cwRecursiveExactTargetFiberParts
          tinyPartAt tinyOrientation tinyTargets tinyCoarse)
        (cwRecursiveApproximateInputTargetParts
          tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse))).support.Nonempty := by
  rw [compactBox_box_support_eq_map
    ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0)
    (cwRecursiveExactTargetFiberParts
      tinyPartAt tinyOrientation tinyTargets tinyCoarse)
    (cwRecursiveApproximateInputTargetParts
      tinyPartAt tinyOrientation tinyTerm rfl 0 tinyTargets tinyCoarse)
    tinyInputTarget_subset_exactTarget]
  apply Finset.map_nonempty.mpr
  exact ⟨⟨tinyFine, tinyFine_mem_ambientInputBox⟩, Finset.mem_univ _⟩

/-- **The recursive common-input-box theorem has a genuine one-sample CW instance.**

The witnesses retain the exact term, its empirical ordered split type, the empirical target
tables, and both the actual fine and coarse source addresses.  In particular, the restriction in
the final conjunct is not obtained from an abstract inhabitance assumption: its source is the
coarsening of `cwChunkSupportWitness ℚ 1 1`, and its target compact box contains the explicitly
retyped image of that same fine address.

**Proof sketch.** Select the singleton complete-split type realized by the supported chunk.  Its
empirical left-child type supplies `alpha`, so exact support embeds into the zero-tolerance
approximate selector and survives every marginal zero-out.  Define each exact compatibility row
as the corresponding empirical cell multiplicity; fine CW legality proves the three complement
boundary equations.  The original address therefore belongs to every approximate-input target
part.  Retype it into the compact exact alphabet, then invoke the common-box theorem with
`reference = coarse`, for which tagged-type equality is reflexive. -/
theorem cwRecursiveApproximateCommonInputBox_nonvacuous :
    ∃ (partAt : Fin 1 → (PUnit : Type))
      (term : ExactInterfaceTermParameters 1)
      (hmultiplicity : term.multiplicity = 1)
      (alpha : ExactRecursiveSplitType
        (cwRecursiveLogicalParent term (Equiv.refl Leg)) (coarseTotal 0) 1)
      (targets : CompatibilityTargets (PUnit : Type) 0)
      (fine : BlockAddress
        (fun _physicalLeg ↦ PositiveWord (PositiveWord CWBlock 1) 0))
      (coarse : CWRecursiveCoarseAddress 0 0),
      fine ∈ (cwSelectedExactInterfaceTerm ℚ 1 term hmultiplicity).support ∧
      fine ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        ℚ 1 term hmultiplicity 0 (Equiv.refl Leg) alpha).support ∧
      cwRecursiveChildGroup 0 0 fine = coarse ∧
      coarse ∈ (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        ℚ 1 term hmultiplicity 0 (Equiv.refl Leg) alpha).support ∧
      coarse ∈ cwRecursiveRelaxedAmbientCoarseSupport
        term (Equiv.refl Leg) alpha ∧
      CWRecursiveMatchesAlpha (Equiv.refl Leg) alpha coarse ∧
      (∀ physicalLeg,
        (cwRecursiveApproximateInputTargetParts
          partAt (Equiv.refl Leg) term hmultiplicity 0 targets coarse
            physicalLeg).Nonempty) ∧
      ((compactBox
          ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0)
          (cwRecursiveExactTargetFiberParts
            partAt (Equiv.refl Leg) targets coarse)).box
        (compactBoxSubparts
          (cwRecursiveExactTargetFiberParts
            partAt (Equiv.refl Leg) targets coarse)
          (cwRecursiveApproximateInputTargetParts
            partAt (Equiv.refl Leg) term hmultiplicity 0 targets coarse))).support.Nonempty ∧
      Restricts
        ((cwRecursiveApproximateCoarsenedAlphaMarginalTerm
          ℚ 1 term hmultiplicity 0 (Equiv.refl Leg) alpha).constituent coarse)
        (((compactBox
            ((cwChunkPartitionedTensor ℚ 1 1).positivePower 0)
            (cwRecursiveExactTargetFiberParts
              partAt (Equiv.refl Leg) targets coarse)).box
          (compactBoxSubparts
            (cwRecursiveExactTargetFiberParts
              partAt (Equiv.refl Leg) targets coarse)
            (cwRecursiveApproximateInputTargetParts
              partAt (Equiv.refl Leg) term hmultiplicity 0 targets coarse))).realize) := by
  refine ⟨tinyPartAt, tinyTerm, rfl, tinyAlpha, tinyTargets, tinyFine, tinyCoarse,
    tinyFine_mem_exact, tinyFine_mem_approximateAlphaMarginals, rfl,
    tinyCoarse_mem_actual, tinyCoarse_mem_ambient, tinyCoarse_matchesAlpha, ?_, ?_, ?_⟩
  · intro physicalLeg
    exact ⟨tinyFine physicalLeg, tinyFine_mem_inputTargetPart physicalLeg⟩
  · exact tinyTargetBox_nonempty
  · exact
      cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_to_commonInputTargetBox
        ℚ 1 tinyPartAt tinyTerm rfl 0 tinyOrientation tinyAlpha tinyTargets
          tinyCoarse tinyCoarse tinyCoarse_mem_actual tinyCoarse_matchesAlpha
          tinyCoarse_mem_ambient rfl

end AlgebraicComplexity.Examples
