/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputBox
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputTransport
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursivePresentExactTargetFiber
import AlgebraicComplexity.Tensor.PartitionedBoxRetyping

set_option autoImplicit false

/-!
# A common approximate-input box for recursive CW constituents

This module formalizes Corollary `cor:recursive-common-input-box` of the Total-Weight manuscript,
`better_bound/paper.tex:1085-1124`.  It follows the recursive constituent argument of
Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou, *More Asymmetry Yields Faster Matrix
Multiplication* [alman2025more], especially
`papers/sources/2404.16349/constituent.tex:338-348,473-479`.

An actually supported coarse constituent is first restricted to its present exact-target fiber.
For an exact-`alpha` coarse address, the finite selector identity identifies that fiber with the
full parent positive power boxed by the approximate-input target alphabet.  A single paired
parent-position permutation then transports all three leg alphabets to any relaxed-ambient
reference address having the same tagged ordered-left empirical type.  Finally, the ambient box
is compactly reindexed inside that reference address's exact target alphabets.

This is deliberately a pre-cleanup result.  It proves neither that compatibility cleanup leaves
the common box intact nor that the box is the independently assembled standard child product.
Hole bounds, repair, and the degeneration to that standard child remain downstream obligations.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- One explicit paired parent-position relabeling identifies the approximate-input boxes over
the source and target coarse addresses.

The direction is from `right` to `left`, matching
`cwRecursivePositionRelabelCoarseAddress depth n tau right = left`.

**Proof sketch.** The positive parent power admits a structure relabeling whose action on every
physical leg is the same positive-word position permutation `tau`.  The alphabet-transport
identity says that relabeling carries the three approximate-input target parts over `right`
exactly to those over `left`; the generic box-isomorphism theorem then gives the result. -/
theorem cwRecursiveApproximateInputTargetBox_isomorphic_of_positionRelabel
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (targets : CompatibilityTargets Part depth)
    (left right : CWRecursiveCoarseAddress depth n)
    (tau : Equiv.Perm (Fin (n + 1)))
    (hpart : partAt ∘ tau = partAt)
    (hcoarse : cwRecursivePositionRelabelCoarseAddress depth n tau right = left) :
    Isomorphic
      ((((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets right)).realize)
      ((((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets left)).realize) := by
  classical
  let relabeling :=
    PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
      (cwChunkPartitionedTensor K q (depth + 1)) n tau
  have hparts :
      relabelParts relabeling.partEquiv
          (cwRecursiveApproximateInputTargetParts
            partAt sigma term hmultiplicity epsilon targets right) =
        cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets left := by
    rw [show relabeling.partEquiv = fun _physicalLeg ↦
        positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau by
      funext physicalLeg
      exact
        PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
          (cwChunkPartitionedTensor K q (depth + 1)) n tau physicalLeg]
    exact relabelParts_cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets left right tau hpart hcoarse
  have hisomorphic := relabeling.box_isomorphic
    (cwRecursiveApproximateInputTargetParts
      partAt sigma term hmultiplicity epsilon targets right)
  rw [hparts] at hisomorphic
  exact hisomorphic

/-- Every supported exact-`alpha` recursive constituent restricts to the same approximate-input
box as any relaxed-ambient reference address of the same tagged ordered-left empirical type.

This is the finite tensor statement of Total-Weight Corollary
`cor:recursive-common-input-box`, `better_bound/paper.tex:1085-1124`.

**Proof sketch.** Restrict the actual coarse constituent to all exact-target fine addresses that
are genuinely present.  The exact-`alpha` selector identity rewrites this target as the full
parent positive-power box over the source approximate-input alphabets.  The canonical
same-tagged-type permutation preserves the region map and carries the entire source coarse
address to the reference address.  Apply the preceding simultaneous three-leg box isomorphism,
then compactly reindex its retained labels inside the reference exact-target alphabets. -/
theorem
    cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_to_commonInputTargetBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (coarse reference : CWRecursiveCoarseAddress depth n)
    (hcoarseSupported : coarse ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    (hcoarseAlpha : CWRecursiveMatchesAlpha sigma alpha coarse)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hsame : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma reference) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma coarse)) :
    Restricts
      ((cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).constituent coarse)
      (((compactBox
          ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
          (cwRecursiveExactTargetFiberParts
            partAt sigma targets reference)).box
        (compactBoxSubparts
          (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
          (cwRecursiveApproximateInputTargetParts
            partAt sigma term hmultiplicity epsilon targets reference))).realize) := by
  classical
  have hcoarseAmbient : coarse ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha :=
    cwRecursiveApproximateCoarsened_support_subset_relaxedAmbient
      K q term hmultiplicity epsilon sigma alpha hcoarseSupported
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma reference coarse hsame
  have hpart : partAt ∘ tau = partAt :=
    partAt_comp_cwRecursivePositionPermOfSameTaggedMultiplicity
      partAt sigma reference coarse hsame
  have hcoarseRelabel :
      cwRecursivePositionRelabelCoarseAddress depth n tau coarse = reference := by
    dsimp only [tau]
    exact cwRecursivePositionRelabelCoarseAddress_of_relaxedAmbient_sameTaggedMultiplicity
      partAt term sigma alpha reference coarse hreference hcoarseAmbient hsame
  have hlocal :=
    cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_to_presentExactTargetFiber
      K q partAt term hmultiplicity epsilon sigma alpha targets coarse hcoarseSupported
  rw [cwRecursiveApproximateSelected_box_exactTarget_eq_inputTargetBox
    K q partAt term hmultiplicity epsilon sigma alpha targets coarse hcoarseAlpha] at hlocal
  have htransport :=
    cwRecursiveApproximateInputTargetBox_isomorphic_of_positionRelabel
      K q partAt sigma term hmultiplicity epsilon targets reference coarse tau
        hpart hcoarseRelabel
  have hsubset : ∀ physicalLeg,
      cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets reference physicalLeg ⊆
        cwRecursiveExactTargetFiberParts
          partAt sigma targets reference physicalLeg := by
    intro physicalLeg fine hfine
    exact (mem_cwRecursiveApproximateInputTargetParts_iff
      partAt sigma term hmultiplicity epsilon targets reference physicalLeg fine).1 hfine |>.1
  exact hlocal.trans (htransport.restricts.trans
    (Restricts.box_to_compactBox_box
      ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
      (cwRecursiveExactTargetFiberParts partAt sigma targets reference)
      (cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets reference)
      hsubset))

end AlgebraicComplexity.Examples
