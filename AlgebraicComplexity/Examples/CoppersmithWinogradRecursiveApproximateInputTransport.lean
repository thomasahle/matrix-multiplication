/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputHoles

set_option autoImplicit false

/-!
# Paired transport of recursive CW approximate-input target alphabets

This module formalizes the alphabet-transport part of the paired fiber normalization in the
Total-Weight manuscript, `better_bound/paper.tex`, Lemma `lem:paired-recursive-normalization`,
lines 975--998.

A parent-position permutation acts simultaneously on the labelled left and right child belonging
to each parent.  If it preserves the region tags and sends one full coarse child address to another,
then it transports the exact target alphabet.  The approximate parent-input predicate is invariant
under the same action, so their intersection—the approximate-input target alphabet—is
transported exactly as well.

No tensor support, cleanup survivor, hole bound, or independent permutation of the doubled child
positions is used here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- A paired parent-position permutation transports membership in the approximate-input target
alphabet in both directions.

**Proof sketch.** In the forward direction, exact-target membership is transported by applying the
existing theorem to the inverse permutation; the inverse preserves tags and carries the left coarse
address back to the right one.  In the reverse direction, use the given permutation directly.
Approximate profile membership is invariant under position permutations in both directions. -/
theorem cwRecursiveApproximateInputTargetParts_positionRelabel_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (targets : CompatibilityTargets Part depth)
    (left right : CWRecursiveCoarseAddress depth n)
    (tau : Equiv.Perm (Fin (n + 1)))
    (hpart : partAt ∘ tau = partAt)
    (hcoarse : cwRecursivePositionRelabelCoarseAddress depth n tau right = left)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau fine ∈
        cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets left physicalLeg ↔
      fine ∈ cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets right physicalLeg := by
  classical
  let Fine := PositiveWord CWBlock (2 ^ (depth + 1) - 1)
  let moved := positiveWordPositionEquiv Fine n tau fine
  have happrox :
      cwRecursiveParentLabelApproximatelyMatches
          term hmultiplicity epsilon physicalLeg moved ↔
        cwRecursiveParentLabelApproximatelyMatches
          term hmultiplicity epsilon physicalLeg fine := by
    simpa only [moved, Fine, cwRecursiveParentLabelApproximatelyMatches] using
      ((cwRecursiveSemanticParentTerm term hmultiplicity).split
        physicalLeg).matchesEncodedPositiveWordApproximately_positionEquiv_iff
          (cwChunkSplitWord (depth + 1)) fine tau epsilon
  rw [mem_cwRecursiveApproximateInputTargetParts_iff,
    mem_cwRecursiveApproximateInputTargetParts_iff]
  constructor
  · rintro ⟨htarget, happroximatelyMatches⟩
    have hpartSymm : partAt ∘ tau.symm = partAt := by
      funext sample
      have h := congrFun hpart (tau.symm sample)
      simpa using h.symm
    have hcoarseSymm :
        cwRecursivePositionRelabelCoarseAddress depth n tau.symm left = right := by
      rw [← hcoarse]
      funext leg occurrence
      refine Fin.addCases ?_ ?_ occurrence <;> intro sample
      · simp only [cwRecursivePositionRelabelCoarseAddress_left, Equiv.apply_symm_apply]
      · simp only [cwRecursivePositionRelabelCoarseAddress_right, Equiv.apply_symm_apply]
    have htargetBack := cwRecursiveExactTargetFiberParts_positionRelabel
      partAt sigma targets right left tau.symm hpartSymm hcoarseSymm physicalLeg htarget
    have hinverse : positiveWordPositionEquiv Fine n tau.symm moved = fine := by
      change positiveWordPositionEquiv Fine n tau.symm
        (positiveWordPositionEquiv Fine n tau fine) = fine
      have hmul := congrArg (fun e ↦ e fine)
        (positiveWordPositionEquiv_mul Fine n tau tau.symm)
      have hone : tau * tau.symm = 1 := by
        apply Equiv.ext
        intro sample
        simp
      rw [hone, positiveWordPositionEquiv_one] at hmul
      exact hmul.symm
    rw [hinverse] at htargetBack
    exact ⟨htargetBack, happrox.mp happroximatelyMatches⟩
  · rintro ⟨htarget, happroximatelyMatches⟩
    exact ⟨cwRecursiveExactTargetFiberParts_positionRelabel
        partAt sigma targets left right tau hpart hcoarse physicalLeg htarget,
      happrox.mpr happroximatelyMatches⟩

/-- Relabelling all three physical-leg alphabets by one paired parent-position permutation carries
the right approximate-input target box alphabet exactly to the left one.

**Proof sketch.** Extensionality reduces the statement to one moved label on one leg.
`mem_relabelParts` pulls that label back by the inverse equivalence, and the preceding membership
iff finishes. -/
theorem relabelParts_cwRecursiveApproximateInputTargetParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (targets : CompatibilityTargets Part depth)
    (left right : CWRecursiveCoarseAddress depth n)
    (tau : Equiv.Perm (Fin (n + 1)))
    (hpart : partAt ∘ tau = partAt)
    (hcoarse : cwRecursivePositionRelabelCoarseAddress depth n tau right = left) :
    relabelParts
        (fun _physicalLeg ↦ positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau)
        (cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets right) =
      cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets left := by
  classical
  funext physicalLeg
  ext moved
  rw [mem_relabelParts]
  simpa using
    (cwRecursiveApproximateInputTargetParts_positionRelabel_iff
      partAt sigma term hmultiplicity epsilon targets left right tau hpart hcoarse
        physicalLeg
        ((positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau).symm moved)).symm

end AlgebraicComplexity.Examples
