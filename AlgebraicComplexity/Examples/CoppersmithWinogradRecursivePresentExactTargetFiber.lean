/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInput
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiberCore
import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# Present exact target fibers of recursive approximate constituents

A constituent of the labelled-child quotient is the sum of all fine constituents in its coarse
fiber.  This module further selects every fine leg label whose complete child table is the requested
exact target.  The resulting box is still based on the approximate marginal-selected source, so it
contains exactly the requested fine addresses that are actually present; it does not assert that
the larger compact exact box has no input-profile holes.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- One supported recursive approximate coarse constituent restricts to all exact-target fine
addresses actually present over that constituent.

The target is a box of the approximate marginal-selected partition.  Consequently its support is
the intersection of the exact target parts with the genuine source support, rather than an
unconditional full exact box. -/
theorem
    cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_to_presentExactTargetFiber
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n)
    (hcoarse : coarse ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support) :
    Restricts
      ((cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).constituent coarse)
      (((cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).box
          (cwRecursiveExactTargetFiberParts partAt sigma targets coarse)).realize) := by
  classical
  let P := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let f := cwRecursiveChildCoarsening depth n
  let keep : ∀ c,
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n → Prop :=
    fun c fine ↦ fine ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets coarse c
  change Restricts ((P.coarsen f).constituent coarse)
    (P.box (cwRecursiveExactTargetFiberParts partAt sigma targets coarse)).realize
  have hcoarse' : coarse ∈ (P.coarsen f).support := hcoarse
  have hrestrict := Tensor.Restricts.coarsen_constituent_to_fineFiberSelect
    P f coarse hcoarse' keep
  rw [PartitionedTensor.coarseningFiber_select_eq_box] at hrestrict
  have hparts :
      coarseningFiberSelectParts f coarse keep =
        cwRecursiveExactTargetFiberParts partAt sigma targets coarse := by
    funext physicalLeg
    ext fine
    rw [mem_coarseningFiberSelectParts]
    change
      (cwRecursiveLabelledChildWord depth n fine = coarse physicalLeg ∧
        fine ∈ cwRecursiveExactTargetFiberParts
          partAt sigma targets coarse physicalLeg) ↔
      fine ∈ cwRecursiveExactTargetFiberParts
        partAt sigma targets coarse physicalLeg
    constructor
    · exact And.right
    · intro hfine
      exact ⟨(mem_cwRecursiveExactTargetFiberParts_iff
        partAt sigma targets coarse physicalLeg fine).1 hfine |>.1, hfine⟩
  rw [hparts] at hrestrict
  exact hrestrict

end AlgebraicComplexity.Examples
