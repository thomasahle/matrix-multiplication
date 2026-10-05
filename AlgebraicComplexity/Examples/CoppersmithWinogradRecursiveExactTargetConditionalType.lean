/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting

set_option autoImplicit false

/-!
# Recursive exact targets as conditional type classes

The native recursive Coppersmith--Winograd target alphabet is equinumerous with its matching
conditional type class.  This is an exact finite equivalence and needs no entropy estimate or
multinomial side condition.  The second theorem permits clients to name the joint profile,
avoiding repeated normalization of large dependent expressions at certificate nodes.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- The exact recursive target alphabet and its native conditional type class have equal size. -/
theorem card_cwRecursiveExactTargetFiberParts_eq_card_conditionalTypeClass
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg) :
    (cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg)).card =
      (WordType.conditionalTypeClass
        (cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference)
        (fun pair : CWOrientedCoarseCell Part depth × SplitWord depth ↦
          targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex pair.1) pair.2)).card := by
  classical
  let target := cwRecursiveExactTargetFiberParts
    partAt sigma targets reference (sigma logicalLeg)
  let encode := cwRecursiveLabelledChildrenEquiv depth n
  let source := cwRecursiveOrientedFiniteCellSequence
    depth n partAt sigma reference
  let jointType : CWOrientedCoarseCell Part depth × SplitWord depth → ℕ :=
    fun pair ↦ targets.exactProfile logicalLeg
      (cwOrientedCoarseCellToIndex pair.1) pair.2
  have himage : target.image encode =
      WordType.conditionalTypeClass source jointType := by
    ext children
    constructor
    · intro hchildren
      obtain ⟨parent, hparent, rfl⟩ := Finset.mem_image.mp hchildren
      exact (mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
        partAt sigma targets hsupported hcoarseSupported reference logicalLeg parent).1 hparent
    · intro hchildren
      let parent := encode.symm children
      have hparent : parent ∈ target := by
        apply (mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
          partAt sigma targets hsupported hcoarseSupported reference logicalLeg parent).2
        simpa [parent, encode, source, jointType] using hchildren
      exact Finset.mem_image.mpr
        ⟨parent, hparent, encode.apply_symm_apply children⟩
  calc
    target.card = (target.image encode).card :=
      (Finset.card_image_of_injective target encode.injective).symm
    _ = (WordType.conditionalTypeClass source jointType).card := by rw [himage]

/-- A named joint profile may replace the native target-profile function without changing the
cardinality bridge. -/
theorem card_cwRecursiveExactTargetFiberParts_eq_card_conditionalTypeClass_of_joint_eq
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg)
    (jointProfile : CWOrientedCoarseCell Part depth × SplitWord depth → ℕ)
    (hjoint : jointProfile = fun pair ↦
      targets.exactProfile logicalLeg
        (cwOrientedCoarseCellToIndex pair.1) pair.2) :
    (cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg)).card =
      (WordType.conditionalTypeClass
        (cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference)
        jointProfile).card := by
  subst jointProfile
  exact card_cwRecursiveExactTargetFiberParts_eq_card_conditionalTypeClass
    partAt sigma targets hsupported hcoarseSupported reference logicalLeg

end AlgebraicComplexity.Examples
