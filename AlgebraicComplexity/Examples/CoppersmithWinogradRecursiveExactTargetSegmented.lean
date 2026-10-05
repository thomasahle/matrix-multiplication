/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetConditionalCore
import AlgebraicComplexity.MatrixMultiplication.ConditionalTypeSegmentedRestriction

set_option autoImplicit false

/-!
# Recursive CW exact targets as segmented families

The exact target alphabet of a recursive Coppersmith--Winograd constituent fixes a complete
split-word profile separately inside every tagged oriented child cell.  This module rewrites that
condition in the segmented form used by the inner leaf extraction: the source cell at every
labelled-child position is enumerated by `Fintype.equivFin`, and each segment retains precisely
the split-word multiplicity prescribed by `CompatibilityTargets.exactProfile`.

The part component of a cell remains visible.  A client may therefore take `Part` to contain the
recursive invocation and region, as required by the family `L_t(\boldsymbol\tau)` in the
Total-Weight manuscript.  The statement does not add the lower recurrence state or complementary
side as extra tags: Claim 6.18 of [alman2025more] pools those contributions inside the same
`(invocation, region, i',j',k')` cell.

This is only a spelling equivalence.  It proves no tensor restriction, compatibility estimate,
cardinality bound, asymptotic rate, certificate instantiation, or matrix-multiplication endpoint.

The fixed-cell condition is used in the proof of Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:376-440`; that claim proves the associated entropy/count
bound.  This module provides the selector interface needed to construct, but does not itself
construct or audit, the segmented whole family required by `better_bound/paper.tex:1691-1775`.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Enumerate the tagged oriented child cell seen at every labelled-child position.

The enumeration is used only to present the finite cell fibers as `Fin` segments.  Its order has
no mathematical significance, because the public membership theorem translates every segment
back through `Fintype.equivFin.symm`. -/
noncomputable def cwRecursiveExactTargetSegmentation
    {Part : Type v} [Fintype Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : CWRecursiveCoarseAddress depth n) :
    Fin ((n + 1) + (n + 1)) →
      Fin (Fintype.card (CWOrientedCoarseCell Part depth)) :=
  WordType.finiteCellSegmentation
    (cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference)

/-- A parent belongs to the recursive exact target fiber exactly when every tagged child-cell
segment has its prescribed complete split-word multiplicity.

Distinct values of `Part` remain distinct segments even if their numerical profiles happen to
agree.  Conversely, the statement imposes no untagged global type that could move mass between
invocations or regions.

Proof sketch: the existing CW target theorem identifies parent membership with a conditional type
class over bounded `(cell, split word)` pairs.  Apply the generic conditional-type/segmented-type
equivalence, using the same finite cell sequence as the segment map. -/
theorem mem_cwRecursiveExactTargetFiberParts_iff_segmentMultiplicity
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    parent ∈ cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg) ↔
      ∀ segment : Fin (Fintype.card (CWOrientedCoarseCell Part depth)),
        segmentMultiplicity
            (cwRecursiveExactTargetSegmentation depth n partAt sigma reference)
            (cwRecursiveLabelledChildrenEquiv depth n parent) segment =
          fun word ↦ targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex
              ((Fintype.equivFin (CWOrientedCoarseCell Part depth)).symm segment)) word := by
  rw [mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
    partAt sigma targets hsupported hcoarseSupported reference logicalLeg parent]
  simpa only [cwRecursiveExactTargetSegmentation] using
    (WordType.mem_conditionalTypeClass_iff_segmentMultiplicity
      (cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference)
      (fun pair : CWOrientedCoarseCell Part depth × SplitWord depth ↦
        targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex pair.1) pair.2)
      (cwRecursiveLabelledChildrenEquiv depth n parent))

end AlgebraicComplexity.Examples
