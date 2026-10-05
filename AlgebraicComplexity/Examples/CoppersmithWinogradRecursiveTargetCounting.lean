/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IdentityOrientationCompetitorCount
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetConditionalCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveCompleteSplitOccurrenceLaw

set_option autoImplicit false

/-!
# Exact cardinality of a recursive CW target alphabet

A parent Coppersmith--Winograd chunk is not merely injected into its two labelled child
complete-split words: the native ternary encoding and the consecutive-halves map are both
equivalences.  Consequently the fine labels in one exact recursive target alphabet are
canonically a conditional type class over the full tagged child-cell word.

The main theorem, `card_cwRecursiveExactTargetFiberParts_eq_prod_multinomial`, identifies the
cardinality exactly with the product of the prescribed cell multinomials.  This is the finite
alphabet of the independently assembled standard-form child product.  It need not coincide with
the alphabet present in one exactly selected parent complete-split profile: the missing labels are
the paper's input-profile holes and require a separate typicality estimate.  No hashing,
sparse-hole estimate, tensor restriction, entropy approximation, or certificate-specific number
occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Occurrence-reconstructed target tables inherit tight coarse support from the underlying
labelled occurrences.  This is the standard way recursive CW clients discharge
`CWRecursiveTargetCoarseTotalSupported`; the target table itself is not trusted with a separate
support claim. -/
theorem recursiveOccurrenceTargetData_toCompatibilityTargets_isCoarseTotalSupported
    {State : Type*} [Fintype State]
    {Part : Type v} [DecidableEq Part] {depth : ℕ}
    {profile : State → ℕ}
    {coarseOf : ComplementaryOccurrence State → CoarseIndex Part}
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
          (coarseOf occurrence).z = coarseTotal depth) :
    CWRecursiveTargetCoarseTotalSupported data.toCompatibilityTargets := by
  intro logicalLeg cell word hpositive
  have support_of_positive
      (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
      (h : 0 < recursiveOccurrenceExactProfile coarseOf law cell word) :
      cell.x + cell.y + cell.z = coarseTotal depth := by
    unfold recursiveOccurrenceExactProfile recursiveOccurrencePooledProfile at h
    rw [Finset.sum_pos_iff] at h
    obtain ⟨occurrence, _hoccurrence, hterm⟩ := h
    by_cases hcell : coarseOf occurrence = cell
    · subst cell
      exact htotal occurrence
    · simp [hcell] at hterm
  cases logicalLeg with
  | X => exact support_of_positive (data.law .X) hpositive
  | Y => exact support_of_positive (data.law .Y) hpositive
  | Z => exact support_of_positive (data.law .Z) hpositive

/-- **Exact recursive target-alphabet count.**  For any physical leg, the number of native
parent labels with the prescribed full tagged child-cell table is the product of the cellwise
multinomial coefficients. -/
theorem card_cwRecursiveExactTargetFiberParts_eq_prod_multinomial
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg)
    (hlegal : (fun pair : CWOrientedCoarseCell Part depth × SplitWord depth ↦
        targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex pair.1) pair.2) ∈
      WordType.types (CWOrientedCoarseCell Part depth × SplitWord depth)
        ((n + 1) + (n + 1)))
    (hfst : WordType.mappedType Prod.fst
        (fun pair : CWOrientedCoarseCell Part depth × SplitWord depth ↦
          targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex pair.1) pair.2) =
      WordType.multiplicity
        (cwRecursiveOrientedFiniteCellSequence
          depth n partAt sigma reference)) :
    (cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg)).card =
      ∏ cell : CWOrientedCoarseCell Part depth,
        Nat.multinomial Finset.univ
          (targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex cell)) := by
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
    _ = ∏ cell : CWOrientedCoarseCell Part depth,
        Nat.multinomial Finset.univ
          (targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex cell)) := by
      simpa [source, jointType] using
        WordType.card_conditionalTypeClass_eq_prod_multinomial
          source jointType hlegal hfst

end AlgebraicComplexity.Examples
