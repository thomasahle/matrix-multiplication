/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFiniteStage
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityProportionalCounting

/-!
# Proportional finite CW compatibility stages

This module derives both finite hypotheses consumed by the fixed-type repair stage.  Aggregate
competitor incidence plus the half-density budget leaves at least half of the selected type
simultaneously sparse, while inclusion in the ambient exact target alphabet gives the target-size
bound.  The remaining premise is only the intact-box matrix-multiplication restriction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- A constructed compatibility cleanup satisfying the explicit incidence estimates produces
the exact fixed-type number of intact rectangular matrix-multiplication copies. -/
theorem CWCompatibilityCleanupData.nonempty_proportionalFixedTypeTargetOutputWholeStage_of_incidence
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    {source : Tensor3 K S}
    (cleanup : CWCompatibilityCleanupData K q partAt term hmultiplicity sigma targets source)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (mass r : ℕ) (hsamples : n + 1 = mass * r)
    (budget : Leg → ℕ)
    (haggregate : ∀ c,
      (r + 2) * 4 *
          ∑ coarse : cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma cleanup.coarseKept reference,
            ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
                cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference).holes
                  coarse c).card ≤
        budget c *
          Fintype.card (BoxPart
            (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤
      Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma cleanup.coarseKept reference))
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K source
      (cwFixedTypeTargetRepairOutputCount (2 ^ depth * mass) r
        (Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference)))
      xSize ySize zSize) := by
  have hfixed := cleanup.fixedTargetCellType_card_le_two_mul_sparse_of_incidence
    K q partAt term hmultiplicity sigma targets reference (r + 2) budget
      haggregate hhalf
  have htarget : ∀ c, (target c).card ≤ 3 ^ ((2 ^ depth * mass) * r) := by
    intro c
    exact card_cwExactTargetSubalphabet_le_proportional_three_pow
      partAt sigma targets reference hsamples target c
  exact cleanup.nonempty_fixedTypeTargetOutputWholeStage
    K q partAt term hmultiplicity sigma targets reference (2 ^ depth * mass) r target
      hfixed htarget xSize ySize zSize hbox

/-- Concrete oriented-hash form of
`CWCompatibilityCleanupData.nonempty_proportionalFixedTypeTargetOutputWholeStage_of_incidence`.
Every semantic cleanup field is constructed from the affine hash and exact compatibility
zero-outs. -/
theorem nonempty_cwOrientedHashCleanup_proportionalFixedTypeTargetOutputWholeStage_of_incidence
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    {depth : ℕ} (encoding : CWCoarseFieldEncoding R depth)
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (mass r : ℕ) (hsamples : n + 1 = mass * r)
    (budget : Leg → ℕ)
    (haggregate :
      let cleanup := cwOrientedHashCompatibilityCleanupData
        encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
      ∀ c,
        (r + 2) * 4 *
            ∑ coarse : cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma cleanup.coarseKept reference,
              ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
                targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
                  cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference).holes
                    coarse c).card ≤
          budget c *
            (cwExactTargetCoarseFiberParts
              partAt sigma targets reference c).card)
    (hhalf :
      let cleanup := cwOrientedHashCompatibilityCleanupData
        encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
      2 * (budget .X + budget .Y + budget .Z) ≤
        Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference))
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (xSize ySize zSize : ℕ)
    (hbox : Restricts
      (cwExactTargetBoxTensor K q partAt term hmultiplicity sigma targets reference target)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    let cleanup := cwOrientedHashCompatibilityCleanupData
      encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
    Nonempty (WholeConstituentLaserVolumeStage.{0, 0, 0} K
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (cwFixedTypeTargetRepairOutputCount (2 ^ depth * mass) r
        (Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference)))
      xSize ySize zSize) := by
  let cleanup := cwOrientedHashCompatibilityCleanupData
    encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
  have haggregate' : ∀ c,
      (r + 2) * 4 *
          ∑ coarse : cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma cleanup.coarseKept reference,
            ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
                cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference).holes
                  coarse c).card ≤
        budget c *
          Fintype.card (BoxPart
            (cwExactTargetCoarseFiberParts partAt sigma targets reference) c) := by
    intro c
    simpa only [Fintype_card_BoxPart] using haggregate c
  exact cleanup.nonempty_proportionalFixedTypeTargetOutputWholeStage_of_incidence
    K q partAt term hmultiplicity sigma targets reference mass r hsamples
      budget haggregate' hhalf target xSize ySize zSize hbox

end AlgebraicComplexity.Examples
