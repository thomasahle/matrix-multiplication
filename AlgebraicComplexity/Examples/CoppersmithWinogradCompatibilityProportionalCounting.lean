/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCleanupData
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetRepair
import AlgebraicComplexity.MatrixMultiplication.SparseRepairProportionalCounting

/-!
# Proportional finite bounds for CW compatibility cleanup

This lightweight module turns the explicit full-cell-type and competitor-incidence estimates
into the two cardinality bounds consumed by the finite repair stage.  Keeping this arithmetic
composition separate from the tensor stage makes the certificate boundary easy to audit and
keeps it available without importing the heavier repair-output semantics.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

private theorem fintypeCard_positiveWord_proportional
    (I : Type v) [Fintype I] (n : ℕ) :
    Fintype.card (PositiveWord I n) = Fintype.card I ^ (n + 1) := by
  calc
    Fintype.card (PositiveWord I n) = Fintype.card (Fin (n + 1) → I) :=
      Fintype.card_congr (positiveWordEquiv I n)
    _ = Fintype.card I ^ (n + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]

/-- Aggregate competitor incidence and the half-density budget leave at least half of the
selected full-cell type simultaneously sparse on all three legs. -/
theorem CWCompatibilityCleanupData.fixedTargetCellType_card_le_two_mul_sparse_of_incidence
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
    (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 *
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
        depth n partAt sigma cleanup.coarseKept reference)) :
    Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma cleanup.coarseKept reference) ≤
      2 * (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
          cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference base).card := by
  let model := cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
    targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
      cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference
  have hbound := model.card_total_le_two_mul_typeLoss_mul_sparseIndices
    (Fintype.card (cwFixedTargetCellTypeCoarseSupport
      depth n partAt sigma cleanup.coarseKept reference)) 1 base (by simp) budget
      haggregate hhalf
  simpa only [one_mul, model, cwSparseTargetCellTypeAddresses] using hbound

/-- The proportional sparse-family bound follows from full-cell-type selection, aggregate
competitor incidence, and the half-density budget. -/
theorem CWCompatibilityCleanupData.coarseKept_card_le_proportionalLoss_mul_sparse_of_incidence
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
    (htype : cleanup.coarseKept.card ≤
      (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference))
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
        depth n partAt sigma cleanup.coarseKept reference)) :
    cleanup.coarseKept.card ≤
      (2 * (mass * r + 1) ^
          Fintype.card (CWOrientedCoarseCell Part depth)) *
        (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
          targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
            cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference (r + 2)).card := by
  let model := cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
    targets cleanup.coarseKept cleanup.finalSupport cleanup.projection_closed
      cleanup.exact_profiles cleanup.grouping cleanup.group_eq reference
  have hn : n + 2 = mass * r + 1 := by omega
  have htype' : cleanup.coarseKept.card ≤
      (mass * r + 1) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma cleanup.coarseKept reference) := by
    simpa only [hn] using htype
  exact model.card_total_le_two_mul_typeLoss_mul_sparseIndices
    cleanup.coarseKept.card
      ((mass * r + 1) ^ Fintype.card (CWOrientedCoarseCell Part depth))
      (r + 2) htype' budget haggregate hhalf

/-- Every finite subalphabet of an exact target fiber satisfies the proportional ambient
`3^(2^depth * mass * r)` bound. -/
theorem card_cwExactTargetSubalphabet_le_proportional_three_pow
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n mass r : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsamples : n + 1 = mass * r)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c))
    (c : Leg) :
    (target c).card ≤ 3 ^ ((2 ^ depth * mass) * r) := by
  calc
    (target c).card ≤ Fintype.card (BoxPart
        (cwExactTargetCoarseFiberParts partAt sigma targets reference) c) :=
      Finset.card_le_univ _
    _ = (cwExactTargetCoarseFiberParts partAt sigma targets reference c).card :=
      Fintype_card_BoxPart _ _
    _ ≤ Fintype.card
        (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :=
      Finset.card_le_univ _
    _ = 3 ^ (2 ^ depth * (n + 1)) := by
      rw [fintypeCard_positiveWord_proportional,
        fintypeCard_positiveWord_proportional]
      have htwo : 2 ^ depth - 1 + 1 = 2 ^ depth :=
        Nat.sub_add_cancel Nat.one_le_two_pow
      rw [htwo, show Fintype.card CWBlock = 3 by rfl, ← pow_mul]
    _ = 3 ^ ((2 ^ depth * mass) * r) := by
      rw [hsamples, mul_assoc]

end AlgebraicComplexity.Examples
