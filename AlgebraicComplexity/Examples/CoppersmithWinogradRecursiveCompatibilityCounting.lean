/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCompatibility
import AlgebraicComplexity.MatrixMultiplication.OrientedCompatibilityCounting
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityInjective

set_option autoImplicit false

/-!
# Loss-free recursive CW compatibility counts

At a positive recursive CW node, every parent position exposes two labelled child chunks.  For a
fixed coarse parent triple, the paper's `Y` and `Z` compatibility cells reveal only the relevant
boundary triple or pooled coordinate, while the target table prescribes the complete-split word
counts inside each cell.  The conditional method of types therefore counts the compatible fine
labels by an exact product of cell multinomials.

These theorems hold at every recursive depth and in every orientation, including repeated
orientations.  They neither assume a hashing conclusion nor an assembled restriction, survivor
family, hole-repair statement, or matrix-multiplication leaf.  A later finite-stage client must
still identify the concrete candidate-label set and prove that its retained pivot label survived
the first zero-out.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe v

/-- The recursive CW compatibility model remembers the complete parent word on every leg. -/
theorem cwRecursiveChildCompatibilityModel_chunks_injective
    {Part : Type v} (depth n : ℕ) (partAt : Fin (n + 1) → Part) (c : Leg) :
    Function.Injective ((cwRecursiveChildCompatibilityModel depth n partAt).chunks c) := by
  exact recursiveChildCompatibilityModel_chunks_injective
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt
      (fun _c ↦ cwChunkSplitWord_injective (depth + 1)) c

/-! ## Logical Y -/

/-- Loss-free logical-`Y` compatibility count for labelled children of a recursive CW node. -/
theorem cwRecursive_card_orientedCompatibleLabelsY_le_prod_multinomial
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hlegal : (fun pair : ObservedCell
        ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
          (logicalAddress sigma address)) × SplitWord depth ↦
          targets.yCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell
        ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
          (logicalAddress sigma address)) × SplitWord depth)
        ((n + 1) + (n + 1)))
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
              (logicalAddress sigma address)) × SplitWord depth ↦
          targets.yCellProfile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord
        ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
          (logicalAddress sigma address)))) :
    (compatibleLabels labels
      (OrientedCompatibleY sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsY_le_prod_multinomial
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      hlegal hfst
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Y).injOn

/-- The pivot label supplies legality and the source-cell marginal after compatibility
soundness. -/
theorem cwRecursive_card_orientedCompatibleLabelsY_le_prod_multinomial_of_self
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hself_mem : address (sigma .Y) ∈ labels)
    (hself : OrientedCompatibleY sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
        (address (sigma .Y)) address) :
    (compatibleLabels labels
      (OrientedCompatibleY sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsY_le_prod_multinomial_of_self
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Y).injOn
      hself_mem hself

/-- Logical-`Y` count directly from the first-zero-out invariants. -/
theorem cwRecursive_card_orientedCompatibleLabelsY_le_prod_multinomial_of_passes
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hself_mem : address (sigma .Y) ∈ labels)
    (hpasses : (cwRecursiveChildCompatibilityModel depth n partAt).PassesYFirstZeroOut
      targets (logicalAddress sigma address)) :
    (compatibleLabels labels
      (OrientedCompatibleY sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).yCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsY_le_prod_multinomial_of_passes
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Y).injOn
      hself_mem hpasses

/-! ## Logical Z -/

/-- Loss-free logical-`Z` compatibility count for labelled children of a recursive CW node. -/
theorem cwRecursive_card_orientedCompatibleLabelsZ_le_prod_multinomial
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hlegal : (fun pair : ObservedCell
        ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
          (logicalAddress sigma address)) × SplitWord depth ↦
          targets.zCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell
        ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
          (logicalAddress sigma address)) × SplitWord depth)
        ((n + 1) + (n + 1)))
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
              (logicalAddress sigma address)) × SplitWord depth ↦
          targets.zCellProfile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord
        ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
          (logicalAddress sigma address)))) :
    (compatibleLabels labels
      (OrientedCompatibleZ sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsZ_le_prod_multinomial
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      hlegal hfst
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Z).injOn

/-- The pivot label supplies legality and the source-cell marginal after compatibility
soundness. -/
theorem cwRecursive_card_orientedCompatibleLabelsZ_le_prod_multinomial_of_self
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hself_mem : address (sigma .Z) ∈ labels)
    (hself : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) targets
        (address (sigma .Z)) address) :
    (compatibleLabels labels
      (OrientedCompatibleZ sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsZ_le_prod_multinomial_of_self
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Z).injOn
      hself_mem hself

/-- Logical-`Z` count directly from the first-zero-out invariants. -/
theorem cwRecursive_card_orientedCompatibleLabelsZ_le_prod_multinomial_of_passes
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hself_mem : address (sigma .Z) ∈ labels)
    (hpasses : (cwRecursiveChildCompatibilityModel depth n partAt).PassesZFirstZeroOut
      targets (logicalAddress sigma address)) :
    (compatibleLabels labels
      (OrientedCompatibleZ sigma
        (cwRecursiveChildCompatibilityModel depth n partAt) targets)
      address).card ≤
        ∏ cell : ObservedCell
            ((cwRecursiveChildCompatibilityModel depth n partAt).zCellWord
              (logicalAddress sigma address)),
          Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  exact CompatibilityModel.card_orientedCompatibleLabelsZ_le_prod_multinomial_of_passes
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets labels address
      (cwRecursiveChildCompatibilityModel_chunks_injective depth n partAt .Z).injOn
      hself_mem hpasses

end AlgebraicComplexity.Examples
