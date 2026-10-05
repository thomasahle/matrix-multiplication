/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetFiber
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCoarsening

set_option autoImplicit false

/-!
# Exact target alphabets inside recursive CW cleanup fibers

This dependency-light module defines the exact alphabet used by sparse repair inside one
recursive Coppersmith--Winograd quotient fiber. A fine parent label belongs to that alphabet
exactly when its labelled-child quotient word is fixed and its complete-split table agrees with
the prescribed target in every tagged logical child cell.

Position normalization of these alphabets is downstream in
`CoppersmithWinogradRecursiveTargetFiber`. Keeping it separate lets finite target counting use
the semantic alphabet without importing competitor bounds, hashing, or normalization.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Read a complete recursive quotient address as a tagged logical coarse-index word. -/
def cwRecursiveOrientedCoarseIndexSequence
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarse : CWRecursiveCoarseAddress depth n) :
    Fin ((n + 1) + (n + 1)) → CoarseIndex Part :=
  fun occurrence ↦
    { part := labelledChildParts partAt occurrence
      x := coarse (sigma .X) occurrence
      y := coarse (sigma .Y) occurrence
      z := coarse (sigma .Z) occurrence }

@[simp] theorem cwRecursiveOrientedCoarseIndexSequence_part
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarse : CWRecursiveCoarseAddress depth n)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    (cwRecursiveOrientedCoarseIndexSequence
      depth n partAt sigma coarse occurrence).part =
      labelledChildParts partAt occurrence :=
  rfl

@[simp] theorem cwRecursiveOrientedCoarseIndexSequence_get
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarse : CWRecursiveCoarseAddress depth n)
    (occurrence : Fin ((n + 1) + (n + 1))) (logicalLeg : Leg) :
    (cwRecursiveOrientedCoarseIndexSequence
      depth n partAt sigma coarse occurrence).get logicalLeg =
      coarse (sigma logicalLeg) occurrence := by
  cases logicalLeg <;> rfl

/-- Fine parent labels over one recursive quotient coordinate which realize the prescribed exact
complete-split table in every tagged logical child cell. -/
noncomputable def cwRecursiveExactTargetFiberParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    Finset (PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) := by
  classical
  exact Finset.univ.filter fun fine ↦
    cwRecursiveLabelledChildWord depth n fine = reference physicalLeg ∧
      ∀ cell word,
        cellMultiplicity
            (cwRecursiveOrientedCoarseIndexSequence
              depth n partAt sigma reference)
            (positiveWordLabelledChildren
              (cwChunkSplitWord (depth + 1)) fine)
            cell word =
          targets.exactProfile (sigma.symm physicalLeg) cell word

@[simp] theorem mem_cwRecursiveExactTargetFiberParts_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    fine ∈ cwRecursiveExactTargetFiberParts
        partAt sigma targets reference physicalLeg ↔
      cwRecursiveLabelledChildWord depth n fine = reference physicalLeg ∧
        ∀ cell word,
          cellMultiplicity
              (cwRecursiveOrientedCoarseIndexSequence
                depth n partAt sigma reference)
              (positiveWordLabelledChildren
                (cwChunkSplitWord (depth + 1)) fine)
              cell word =
            targets.exactProfile (sigma.symm physicalLeg) cell word := by
  classical
  simp [cwRecursiveExactTargetFiberParts]

end AlgebraicComplexity.Examples
