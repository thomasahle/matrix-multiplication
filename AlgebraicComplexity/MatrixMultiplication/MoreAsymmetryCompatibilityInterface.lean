/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityInterfaceCore
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityAggregation
import Mathlib.Tactic.FieldSimp

/-!
# Exact pooled compatibility-table reconstruction

This module re-exports the lightweight native positive-power compatibility interface and adds the
data boundary for reconstructed `Split_avg` tables.  The paper schema is
expressed by exact integer profiles and a proved count decomposition; generated numerical data can
instantiate `ExactSplitAvgFamily.RealizesTargets` without becoming part of this reusable module.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u

/-! ## Exact `Split_avg` reconstruction boundary -/

/-- An exact pooled table consists of boundary and positive-region profiles and a reconstructed
all-region profile whose integer counts are their sum.  Keeping this relation at the count level
avoids any division or floating-point equality in the certificate interface. -/
structure ExactSplitAvgTable (depth total : ℕ) where
  boundarySamples : ℕ
  positiveSamples : ℕ
  boundary : CompleteSplitProfile depth total boundarySamples
  positive : CompleteSplitProfile depth total positiveSamples
  pooledAll : CompleteSplitProfile depth total (boundarySamples + positiveSamples)
  counts_decompose : ∀ word,
    pooledAll.counts word = boundary.counts word + positive.counts word

namespace ExactSplitAvgTable

variable {depth total : ℕ}

/-- The canonical exact pooled table obtained by adding two finite profiles. -/
def canonical {boundarySamples positiveSamples : ℕ}
    (boundary : CompleteSplitProfile depth total boundarySamples)
    (positive : CompleteSplitProfile depth total positiveSamples) :
    ExactSplitAvgTable depth total where
  boundarySamples := boundarySamples
  positiveSamples := positiveSamples
  boundary := boundary
  positive := positive
  pooledAll := boundary.add positive
  counts_decompose := CompleteSplitProfile.add_counts boundary positive

/-- After normalization, exact count decomposition is precisely the weighted-average identity
used for the paper's `Split_avg` tables. -/
theorem toDistribution_weight_eq_weighted_average
    (table : ExactSplitAvgTable depth total)
    (hboundary : 0 < table.boundarySamples)
    (hpositive : 0 < table.positiveSamples)
    (word : SplitWord depth) :
    (table.pooledAll.toDistribution (Nat.add_pos_left hboundary _)).weight word =
      (table.boundarySamples : ℝ) /
          (table.boundarySamples + table.positiveSamples) *
            (table.boundary.toDistribution hboundary).weight word +
        (table.positiveSamples : ℝ) /
          (table.boundarySamples + table.positiveSamples) *
            (table.positive.toDistribution hpositive).weight word := by
  simp only [CompleteSplitProfile.toDistribution_weight]
  rw [table.counts_decompose word]
  push_cast
  have hsum : (table.boundarySamples + table.positiveSamples : ℝ) ≠ 0 := by
    positivity
  have hboundaryReal : (table.boundarySamples : ℝ) ≠ 0 := by positivity
  have hpositiveReal : (table.positiveSamples : ℝ) ≠ 0 := by positivity
  field_simp

end ExactSplitAvgTable

/-- Exact reconstructed `Split_avg` tables for every pooled `Y` and `Z` coarse coordinate. -/
structure ExactSplitAvgFamily (Part : Type u) (depth : ℕ) where
  y : Part → (coordinate : ℕ) → ExactSplitAvgTable depth coordinate
  z : Part → (coordinate : ℕ) → ExactSplitAvgTable depth coordinate

namespace ExactSplitAvgFamily

variable {Part : Type u} {depth : ℕ}

/-- The minimal data-facing proposition: reconstructed exact tables realize the boundary and
positive-region counts computed by the semantic compatibility evaluator. -/
def RealizesTargets (data : ExactSplitAvgFamily Part depth)
    (targets : CompatibilityTargets Part depth) : Prop :=
  (∀ part coordinate word,
      (data.y part coordinate).boundary.counts word =
        targets.yBoundaryAggregate part coordinate word ∧
      (data.y part coordinate).positive.counts word =
        targets.yPooled part coordinate word) ∧
  (∀ part coordinate word,
      (data.z part coordinate).boundary.counts word =
        targets.zBoundaryAggregate part coordinate word ∧
      (data.z part coordinate).positive.counts word =
        targets.zPooled part coordinate word)

/-- Exact reconstructed `Split_avg` tables satisfying `RealizesTargets` provide the pooled-all
decomposition required by the compatibility soundness theorem. -/
def toPooledAllTargets (data : ExactSplitAvgFamily Part depth)
    (targets : CompatibilityTargets Part depth) (hdata : data.RealizesTargets targets) :
    PooledAllTargets targets where
  yAll part coordinate word := (data.y part coordinate).pooledAll.counts word
  zAll part coordinate word := (data.z part coordinate).pooledAll.counts word
  y_decompose part coordinate word := by
    rw [(data.y part coordinate).counts_decompose word,
      (hdata.1 part coordinate word).1,
      (hdata.1 part coordinate word).2]
  z_decompose part coordinate word := by
    rw [(data.z part coordinate).counts_decompose word,
      (hdata.2 part coordinate word).1,
      (hdata.2 part coordinate word).2]

end ExactSplitAvgFamily

end MoreAsymmetryCompatibility
end AlgebraicComplexity
