/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeGeometry
import AlgebraicComplexity.Probability.Rational

/-!
# Exact reconstruction primitives for recursive level-four certificates

This module provides a small, executable boundary between flat dyadic optimizer arrays and the
probability vectors used by the recursive laser analysis.  It deliberately contains no named
matrix-multiplication construction and no floating-point arithmetic.

The first client is the level-four Coppersmith--Winograd certificate.  Its positive level-three
nodes are triples of positive natural numbers summing to eight, each repeated for six incoming
regions.  Every such node is split into triples summing to four, padded to ten slots.  The
definitions below reconstruct that geometry rather than trusting an exported mask.

`PositiveLevelThreeData.IsValid` checks three exact facts:

* every regional row is a dyadic probability vector;
* every split row is a dyadic probability vector;
* padded split slots outside the mathematically reconstructed support are interpreted as zero.

The conversion theorems then expose those rows as `RationalProbabilityData`.  Thus later semantic
recurrence theorems can consume genuine finite probability vectors without repeating array-index
or denominator arithmetic.
-/

open scoped BigOperators

namespace AlgebraicComplexity.LevelFourReconstruction

namespace PositiveLevelThreeData

/-- Read a regional numerator, returning zero if a malformed array is too short. -/
def regionNumerator (data : PositiveLevelThreeData)
    (node : Fin nodeCount) (region : Fin regionCount) : ℕ :=
  (data.regionNumerators[node.val]?.getD #[])[region.val]?.getD 0

/-- Read a split numerator, returning zero if a malformed array is too short. -/
def splitNumerator (data : PositiveLevelThreeData)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) : ℕ :=
  if splitSlotValid node slot then
    ((data.splitNumerators[node.val]?.getD #[])[region.val]?.getD #[])[slot.val]?.getD 0
  else 0

/-- Exact structural and simplex checks at the positive level-three reconstruction boundary. -/
def IsValid (data : PositiveLevelThreeData) : Prop :=
  (∀ node, ∑ region, data.regionNumerator node region = dyadicDenominator) ∧
  (∀ node region, ∑ slot, data.splitNumerator node region slot = dyadicDenominator) ∧
  data.regionNumerators.size = nodeCount ∧
  (∀ node : Fin nodeCount,
    (data.regionNumerators[node.val]?.getD #[]).size = regionCount) ∧
  data.splitNumerators.size = nodeCount ∧
  (∀ node : Fin nodeCount,
    (data.splitNumerators[node.val]?.getD #[]).size = regionCount) ∧
  (∀ (node : Fin nodeCount) (region : Fin regionCount),
    ((data.splitNumerators[node.val]?.getD #[])[region.val]?.getD #[]).size = splitSlotCount)

instance (data : PositiveLevelThreeData) : Decidable data.IsValid := by
  unfold IsValid
  infer_instance

/-- A regional row interpreted as exact rational weights. -/
def regionProbabilityData (data : PositiveLevelThreeData) (node : Fin nodeCount) :
    RationalProbabilityData (Fin regionCount) where
  weight region := data.regionNumerator node region / dyadicDenominator

/-- A padded split row interpreted as exact rational weights. -/
def splitProbabilityData (data : PositiveLevelThreeData)
    (node : Fin nodeCount) (region : Fin regionCount) :
    RationalProbabilityData (Fin splitSlotCount) where
  weight slot := data.splitNumerator node region slot / dyadicDenominator

/-- Exact validity turns every regional row into a genuine rational probability vector. -/
theorem regionProbabilityData_isProbability
    {data : PositiveLevelThreeData} (hdata : data.IsValid) (node : Fin nodeCount) :
    (data.regionProbabilityData node).IsProbability := by
  constructor
  · intro region
    exact div_nonneg (by positivity) (by positivity)
  · simp only [regionProbabilityData]
    rw [← Finset.sum_div]
    have hsum : (∑ region, (data.regionNumerator node region : ℚ)) =
        (dyadicDenominator : ℚ) := by
      exact_mod_cast hdata.1 node
    rw [hsum]
    norm_num [dyadicDenominator]

/-- Exact validity turns every padded split row into a genuine rational probability vector. -/
theorem splitProbabilityData_isProbability
    {data : PositiveLevelThreeData} (hdata : data.IsValid)
    (node : Fin nodeCount) (region : Fin regionCount) :
    (data.splitProbabilityData node region).IsProbability := by
  constructor
  · intro slot
    exact div_nonneg (by positivity) (by positivity)
  · simp only [splitProbabilityData]
    rw [← Finset.sum_div]
    have hsum : (∑ slot, (data.splitNumerator node region slot : ℚ)) =
        (dyadicDenominator : ℚ) := by
      exact_mod_cast hdata.2.1 node region
    rw [hsum]
    norm_num [dyadicDenominator]

/-- Invalid padded slots have zero rational mass. -/
theorem splitProbabilityData_weight_eq_zero_of_invalid
    {data : PositiveLevelThreeData}
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hslot : ¬ splitSlotValid node slot) :
    (data.splitProbabilityData node region).weight slot = 0 := by
  simp [splitProbabilityData, splitNumerator, hslot]

end PositiveLevelThreeData

end AlgebraicComplexity.LevelFourReconstruction
