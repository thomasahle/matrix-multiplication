import AlgebraicComplexity.Analysis.RetainedExponentAggregation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Exact coarse retained-exponent floors

This certificate artifact records conservative six-decimal common branch floors for the root,
level-four, and level-three regional families, together with the already coarsened level-two
floor.  The values come from certificate SHA-256
`eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`.

The theorem in this file is deliberately arithmetic only: it proves that the sum of these exact
rational floors is `8.200174 > 8.2`.  Separate generated reconstruction modules must prove that
each floor is below all three semantic branch rates before
`RetainedExponentAggregation.fourFamilyFloor_le_fourFamilyExponent` can be applied.
-/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors

open AlgebraicComplexity.RetainedExponentAggregation

noncomputable section

abbrev Region := Fin 6
abbrev LevelTwoGroup := Unit

/-- Common decimal denominator used only for the coarse arithmetic interface. -/
def denominator : ℕ := 1_000_000

/-- Root-family floor numerators in region order. -/
def rootFloorNumerators : Array ℕ :=
  #[1_140, 2_648_955, 0, 0, 2_018, 678]

/-- Level-four-family floor numerators in region order. -/
def levelFourFloorNumerators : Array ℕ :=
  #[593, 1_656_892, 0, 0, 1_103, 345]

/-- Level-three-family floor numerators in region order. -/
def levelThreeFloorNumerators : Array ℕ :=
  #[673_837, 196, 1_243_034, 569, 198_046, 278]

/-- Conservative common three-branch floor for one root region. -/
def rootFloor (region : Region) : ℝ :=
  (rootFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Conservative common three-branch floor for one level-four region. -/
def levelFourFloor (region : Region) : ℝ :=
  (levelFourFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Conservative common three-branch floor for one level-three region. -/
def levelThreeFloor (region : Region) : ℝ :=
  (levelThreeFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Existing level-two common floor `1.77249`, expressed at the shared six-decimal denominator. -/
def levelTwoFloor (_group : LevelTwoGroup) : ℝ :=
  1_772_490 / denominator

/-- Exact four-family floor assembled by the generic retained-exponent aggregator. -/
def coarseFourFamilyFloor : ℝ :=
  fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor

/-- The four independently rounded family floors sum exactly to `8.200174`. -/
theorem coarseFourFamilyFloor_eq :
    coarseFourFamilyFloor = (8_200_174 / 1_000_000 : ℝ) := by
  norm_num [coarseFourFamilyFloor, fourFamilyFloor, familyFloor,
    rootFloor, levelFourFloor, levelThreeFloor, levelTwoFloor,
    rootFloorNumerators, levelFourFloorNumerators, levelThreeFloorNumerators,
    denominator, Fin.sum_univ_succ]

/-- The exact conservative family floors retain `0.000174` bits of margin above `8.2`. -/
theorem eightPointTwo_lt_coarseFourFamilyFloor :
    (82 / 10 : ℝ) < coarseFourFamilyFloor := by
  rw [coarseFourFamilyFloor_eq]
  norm_num

end

end MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors
