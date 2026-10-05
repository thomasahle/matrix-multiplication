import AlgebraicComplexity.Analysis.RetainedExponentAggregation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Exact per-stage retained-exponent floors for the total-weight quotient candidate

This certificate artifact is the total-weight analogue of
`Generated/SimplifiedExponentCoarseFloors.lean`: it records conservative six-decimal common branch
floors for the root, level-four and level-three regional families, together with the already
coarsened level-two floor, for the volume-only `CW₅⁸` total-weight candidate at depth 4.

Provenance.  Certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, coarsening spec
`2:1=0|0;2:2=0|0|0;2:3=0|0`.  The numerators below are the six-decimal truncations of the
exporter's `branch_common_lower_values`, distilled into
`better_bound/total_weight_exponent_stage_floors.json`.  They are *certified arithmetic*: the exact
exporter invocation that re-derives them (including `--compression-bits 11`, which is required to
reproduce `directed_compressed_lower_value = 8.24198033029317`) is recorded in
`better_bound/total_weight_stage_floor_prep.md`, §4.  There is no per-stage Lean emitter, so — like
its `Simplified…` predecessor — this module is hand-assembled from that JSON.

Contents.  The theorems here are deliberately arithmetic only.  They establish

* the exact per-family sums `2.681658`, `1.737288`, `2.080193`, `1.742834`;
* `811/125 ≤ root + level4 + level3` (the outer acceptance floor of
  `MatrixMultiplication/TotalWeightAcceptanceFloors.lean`, with margin `1.114e-02`);
* `433/250 ≤ level2` (the inner acceptance floor, with margin `1.083e-02`); and
* `411/50 < 8.241973`, the total four-family floor.

Scope.  Connecting these rational floors to the *semantic* retained rate — i.e. proving that each
floor lies below all three directional branch rates of its group, so that
`RetainedExponentAggregation.fourFamilyFloor_le_fourFamilyExponent` applies — is the next
milestone (the recurrence-validation stack) and is **not** done here.  Nothing in this file asserts
anything about a tensor.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentStageFloors

open AlgebraicComplexity.RetainedExponentAggregation

noncomputable section

abbrev Region := Fin 6
abbrev LevelTwoGroup := Unit

/-- Common decimal denominator used only for the coarse arithmetic interface. -/
def denominator : ℕ := 1_000_000

/-- Root-family floor numerators in region order. -/
def rootFloorNumerators : Array ℕ :=
  #[1_157, 2_677_749, 0, 0, 2_074, 678]

/-- Level-four-family floor numerators in region order. -/
def levelFourFloorNumerators : Array ℕ :=
  #[601, 1_735_207, 0, 0, 1_134, 346]

/-- Level-three-family floor numerators in region order. -/
def levelThreeFloorNumerators : Array ℕ :=
  #[661_485, 185, 1_242_085, 280, 175_901, 257]

/-- Conservative common three-branch floor for one root region. -/
def rootFloor (region : Region) : ℝ :=
  (rootFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Conservative common three-branch floor for one level-four region. -/
def levelFourFloor (region : Region) : ℝ :=
  (levelFourFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Conservative common three-branch floor for one level-three region. -/
def levelThreeFloor (region : Region) : ℝ :=
  (levelThreeFloorNumerators[region.val]?.getD 0 : ℝ) / denominator

/-- Level-two common floor `1.742834`, expressed at the shared six-decimal denominator.

Unlike the outer stages, the level-two value loses essentially nothing to directed compression
(`~1e-15`), so this truncation is the only conservatism on the inner side. -/
def levelTwoFloor (_group : LevelTwoGroup) : ℝ :=
  1_742_834 / denominator

/-- Outer retained floor of the total-weight candidate: the three stages above level two. -/
def outerFloor : ℝ :=
  familyFloor rootFloor + familyFloor levelFourFloor + familyFloor levelThreeFloor

/-- Inner retained floor of the total-weight candidate: the level-two family alone. -/
def innerFloor : ℝ :=
  familyFloor levelTwoFloor

/-- Exact four-family floor assembled by the generic retained-exponent aggregator. -/
def coarseFourFamilyFloor : ℝ :=
  fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor

/-- The root family sums exactly to `2.681658`. -/
theorem rootFamilyFloor_eq : familyFloor rootFloor = (2_681_658 / 1_000_000 : ℝ) := by
  norm_num [familyFloor, rootFloor, rootFloorNumerators, denominator, Fin.sum_univ_succ]

/-- The level-four family sums exactly to `1.737288`. -/
theorem levelFourFamilyFloor_eq : familyFloor levelFourFloor = (1_737_288 / 1_000_000 : ℝ) := by
  norm_num [familyFloor, levelFourFloor, levelFourFloorNumerators, denominator, Fin.sum_univ_succ]

/-- The level-three family sums exactly to `2.080193`. -/
theorem levelThreeFamilyFloor_eq : familyFloor levelThreeFloor = (2_080_193 / 1_000_000 : ℝ) := by
  norm_num [familyFloor, levelThreeFloor, levelThreeFloorNumerators, denominator,
    Fin.sum_univ_succ]

/-- The level-two family sums exactly to `1.742834`. -/
theorem levelTwoFamilyFloor_eq : familyFloor levelTwoFloor = (1_742_834 / 1_000_000 : ℝ) := by
  norm_num [familyFloor, levelTwoFloor, denominator]

/-- The three outer stages sum exactly to `6.499139`, matching the JSON field `outer_floor`. -/
theorem outerFloor_eq : outerFloor = (6_499_139 / 1_000_000 : ℝ) := by
  rw [outerFloor, rootFamilyFloor_eq, levelFourFamilyFloor_eq, levelThreeFamilyFloor_eq]
  norm_num

/-- The inner stage is exactly `1.742834 = 871417/500000`, matching the JSON field `inner_floor`. -/
theorem innerFloor_eq : innerFloor = (871_417 / 500_000 : ℝ) := by
  rw [innerFloor, levelTwoFamilyFloor_eq]
  norm_num

/-- The certified per-stage data dominates the outer acceptance floor `811/125 = 6.488`,
with margin `1.114e-02`. -/
theorem outerRetainedFloor_le_outerFloor : (811 / 125 : ℝ) ≤ outerFloor := by
  rw [outerFloor_eq]
  norm_num

/-- The certified per-stage data dominates the inner acceptance floor `433/250 = 1.732`,
with margin `1.083e-02`. -/
theorem innerRetainedFloor_le_innerFloor : (433 / 250 : ℝ) ≤ innerFloor := by
  rw [innerFloor_eq]
  norm_num

/-- The four independently truncated family floors sum exactly to `8.241973`. -/
theorem coarseFourFamilyFloor_eq :
    coarseFourFamilyFloor = (8_241_973 / 1_000_000 : ℝ) := by
  have : coarseFourFamilyFloor = outerFloor + innerFloor := by
    rw [coarseFourFamilyFloor, fourFamilyFloor, outerFloor, innerFloor]
  rw [this, outerFloor_eq, innerFloor_eq]
  norm_num

/-- The total-weight retained floor `411/50 = 8.22` used by the acceptance endpoint sits strictly
below the certified per-stage total, with margin `2.1973e-02`. -/
theorem retainedFloor_lt_coarseFourFamilyFloor :
    (411 / 50 : ℝ) < coarseFourFamilyFloor := by
  rw [coarseFourFamilyFloor_eq]
  norm_num

/-- The acceptance split is consistent with the per-stage data: the two acceptance floors add up
to the retained floor and each is separately dominated. -/
theorem acceptanceSplit_le_coarseFourFamilyFloor :
    (811 / 125 : ℝ) + (433 / 250 : ℝ) ≤ coarseFourFamilyFloor := by
  rw [coarseFourFamilyFloor_eq]
  norm_num

end

end MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
