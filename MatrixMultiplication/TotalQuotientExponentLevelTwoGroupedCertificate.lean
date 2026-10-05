/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck2
import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance
import MatrixMultiplication.TotalQuotientExponentStageAggregation

/-!
# Directed numerical certificate for the compact level-two recurrence

The semantic provenance theorem replaces the 1,620 active edge records by 67 exact sufficient-
statistic records.  This module completes the analytic checker:

* three small finite reductions normalize the compact branch forms;
* three finite bridges identify their literal targets with the existing directed-log targets;
* the previously proved logarithm enclosures put the common floor below those targets; and
* semantic grouping transports the inequalities back to the original sparse-table recurrence.

No optimizer or floating-point output is trusted.  The only numerical proof obligations are exact
form equalities and the established rationally directed logarithm bounds.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchTargets
open MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance

/-- The exact normalized target selected by a coordinate branch. -/
def certifiedTargets : Fin 3 → Form := ![branch0, branch1, branch2]

/-- Compact branch zero is the established directed-log target. -/
theorem branch0_eq_established : branch0 = Branch0.expectedForm := by
  decide

/-- Compact branch one is the established directed-log target. -/
theorem branch1_eq_established : branch1 = Branch1.expectedForm := by
  decide

/-- Compact branch two is the established directed-log target. -/
theorem branch2_eq_established : branch2 = Branch2.expectedForm := by
  decide

/-- Every compact branch form normalizes to its displayed exact target.

Proof sketch: split the three-element coordinate type and invoke the corresponding independently
checked finite normalization leaf. -/
theorem groupedBranch_normalize (coordinate : Fin 3) :
    Form.normalize (inputBranchForm groupedInputs coordinate) =
      certifiedTargets coordinate := by
  fin_cases coordinate
  · exact MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck0.normalized_eq
  · exact MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck1.normalized_eq
  · exact MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchCheck2.normalized_eq

/-- The stage floor is the directed checker family's common floor. -/
theorem levelTwoFloor_eq_commonFloor :
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () = commonFloor := by
  norm_num [Generated.TotalQuotientExponentStageFloors.levelTwoFloor,
    Generated.TotalQuotientExponentStageFloors.denominator, commonFloor]

/-- The stage floor lies below the evaluation of every compact normalized target.

Proof sketch: identify each exact target with its established form and apply that branch's directed
logarithm enclosure. -/
theorem levelTwoFloor_le_target (coordinate : Fin 3) :
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () ≤
      Form.eval levelTwoFormBits (certifiedTargets coordinate) := by
  rw [levelTwoFloor_eq_commonFloor]
  fin_cases coordinate
  · change commonFloor ≤ Form.eval levelTwoFormBits branch0
    rw [branch0_eq_established]
    exact commonFloor_le_branch0
  · change commonFloor ≤ Form.eval levelTwoFormBits branch1
    rw [branch1_eq_established]
    exact commonFloor_le_branch1
  · change commonFloor ≤ Form.eval levelTwoFormBits branch2
    rw [branch2_eq_established]
    exact commonFloor_le_branch2

/-- **The compact checker proves the semantic level-two branch floor.**

Proof sketch: rewrite the original branch rate to evaluation of the 67-record form using semantic
provenance.  Replace that form by its normalized target using `Form.eval_normalize`, then apply the
directed target bound. -/
theorem branchFloorCertified :
    TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified
      certifiedTables certifiedMassThree := by
  intro coordinate
  unfold TotalQuotientExponentLevelTwoRecurrence.branchRate
  rw [activeBranchRate_eq_grouped]
  calc
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () ≤
        Form.eval levelTwoFormBits (certifiedTargets coordinate) :=
      levelTwoFloor_le_target coordinate
    _ = Form.eval levelTwoFormBits
        (inputBranchForm groupedInputs coordinate) := by
      rw [← groupedBranch_normalize coordinate, Form.eval_normalize]

/-- The accepted inner retained floor is below the exact level-two family exponent. -/
theorem innerRetainedFloor_le_levelTwoFamilyExponent :
    TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      AlgebraicComplexity.RetainedExponentAggregation.familyExponent
        (TotalQuotientExponentLevelTwoRecurrence.familyRate
          certifiedTables certifiedMassThree) :=
  TotalQuotientExponentStageAggregation.innerRetainedFloor_le_levelTwoFamilyExponent
    certifiedTables certifiedMassThree branchFloorCertified

/-- The same unconditional inner floor bound against the concrete three-branch bottleneck. -/
theorem innerRetainedFloor_le_retainedExponent :
    TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent
        certifiedTables certifiedMassThree := by
  have h := TotalQuotientExponentLevelTwoRecurrence.innerRetainedFloor_le_retainedExponent
    certifiedTables certifiedMassThree branchFloorCertified
  simpa only [TotalWeightAcceptanceFloors.innerRetainedFloor] using h

end MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate
