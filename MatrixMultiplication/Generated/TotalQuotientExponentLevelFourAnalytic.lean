import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion2Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion2Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion2Branch2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion3Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion3Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion3Branch2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2
import Mathlib.Tactic.FinCases

/-! Compact selected-parent level-four analytic certificate; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.

The public theorem supplies all eighteen directed regional branch floors.  The certificate stores
only positive integer dual factors, selected-parent lists, and bounded signed-log shards; the full
per-parent row snapshots used by the historical exporter are absent.  A certificate may retain any
explicit parent subset, so no costly claim that this list exhausts the ambient active support is
needed. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

def weights : ℕ → ℕ → DualWeights
  | 0 => Weights.Region0.dualWeights
  | 1 => Weights.Region1.dualWeights
  | 2 => Weights.Region2.dualWeights
  | 3 => Weights.Region3.dualWeights
  | 4 => Weights.Region4.dualWeights
  | _ => Weights.Region5.dualWeights

def parents : ℕ → List ℕ
  | 0 => Region0.Branch0.expectedParents
  | 1 => Region1.Branch0.expectedParents
  | 2 => Region2.Branch0.expectedParents
  | 3 => Region3.Branch0.expectedParents
  | 4 => Region4.Branch0.expectedParents
  | _ => Region5.Branch0.expectedParents

noncomputable def branchRate (region : Fin 6) (branch : Fin 3) : ℝ :=
  branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
    (weights region.val) region.val (parents region.val) branch

/-- Every generated regional floor is below every selected-parent integer-dual branch rate. -/
theorem levelFourFloor_le_branchRate (region : Fin 6) (branch : Fin 3) :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor region ≤
      branchRate region branch := by
  fin_cases region <;> fin_cases branch
  · simpa [branchRate, weights, parents] using Region0.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region0.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region0.Branch2.floor_le_rate
  · simpa [branchRate, weights, parents] using Region1.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region1.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region1.Branch2.floor_le_rate
  · simpa [branchRate, weights, parents] using Region2.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region2.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region2.Branch2.floor_le_rate
  · simpa [branchRate, weights, parents] using Region3.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region3.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region3.Branch2.floor_le_rate
  · simpa [branchRate, weights, parents] using Region4.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region4.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region4.Branch2.floor_le_rate
  · simpa [branchRate, weights, parents] using Region5.Branch0.floor_le_rate
  · simpa [branchRate, weights, parents] using Region5.Branch1.floor_le_rate
  · simpa [branchRate, weights, parents] using Region5.Branch2.floor_le_rate

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic
