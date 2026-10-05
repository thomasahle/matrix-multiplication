/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion0
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion1
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion2
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion3
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion4
import MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThreeWeightsRegion5

/-!
# Level-three integer dual witness of the total-weight candidate

Region-indexed selector over the six exact per-region factor tables of certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
Out-of-range regions fall through to the last table; no statement below depends on that choice.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThree.Weights

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-- Region-indexed product-family witness. -/
def dualWeights : ℕ → ℕ → DualWeights
  | 0 => Region0.dualWeights
  | 1 => Region1.dualWeights
  | 2 => Region2.dualWeights
  | 3 => Region3.dualWeights
  | 4 => Region4.dualWeights
  | _ => Region5.dualWeights

/-- Every selected factor of every region is strictly positive on the `X` role.

The six labelled regions and the out-of-range fallthrough are enumerated as literals so each
branch's goal is the corresponding region table; a wildcard would leave `region` unsubstituted. -/
theorem dualWeights_x_pos (region node : ℕ) (value : Fin coordinateCount) :
    0 < (dualWeights region node).x value := by
  match region with
  | 0 => exact Region0.dualWeights_x_pos node value
  | 1 => exact Region1.dualWeights_x_pos node value
  | 2 => exact Region2.dualWeights_x_pos node value
  | 3 => exact Region3.dualWeights_x_pos node value
  | 4 => exact Region4.dualWeights_x_pos node value
  | 5 => exact Region5.dualWeights_x_pos node value
  | (_ + 6) => exact Region5.dualWeights_x_pos node value

end MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThree.Weights
