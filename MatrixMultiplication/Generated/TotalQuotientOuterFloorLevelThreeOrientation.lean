/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-!
# Level-three regional orientation of the total-weight candidate

Repeated physical order `(X, Z, Y)` for certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.

This order is a structural convention of the level-three recurrence's coordinate map, not an
optimizer output: the committed level-four payload of the same certificate,
`Generated/TotalQuotientExponentLevelFourOrientation.lean`, carries the identical
`⟨0, 2, 1⟩`.  Repetition across the six output regions is intentional.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThree.Orientation

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

/-- All six labelled regions use the same physical order `(0, 2, 1)`. -/
def order (_region : ℕ) : CoordinateOrder := ⟨0, 2, 1⟩

/-- Every repeated regional order is nevertheless an individual permutation of the coordinates. -/
theorem order_isPermutation (region : ℕ) : (order region).IsPermutation := by
  simp [order, CoordinateOrder.IsPermutation]

end MatrixMultiplication.Generated.TotalQuotientOuterFloorLevelThree.Orientation
