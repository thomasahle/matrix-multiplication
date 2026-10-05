import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-! Repeated `(X,Z,Y)` level-four orientation; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Orientation

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

def order (_region : ℕ) : CoordinateOrder := ⟨0, 2, 1⟩

theorem order_isPermutation (region : ℕ) : (order region).IsPermutation := by
  simp [order, CoordinateOrder.IsPermutation]

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Orientation
