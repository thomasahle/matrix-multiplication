import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopRow0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopRow7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopRow28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopRow35

/-! Literal dense positive top cache; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Top

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

def zeroRow : Array (Array ℕ) :=
  Array.replicate topBranchChunkCount (Array.replicate topBranchChunkSize 0)

def expectedRows : TopBranchRows := #[Row0.expectedRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, Row7.expectedRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, Row28.expectedRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, zeroRow, Row35.expectedRow]

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence.Top
