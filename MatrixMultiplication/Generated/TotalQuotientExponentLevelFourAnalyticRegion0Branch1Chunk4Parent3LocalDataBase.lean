import MatrixMultiplication.BetaFourLocalContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength8Total6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total4

/-!
# Parent-local beta-four routing base for region 0, branch 1, parent 55

This is the common support and coordinate data for the line-budgeted slot certificates generated
from untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  Separate part modules check each fixed-left row.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 55

/-- Physical coordinate selected by this logical compatibility branch. -/
def coordinate : ℕ := 1

namespace ParentSupport

/-- Checked inert support of this parent coordinate. -/
def codes : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total6.codes

/-- The semantic parent support is the shared checked table. -/
theorem routedSupport_eq :
    BetaFourLocalSlotData.routedParentSupport parent coordinate = codes := by
  unfold BetaFourLocalSlotData.routedParentSupport codes
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total6.codes_eq

/-- Exact length of this coordinate's genuine, unpadded parent support. -/
theorem codes_length : codes.length = 784 := by
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total6.codes_length

end ParentSupport

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent3
