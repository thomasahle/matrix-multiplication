import MatrixMultiplication.BetaFourLocalContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength8Total7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportLength4Total5

/-!
# Parent-local beta-four routing base for region 5, branch 2, parent 53

This is the common support and coordinate data for the line-budgeted slot certificates generated
from untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  Separate part modules check each fixed-left row.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parent : ℕ := 53

/-- Physical coordinate selected by this logical compatibility branch. -/
def coordinate : ℕ := 2

namespace ParentSupport

/-- Checked inert support of this parent coordinate. -/
def codes : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total7.codes

/-- The semantic parent support is the shared checked table. -/
theorem routedSupport_eq :
    BetaFourLocalSlotData.routedParentSupport parent coordinate = codes := by
  unfold BetaFourLocalSlotData.routedParentSupport codes
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total7.codes_eq

/-- Exact length of this coordinate's genuine, unpadded parent support. -/
theorem codes_length : codes.length = 1016 := by
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total7.codes_length

end ParentSupport

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent1
