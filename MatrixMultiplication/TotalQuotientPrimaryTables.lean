import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.TotalQuotientPrimaryPrimaryData

/-!
# Lightweight primary-table boundary for the total-weight quotient certificate

This module exposes only the seven exact integer tables needed by recurrence checkers.  It is
deliberately separate from `TotalQuotientVolumeReconstructionBase`: that later module also imports
the logarithmic scalar certificate, which is irrelevant to finite row reconstruction and makes
each generated checker reload a much larger environment.

Keeping the declaration name in `TotalQuotientVolumeReconstruction` preserves the public API.
Downstream analytic modules may import the larger reconstruction boundary, while finite cache
checkers should import this module directly.
-/

namespace MatrixMultiplication.TotalQuotientVolumeReconstruction

open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- The seven primary families from the SHA-bound total-quotient certificate.

The tables are exact natural-number or dyadic data.  Dual potentials and logarithmic interval
certificates are intentionally absent from this dependency boundary. -/
def primaryTables : PrimaryTables where
  top := Generated.TotalQuotientPrimary.topChunks
  pos3A := Generated.TotalQuotientPrimary.pos3AChunks
  pos3Alpha := Generated.TotalQuotientPrimary.pos3AlphaChunks
  edgeZero2 := Generated.TotalQuotientPrimary.edgeZero2Chunks
  zero3 := Generated.TotalQuotientPrimary.zero3Chunks
  zero4 := Generated.TotalQuotientPrimary.zero4Chunks
  mu := Generated.TotalQuotientPrimary.muChunks

end MatrixMultiplication.TotalQuotientVolumeReconstruction
