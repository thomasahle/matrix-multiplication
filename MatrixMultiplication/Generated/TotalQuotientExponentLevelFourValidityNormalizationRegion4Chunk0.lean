/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion4Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData

/-!
# Bounded beta-three normalization check: region 4, chunk 0

The untrusted key list comes from certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module gives it
authority only by reducing the reusable normalization checker against the separately checked
beta-three cache.  The chunk contains at most 64 keys.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Normalization.Region4.Chunk0

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Every key in this bounded chunk names a row of exact mass `2^48`. -/
opaque checked :
    levelFourChildRowKeysNormalizedCheck
      BetaThree.expectedRows Keys.Region4.Chunk0.entries = true := by
  decide +kernel

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Normalization.Region4.Chunk0
