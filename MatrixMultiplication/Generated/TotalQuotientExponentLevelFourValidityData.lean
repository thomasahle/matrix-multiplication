/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion5

/-!
# Compact level-four validity-key family

This is certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`'s untrusted sufficient-statistic proposal.
The six regions contain

* [57, 135, 0, 0, 63, 54] distinct keys; and
* [222, 1567, 0, 0, 306, 180] active ordered slots.

Lean gives these lists authority only after separately checking normalization and active-slot
coverage.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

/-- Region-indexed key lists, matching the six incoming-region rows. -/
def keysForRegion : ℕ → List LevelFourChildRowKey
  | 0 => Keys.Region0.entries
  | 1 => Keys.Region1.entries
  | 2 => Keys.Region2.entries
  | 3 => Keys.Region3.entries
  | 4 => Keys.Region4.entries
  | _ => Keys.Region5.entries

/-- All submitted keys, useful for global diagnostics and provenance checks. -/
def expectedKeys : List LevelFourChildRowKey :=
  Keys.Region0.entries ++
    Keys.Region1.entries ++
    Keys.Region2.entries ++
    Keys.Region3.entries ++
    Keys.Region4.entries ++
    Keys.Region5.entries

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity
