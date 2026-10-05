/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityIndexRegion1Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityIndexRegion1Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityIndexRegion1Chunk2

/-!
# Level-four child-key index: region 1

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` supplies a 135-entry table, assembled here from bounded literal
slices.  Code `3 * shape + coordinate` selects a proposed position in the region's key array.
Missing and out-of-domain codes fall back to the out-of-bounds sentinel `entries.length`.

The table remains untrusted: every consumer checks that the selected array entry equals the full
computed key, including the complete-split total.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Index.Region1

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

/-- Regional index table assembled without repeating any literal entry. -/
def table : Array ℕ :=
  Chunk0.entries ++
    Chunk1.entries ++
    Chunk2.entries

/-- Shape-coordinate code of a child-row key; the incoming region is already fixed by this module. -/
def code (key : LevelFourChildRowKey) : ℕ := 3 * (key.row / 6) + key.coordinate

/-- Untrusted proposed location of a key in the regional deduplicated list. -/
def index (key : LevelFourChildRowKey) : ℕ :=
  (table[code key]?).getD Keys.Region1.entries.length

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Index.Region1
