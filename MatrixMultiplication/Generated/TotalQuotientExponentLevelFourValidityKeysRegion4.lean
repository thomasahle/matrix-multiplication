/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion4Chunk0

/-!
# Distinct level-four child-row keys: region 4

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` has 306 active ordered slots in this region.  Their
labelled children reduce to 63 distinct normalization keys, stored in 1
bounded chunks.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region4

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

/-- Deduplicated row keys for incoming region 4. -/
def entries : List LevelFourChildRowKey :=
  Chunk0.entries

/-- Array view assembled from the same bounded chunks for constant-index coverage checks. -/
def array : Array LevelFourChildRowKey :=
  Chunk0.array

/-- The array and list views contain exactly the same submitted keys in the same order. -/
theorem array_toList_eq_entries : array.toList = entries := by
  simp [array, entries, Chunk0.entries]

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region4
