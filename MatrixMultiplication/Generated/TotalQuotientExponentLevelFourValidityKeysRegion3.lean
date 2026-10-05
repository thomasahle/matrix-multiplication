/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveFiniteFamilies


/-!
# Distinct level-four child-row keys: region 3

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` has 0 active ordered slots in this region.  Their
labelled children reduce to 0 distinct normalization keys, stored in 0
bounded chunks.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region3

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

/-- Deduplicated row keys for incoming region 3. -/
def entries : List LevelFourChildRowKey :=
  []

/-- Array view assembled from the same bounded chunks for constant-index coverage checks. -/
def array : Array LevelFourChildRowKey :=
  #[]

/-- The array and list views contain exactly the same submitted keys in the same order. -/
theorem array_toList_eq_entries : array.toList = entries := rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region3
