/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

/-!
# Distinct level-four child-row keys: region 1, chunk 2

This untrusted generated list is part of certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`'s compact proposal for
the beta-three rows used by active level-four splits.  It contains 7 keys and is bounded
by the producer's requested chunk size.

The data has no authority on its own.  Separate kernel checks prove both active-slot coverage and
normalization of every listed key before the semantic family theorem consumes it.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region1.Chunk2

open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

/-- This chunk's `(global row, physical coordinate, complete-split total)` obligations. -/
def array : Array LevelFourChildRowKey := #[
    { row := 253, coordinate := 2, total := 1 },
    { row := 259, coordinate := 0, total := 7 },
    { row := 259, coordinate := 1, total := 1 },
    { row := 259, coordinate := 2, total := 0 },
    { row := 265, coordinate := 0, total := 8 },
    { row := 265, coordinate := 1, total := 0 },
    { row := 265, coordinate := 2, total := 0 }]

/-- List view used by the shared once-per-key normalization checker. -/
def entries : List LevelFourChildRowKey := array.toList

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Keys.Region1.Chunk2
