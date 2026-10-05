/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AData0
import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AlphaData0
import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AlphaData1
import MatrixMultiplication.Generated.TotalQuotientPrimaryMuData0
import MatrixMultiplication.SimplifiedExponentLevelTwoInput

/-!
# Compact exact inputs for the total-quotient level-two checker

This module is the result-specific data boundary of the lightweight checker.  It imports only the
three sparse primary families read by the positive level-two recurrence and records the 270 cached
level-three mass numerators.  In particular, it does not import the scalar-volume reconstruction,
the 1,620 historical recurrence records, or any real logarithm theorem.

The literals come from certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  The independent top-scatter
proof and the semantic adapter identify `massThree` with the established generated cache; this
module's job is only to give the exact edge checker a narrow input closure.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoInputData

open MatrixMultiplication.Generated.TotalQuotientPrimary
open MatrixMultiplication.SimplifiedExponentLevelTwoInput

/-- The only sparse primary families consulted by the level-two edge recurrence. -/
def tables : InputTables where
  pos3A := #[Pos3AData0.rawData]
  pos3Alpha := #[Pos3AlphaData0.rawData, Pos3AlphaData1.rawData]
  mu := #[MuData0.rawData]

/-- Cached exact level-three mass numerators, at the same denominator as the established
total-quotient recurrence. -/
def massThree : Array Nat := #[
    0, 133, 0, 0, 0, 0,
    0, 211, 0, 0, 0, 0,
    0, 1255, 0, 0, 0, 0,
    0, 13301, 0, 0, 0, 0,
    0, 29753, 0, 0, 6, 0,
    0, 10058, 0, 0, 0, 0,
    0, 1145, 0, 0, 0, 0,
    0, 209, 0, 0, 0, 0,
    0, 134, 0, 0, 0, 0,
    0, 184, 0, 0, 0, 0,
    0, 1612, 0, 0, 0, 0,
    12, 22811, 0, 0, 24, 6,
    42, 110887, 0, 0, 84, 30,
    42, 101516, 0, 0, 84, 30,
    12, 19650, 0, 0, 24, 6,
    0, 1452, 0, 0, 0, 0,
    0, 223, 0, 0, 0, 0,
    0, 1133, 0, 0, 0, 0,
    12, 20415, 0, 0, 24, 6,
    84, 148110, 0, 0, 132, 42,
    140, 264735, 0, 0, 220, 86,
    86, 139736, 0, 0, 132, 42,
    12, 18332, 0, 0, 24, 6,
    0, 1138, 0, 0, 0, 0,
    0, 9305, 0, 0, 0, 0,
    42, 84934, 0, 0, 84, 30,
    142, 249959, 0, 0, 220, 90,
    140, 256703, 0, 0, 222, 86,
    42, 87166, 0, 0, 84, 30,
    0, 8742, 0, 0, 0, 0,
    6, 23240, 0, 0, 6, 0,
    42, 93500, 0, 0, 84, 30,
    84, 157859, 0, 0, 132, 42,
    42, 105253, 0, 0, 84, 30,
    0, 24871, 0, 0, 6, 0,
    0, 13034, 0, 0, 0, 0,
    12, 24066, 0, 0, 24, 6,
    12, 26150, 0, 0, 24, 6,
    0, 13461, 0, 0, 0, 0,
    0, 1248, 0, 0, 0, 0,
    0, 1677, 0, 0, 0, 0,
    0, 1335, 0, 0, 0, 0,
    0, 184, 0, 0, 0, 0,
    0, 227, 0, 0, 0, 0,
    0, 131, 0, 0, 0, 0
  ]

/-- The cached mass vector has the expected `45 * 6` ambient rows. -/
theorem massThree_size : massThree.size = 270 := by
  set_option maxRecDepth 100000 in
    decide

end MatrixMultiplication.TotalQuotientExponentLevelTwoInputData
