/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRootRecurrence

/-!
# Exact root-family integer dual factors of the total-weight candidate

Positive 8-bit integer product-family factors for certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`,
one `3 * 17` block per root orientation, flattened at stride
`root * 51 + coordinate * 17 + value`.

The certificate serializes these duals as raw binary32 words in
`Generated/TotalQuotientPrimaryRootDualData0.lean` (row width
`Manifest.rootDualRowWidth = 3 * 17`).  Decoding binary32 inside the kernel would add a
floating-point surface to the trusted path for no mathematical gain, so — exactly as the committed
level-four payload `TotalQuotientExponentLevelFourWeightsRegion*` does — the *selected integers*
are emitted directly and the Float32 potentials appear in no statement.  Soundness of the retained
rate uses only positivity of these factors, which is structural here: the array stores each factor
minus one, so `weight` is a successor and needs no decision procedure.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Weights

open MatrixMultiplication.SimplifiedExponentRootRecurrence

set_option maxRecDepth 100000

/-- Flattened root dual factors minus one. -/
def rawWeightsMinusOne : Array ℕ := #[
    255, 2624, 11279, 29610, 54337, 74429, 76829, 59955, 33742, 14619,
    7222, 5943, 5311, 3167, 2343, 6070, 29520, 255, 2504, 10562,
    27635, 50456, 68825, 71032, 54889, 30684, 13108, 6564, 5532, 4928,
    2895, 2222, 6014, 28660, 255, 2682, 11696, 30992, 57212, 78481,
    80799, 62907, 35154, 15091, 7463, 6140, 5454, 3199, 2384, 6077,
    29565, 255, 2050, 9718, 31254, 74926, 147844, 228211, 279174, 228196,
    122035, 45847, 19113, 12815, 6759, 2227, 2211, 15249, 255, 1998,
    9519, 30342, 71849, 143188, 226683, 276177, 221588, 112928, 42873, 18824,
    12905, 6909, 2389, 2267, 15216, 255, 2128, 10029, 32106, 78554,
    152716, 239261, 285113, 235099, 123838, 46601, 19715, 13295, 7193, 2403,
    2228, 15631, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 2668, 11836, 31776, 59879, 84665,
    90802, 71854, 41294, 17842, 8503, 6843, 6089, 3557, 2512, 6190,
    26435, 255, 2507, 10758, 28517, 53522, 75506, 80896, 63720, 36299,
    15575, 7553, 6227, 5508, 3209, 2373, 6174, 24828, 255, 2683,
    11881, 31717, 59463, 83850, 89316, 70968, 41093, 17956, 8521, 6766,
    6091, 3621, 2514, 5984, 26716, 255, 2663, 11525, 29858, 54768,
    73883, 75570, 57983, 32409, 13744, 6927, 5825, 5183, 3047, 2341,
    6248, 31562, 255, 2553, 10810, 27741, 50628, 67910, 68751, 52808,
    29547, 12511, 6353, 5397, 4788, 2807, 2204, 6104, 28776, 255,
    2646, 11320, 29008, 52797, 70877, 72183, 55521, 31333, 13560, 6809,
    5632, 5045, 3062, 2305, 5983, 30714
  ]

/-- The serialized table has exactly one entry per root, coordinate and value. -/
theorem rawWeightsMinusOne_size :
    rawWeightsMinusOne.size = 6 * 3 * 17 := by decide

/-- Recover the exact positive factor selected for one root coordinate value. -/
def weight (root coordinate value : ℕ) : ℕ :=
  rawWeightsMinusOne[root * 51 + coordinate * 17 + value]?.getD 0 + 1

/-- Every serialized root factor is strictly positive, structurally. -/
theorem weight_pos (root coordinate value : ℕ) : 0 < weight root coordinate value := by
  simp [weight]

/-- Logical-`X` factor family of one root orientation. -/
def weightX (root : ℕ) (value : Fin 17) : ℕ := weight root 0 value.val

/-- Logical-`Y` factor family of one root orientation. -/
def weightY (root : ℕ) (value : Fin 17) : ℕ := weight root 1 value.val

/-- Logical-`Z` factor family of one root orientation. -/
def weightZ (root : ℕ) (value : Fin 17) : ℕ := weight root 2 value.val

/-- The logical-`X` dual family is positive, as `RootRows.IsValid` requires. -/
theorem weightX_pos (root : ℕ) (value : Fin 17) : 0 < weightX root value :=
  weight_pos root 0 value.val

/-- The logical-`Y` dual family is positive, as `RootRows.IsValid` requires. -/
theorem weightY_pos (root : ℕ) (value : Fin 17) : 0 < weightY root value :=
  weight_pos root 1 value.val

/-- The logical-`Z` dual family is positive, as `RootRows.IsValid` requires. -/
theorem weightZ_pos (root : ℕ) (value : Fin 17) : 0 < weightZ root value :=
  weight_pos root 2 value.val

end MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Weights
