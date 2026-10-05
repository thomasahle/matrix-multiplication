import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 8 and weight 4

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total4

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [8, 14, 16, 20, 22, 24, 32, 34, 38, 40, 42, 46, 48, 56, 58, 60, 64, 66, 72, 86, 88, 92, 94, 96, 100, 102, 110, 112, 114, 118, 120, 126, 136, 138, 144, 164, 166, 168, 172, 174, 180, 190, 192, 198, 216, 248, 250, 254, 256, 258, 262, 264, 272, 274, 276, 280, 282, 288, 298, 300, 306, 326, 328, 330]

end Chunk0

namespace Chunk1

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [334, 336, 342, 352, 354, 360, 378, 406, 408, 414, 432, 488, 490, 492, 496, 498, 504, 514, 516, 522, 540, 568, 570, 576, 594, 648, 734, 736, 740, 742, 744, 748, 750, 758, 760, 762, 766, 768, 774, 784, 786, 792, 812, 814, 816, 820, 822, 828, 838, 840, 846, 864, 892, 894, 900, 918, 974, 976, 978, 982, 984, 990, 1000, 1002]

end Chunk1

namespace Chunk2

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [1008, 1026, 1054, 1056, 1062, 1080, 1134, 1216, 1218, 1224, 1242, 1296, 1460, 1462, 1464, 1468, 1470, 1476, 1486, 1488, 1494, 1512, 1540, 1542, 1548, 1566, 1620, 1702, 1704, 1710, 1728, 1782, 1944, 2192, 2194, 2198, 2200, 2202, 2206, 2208, 2216, 2218, 2220, 2224, 2226, 2232, 2242, 2244, 2250, 2270, 2272, 2274, 2278, 2280, 2286, 2296, 2298, 2304, 2322, 2350, 2352, 2358, 2376, 2432]

end Chunk2

namespace Chunk3

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [2434, 2436, 2440, 2442, 2448, 2458, 2460, 2466, 2484, 2512, 2514, 2520, 2538, 2592, 2674, 2676, 2682, 2700, 2754, 2918, 2920, 2922, 2926, 2928, 2934, 2944, 2946, 2952, 2970, 2998, 3000, 3006, 3024, 3078, 3160, 3162, 3168, 3186, 3240, 3402, 3646, 3648, 3654, 3672, 3726, 3888, 4376, 4378, 4380, 4384, 4386, 4392, 4402, 4404, 4410, 4428, 4456, 4458, 4464, 4482, 4536, 4618, 4620, 4626]

end Chunk3

namespace Chunk4

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [4644, 4698, 4860, 5104, 5106, 5112, 5130, 5184, 5346, 5832]

end Chunk4

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes ++ Chunk1.codes ++ Chunk2.codes ++ Chunk3.codes ++ Chunk4.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 8 4 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 266 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total4
