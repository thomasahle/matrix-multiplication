import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 8 and weight 12

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total12

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [728, 1214, 1376, 1430, 1448, 1454, 1456, 1700, 1862, 1916, 1934, 1940, 1942, 2024, 2078, 2096, 2102, 2104, 2132, 2150, 2156, 2158, 2168, 2174, 2176, 2180, 2182, 2184, 2672, 2834, 2888, 2906, 2912, 2914, 3158, 3320, 3374, 3392, 3398, 3400, 3482, 3536, 3554, 3560, 3562, 3590, 3608, 3614, 3616, 3626, 3632, 3634, 3638, 3640, 3642, 3806, 3860, 3878, 3884, 3886, 3968, 4022, 4040, 4046]

end Chunk0

namespace Chunk1

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [4048, 4076, 4094, 4100, 4102, 4112, 4118, 4120, 4124, 4126, 4128, 4184, 4202, 4208, 4210, 4238, 4256, 4262, 4264, 4274, 4280, 4282, 4286, 4288, 4290, 4310, 4316, 4318, 4328, 4334, 4336, 4340, 4342, 4344, 4352, 4354, 4358, 4360, 4362, 4366, 4368, 4616, 4778, 4832, 4850, 4856, 4858, 4940, 4994, 5012, 5018, 5020, 5048, 5066, 5072, 5074, 5084, 5090, 5092, 5096, 5098, 5100, 5264, 5318]

end Chunk1

namespace Chunk2

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [5336, 5342, 5344, 5426, 5480, 5498, 5504, 5506, 5534, 5552, 5558, 5560, 5570, 5576, 5578, 5582, 5584, 5586, 5642, 5660, 5666, 5668, 5696, 5714, 5720, 5722, 5732, 5738, 5740, 5744, 5746, 5748, 5768, 5774, 5776, 5786, 5792, 5794, 5798, 5800, 5802, 5810, 5812, 5816, 5818, 5820, 5824, 5826, 5912, 5966, 5984, 5990, 5992, 6020, 6038, 6044, 6046, 6056, 6062, 6064, 6068, 6070, 6072, 6128]

end Chunk2

namespace Chunk3

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [6146, 6152, 6154, 6182, 6200, 6206, 6208, 6218, 6224, 6226, 6230, 6232, 6234, 6254, 6260, 6262, 6272, 6278, 6280, 6284, 6286, 6288, 6296, 6298, 6302, 6304, 6306, 6310, 6312, 6344, 6362, 6368, 6370, 6380, 6386, 6388, 6392, 6394, 6396, 6416, 6422, 6424, 6434, 6440, 6442, 6446, 6448, 6450, 6458, 6460, 6464, 6466, 6468, 6472, 6474, 6488, 6494, 6496, 6500, 6502, 6504, 6512, 6514, 6518]

end Chunk3

namespace Chunk4

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [6520, 6522, 6526, 6528, 6536, 6538, 6540, 6544, 6546, 6552]

end Chunk4

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes ++ Chunk1.codes ++ Chunk2.codes ++ Chunk3.codes ++ Chunk4.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 8 12 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 266 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total12
