import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 8 and weight 13

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total13

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [1457, 1943, 2105, 2159, 2177, 2183, 2185, 2915, 3401, 3563, 3617, 3635, 3641, 3643, 3887, 4049, 4103, 4121, 4127, 4129, 4211, 4265, 4283, 4289, 4291, 4319, 4337, 4343, 4345, 4355, 4361, 4363, 4367, 4369, 4371, 4859, 5021, 5075, 5093, 5099, 5101, 5345, 5507, 5561, 5579, 5585, 5587, 5669, 5723, 5741, 5747, 5749, 5777, 5795, 5801, 5803, 5813, 5819, 5821, 5825, 5827, 5829, 5993, 6047]

end Chunk0

namespace Chunk1

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [6065, 6071, 6073, 6155, 6209, 6227, 6233, 6235, 6263, 6281, 6287, 6289, 6299, 6305, 6307, 6311, 6313, 6315, 6371, 6389, 6395, 6397, 6425, 6443, 6449, 6451, 6461, 6467, 6469, 6473, 6475, 6477, 6497, 6503, 6505, 6515, 6521, 6523, 6527, 6529, 6531, 6539, 6541, 6545, 6547, 6549, 6553, 6555]

end Chunk1

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes ++ Chunk1.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 8 13 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 112 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total13
