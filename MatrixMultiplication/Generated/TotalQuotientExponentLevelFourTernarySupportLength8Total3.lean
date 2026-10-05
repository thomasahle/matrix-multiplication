import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 8 and weight 3

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total3

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [5, 7, 11, 13, 15, 19, 21, 29, 31, 33, 37, 39, 45, 55, 57, 63, 83, 85, 87, 91, 93, 99, 109, 111, 117, 135, 163, 165, 171, 189, 245, 247, 249, 253, 255, 261, 271, 273, 279, 297, 325, 327, 333, 351, 405, 487, 489, 495, 513, 567, 731, 733, 735, 739, 741, 747, 757, 759, 765, 783, 811, 813, 819, 837]

end Chunk0

namespace Chunk1

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [891, 973, 975, 981, 999, 1053, 1215, 1459, 1461, 1467, 1485, 1539, 1701, 2189, 2191, 2193, 2197, 2199, 2205, 2215, 2217, 2223, 2241, 2269, 2271, 2277, 2295, 2349, 2431, 2433, 2439, 2457, 2511, 2673, 2917, 2919, 2925, 2943, 2997, 3159, 3645, 4375, 4377, 4383, 4401, 4455, 4617, 5103]

end Chunk1

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes ++ Chunk1.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 8 3 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 112 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total3
