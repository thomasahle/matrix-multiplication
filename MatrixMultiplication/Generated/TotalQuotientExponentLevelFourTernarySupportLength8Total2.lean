import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 8 and weight 2

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total2

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [2, 4, 6, 10, 12, 18, 28, 30, 36, 54, 82, 84, 90, 108, 162, 244, 246, 252, 270, 324, 486, 730, 732, 738, 756, 810, 972, 1458, 2188, 2190, 2196, 2214, 2268, 2430, 2916, 4374]

end Chunk0

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 8 2 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 36 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length8.Total2
