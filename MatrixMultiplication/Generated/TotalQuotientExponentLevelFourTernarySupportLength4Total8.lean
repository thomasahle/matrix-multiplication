import MatrixMultiplication.BetaFourLocalGeometry

/-!
# Shared checked ternary support of length 4 and weight 8

The untrusted producer writes this finite support in chunks of at most sixty-four natural numbers.
Lean recomputes it from `ternarySupportCodes`; every parent-local routing certificate with the same
length and weight reuses the resulting checked inert list.

Certificate source: `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8

open MatrixMultiplication.BetaFourLocalGeometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Chunk0

/-- Bounded literal chunk of this exact ternary support. -/
def codes : List ℕ := [80]

end Chunk0

/-- Full support assembled from independently bounded literal chunks. -/
def codes : List ℕ := Chunk0.codes

/-- Kernel computation checks the assembled support against its semantic enumeration. -/
theorem codes_eq : ternarySupportCodes 4 8 = codes := by
  rfl

/-- The assembled chunks have the advertised exact support length. -/
theorem codes_length : codes.length = 1 := by
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8
