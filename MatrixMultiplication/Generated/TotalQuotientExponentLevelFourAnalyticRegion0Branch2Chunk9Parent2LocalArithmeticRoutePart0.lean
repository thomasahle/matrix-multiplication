import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk9Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 21398131545860751408142221312 }, { target := 19, numerator := 76052509452523884336346300416 }, { target := 21, numerator := 21391574438812973427956121600 }, { target := 26, numerator := 21398131545860751408142221312 }, { target := 28, numerator := 21398139977585542164104871936 }, { target := 50, numerator := 21398139977585542164104871936 }, { target := 53, numerator := 76052549055099470304549797888 }, { target := 55, numerator := 21391583072910391139532537856 }, { target := 60, numerator := 76052509452523884336346300416 }, { target := 62, numerator := 76052549055099470304549797888 }, { target := 71, numerator := 21391574438812973427956121600 }, { target := 73, numerator := 21391583072910391139532537856 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent2
