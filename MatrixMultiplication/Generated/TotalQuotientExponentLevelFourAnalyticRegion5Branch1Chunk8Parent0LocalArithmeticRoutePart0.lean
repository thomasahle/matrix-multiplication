import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 14447645412626085096011595776 }, { target := 19, numerator := 50342297512149512448165019648 }, { target := 21, numerator := 14438177088190394222560411648 }, { target := 26, numerator := 14447645412626085096011595776 }, { target := 28, numerator := 14447660347719874560810549248 }, { target := 50, numerator := 14447660347719874560810549248 }, { target := 53, numerator := 50342352685283550702585511936 }, { target := 55, numerator := 14438191982559258156954812416 }, { target := 60, numerator := 50342297512149512448165019648 }, { target := 62, numerator := 50342352685283550702585511936 }, { target := 71, numerator := 14438177088190394222560411648 }, { target := 73, numerator := 14438191982559258156954812416 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent0
