import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk24Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 100; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot7.Left0.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 84477554541355200952378851328 }, { target := 3, numerator := 306413870725242106526151213056 }, { target := 5, numerator := 84477549818988718082733637632 }, { target := 10, numerator := 38492198096529792922644643840 }, { target := 11, numerator := 10464461894584230136256659456 }, { target := 12, numerator := 38492198096529792922644643840 }, { target := 13, numerator := 10464461894584230136256659456 }, { target := 14, numerator := 84477554541355200952378851328 }, { target := 15, numerator := 10464461894584230136256659456 }, { target := 17, numerator := 10464461894584230136256659456 }, { target := 21, numerator := 38492198096529792922644643840 }, { target := 22, numerator := 10464461894584230136256659456 }, { target := 23, numerator := 38492198096529792922644643840 }, { target := 24, numerator := 10464461894584230136256659456 }, { target := 25, numerator := 306413870725242106526151213056 }, { target := 27, numerator := 84477549818988718082733637632 }, { target := 28, numerator := 10464461894584230136256659456 }, { target := 30, numerator := 10464461894584230136256659456 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24.Parent2
