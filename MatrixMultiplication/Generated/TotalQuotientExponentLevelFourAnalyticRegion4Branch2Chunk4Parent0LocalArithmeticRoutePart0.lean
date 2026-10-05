import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1346849329296230964153810944 }, { target := 21, numerator := 58074206443299409553642225664 }, { target := 24, numerator := 58074241861056475325282648064 }, { target := 31, numerator := 1346898914079561850785103872 }, { target := 35, numerator := 18204431596559506248103362560 }, { target := 38, numerator := 64049917287687201480708718592 }, { target := 40, numerator := 18223745003225637140291387392 }, { target := 71, numerator := 1346849329296230964153810944 }, { target := 73, numerator := 1346849903296891971126165504 }, { target := 90, numerator := 1346849903296891971126165504 }, { target := 92, numerator := 58074253092907282247779876864 }, { target := 95, numerator := 58074288510647459520817659904 }, { target := 102, numerator := 1346899488209701347044360192 }, { target := 106, numerator := 64049917287687201480708718592 }, { target := 109, numerator := 225366898659895774515820494848 }, { target := 111, numerator := 64117701181531781356245221376 }, { target := 116, numerator := 58074206443299409553642225664 }, { target := 118, numerator := 58074253092907282247779876864 }, { target := 140, numerator := 18223745003225637140291387392 }, { target := 143, numerator := 64117701181531781356245221376 }, { target := 145, numerator := 18243080398505842436393140224 }, { target := 150, numerator := 58074241861056475325282648064 }, { target := 152, numerator := 58074288510647459520817659904 }, { target := 232, numerator := 1346898914079561850785103872 }, { target := 234, numerator := 1346899488209701347044360192 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent0
