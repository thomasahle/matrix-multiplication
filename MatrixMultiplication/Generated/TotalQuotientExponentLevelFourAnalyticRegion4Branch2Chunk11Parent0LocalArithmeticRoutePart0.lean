import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk11Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 85; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 144138687343612283867627520 }, { target := 37, numerator := 6641760605741182518831349760 }, { target := 40, numerator := 6641750089510949010622382080 }, { target := 47, numerator := 144124935350230003902054400 }, { target := 86, numerator := 144138687343612283867627520 }, { target := 89, numerator := 553159969660576438438330368 }, { target := 91, numerator := 144142047646490401160822784 }, { target := 145, numerator := 553159969660576438438330368 }, { target := 147, numerator := 25489035337239187312905027584 }, { target := 150, numerator := 25488994979180541728650166272 }, { target := 157, numerator := 553107193737732212874280960 }, { target := 161, numerator := 6641760605741182518831349760 }, { target := 164, numerator := 25489035337239187312905027584 }, { target := 166, numerator := 6641915444998362886247022592 }, { target := 216, numerator := 144142047646490401160822784 }, { target := 218, numerator := 6641915444998362886247022592 }, { target := 221, numerator := 6641904928522964673323073536 }, { target := 228, numerator := 144128295332508122721812480 }, { target := 232, numerator := 6641750089510949010622382080 }, { target := 235, numerator := 25488994979180541728650166272 }, { target := 237, numerator := 6641904928522964673323073536 }, { target := 406, numerator := 144124935350230003902054400 }, { target := 409, numerator := 553107193737732212874280960 }, { target := 411, numerator := 144128295332508122721812480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11.Parent0
