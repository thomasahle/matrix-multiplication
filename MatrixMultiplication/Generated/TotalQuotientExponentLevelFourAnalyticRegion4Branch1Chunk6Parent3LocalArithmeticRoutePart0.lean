import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1048256744767955235600596992 }, { target := 2, numerator := 38565824512364213561171378176 }, { target := 5, numerator := 38565867013662559387978301440 }, { target := 12, numerator := 1048214243469609408793673728 }, { target := 16, numerator := 66608985291989366267845804032 }, { target := 19, numerator := 223352258353070215982288470016 }, { target := 21, numerator := 66565681286155734576267264000 }, { target := 26, numerator := 66608985291989366267845804032 }, { target := 28, numerator := 66608916521365530774775791616 }, { target := 44, numerator := 1048256744767955235600596992 }, { target := 50, numerator := 66608916521365530774775791616 }, { target := 53, numerator := 223352008849894857567583076352 }, { target := 55, numerator := 66565612325903333173135147008 }, { target := 60, numerator := 223352258353070215982288470016 }, { target := 62, numerator := 223352008849894857567583076352 }, { target := 64, numerator := 38565824512364213561171378176 }, { target := 71, numerator := 66565681286155734576267264000 }, { target := 73, numerator := 66565612325903333173135147008 }, { target := 75, numerator := 38565867013662559387978301440 }, { target := 104, numerator := 1048214243469609408793673728 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent3
