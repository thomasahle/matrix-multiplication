import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk9Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1080217721124016994406891520 }, { target := 2, numerator := 38533872980741117541655511040 }, { target := 5, numerator := 38533872980741117541655511040 }, { target := 12, numerator := 1080198831658085515826036736 }, { target := 16, numerator := 64165146029151730862175289344 }, { target := 19, numerator := 228192342552444446584229330944 }, { target := 21, numerator := 64169549686414728251482046464 }, { target := 26, numerator := 64165146029151730862175289344 }, { target := 28, numerator := 64165035638935840339592740864 }, { target := 44, numerator := 1080217721124016994406891520 }, { target := 50, numerator := 64165035638935840339592740864 }, { target := 53, numerator := 228191949526268897465806618624 }, { target := 55, numerator := 64169439195163394838609526784 }, { target := 60, numerator := 228192342552444446584229330944 }, { target := 62, numerator := 228191949526268897465806618624 }, { target := 64, numerator := 38533872980741117541655511040 }, { target := 71, numerator := 64169549686414728251482046464 }, { target := 73, numerator := 64169439195163394838609526784 }, { target := 75, numerator := 38533872980741117541655511040 }, { target := 104, numerator := 1080198831658085515826036736 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent1
