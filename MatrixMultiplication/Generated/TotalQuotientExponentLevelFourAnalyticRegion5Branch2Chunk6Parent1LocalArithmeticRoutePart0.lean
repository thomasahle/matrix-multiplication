import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk6Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2543065914349282771599360 }, { target := 57, numerator := 64369481739156399883026432 }, { target := 59, numerator := 686977177979630626057224192 }, { target := 67, numerator := 64430092658996329888874496 }, { target := 74, numerator := 2408586964680220958785536 }, { target := 110, numerator := 2543065914349282771599360 }, { target := 112, numerator := 120203396071079913728245760 }, { target := 115, numerator := 120202693712200027162542080 }, { target := 122, numerator := 2543065914349282771599360 }, { target := 152, numerator := 120203396071079913728245760 }, { target := 153, numerator := 3042559874175266423792730112 }, { target := 155, numerator := 32471431177043642739979190272 }, { target := 163, numerator := 3045424777661504146464833536 }, { target := 170, numerator := 113846963719451584732594176 }, { target := 206, numerator := 64369481739156399883026432 }, { target := 208, numerator := 3042559874175266423792730112 }, { target := 211, numerator := 3042542096233751777269252096 }, { target := 218, numerator := 64369481739156399883026432 }, { target := 283, numerator := 120202693712200027162542080 }, { target := 284, numerator := 3042542096233751777269252096 }, { target := 286, numerator := 32471241443651947751198949376 }, { target := 294, numerator := 3045406982980109685005221888 }, { target := 301, numerator := 113846298501757825091371008 }, { target := 302, numerator := 686977177979630626057224192 }, { target := 304, numerator := 32471431177043642739979190272 }, { target := 307, numerator := 32471241443651947751198949376 }, { target := 314, numerator := 686977177979630626057224192 }, { target := 660, numerator := 2543065914349282771599360 }, { target := 661, numerator := 64369481739156399883026432 }, { target := 663, numerator := 686977177979630626057224192 }, { target := 671, numerator := 64430092658996329888874496 }, { target := 678, numerator := 2408586964680220958785536 }, { target := 679, numerator := 64430092658996329888874496 }, { target := 681, numerator := 3045424777661504146464833536 }, { target := 684, numerator := 3045406982980109685005221888 }, { target := 691, numerator := 64430092658996329888874496 }, { target := 966, numerator := 2408586964680220958785536 }, { target := 968, numerator := 113846963719451584732594176 }, { target := 971, numerator := 113846298501757825091371008 }, { target := 978, numerator := 2408586964680220958785536 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent1
