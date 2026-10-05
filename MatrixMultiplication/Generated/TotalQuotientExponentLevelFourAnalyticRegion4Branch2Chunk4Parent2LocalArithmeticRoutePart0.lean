import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 51; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1738442421311379100139520 }, { target := 35, numerator := 78531909389106456878383104 }, { target := 40, numerator := 78518609620458634670505984 }, { target := 48, numerator := 1738442421311379100139520 }, { target := 79, numerator := 60754146583204121972572160 }, { target := 80, numerator := 2744490744125773202463916032 }, { target := 85, numerator := 2744025950995988108460163072 }, { target := 93, numerator := 60754146583204121972572160 }, { target := 121, numerator := 1738442421311379100139520 }, { target := 122, numerator := 60754146583204121972572160 }, { target := 124, numerator := 733020105169087798517432320 }, { target := 132, numerator := 60755578536482641627054080 }, { target := 139, numerator := 1738493562499897659228160 }, { target := 154, numerator := 733020105169087798517432320 }, { target := 155, numerator := 33113244231642755315389169664 }, { target := 160, numerator := 33107636339374688652171935744 }, { target := 168, numerator := 733020105169087798517432320 }, { target := 196, numerator := 78531909389106456878383104 }, { target := 197, numerator := 2744490744125773202463916032 }, { target := 199, numerator := 33113244231642755315389169664 }, { target := 207, numerator := 2744555430780757904631791616 }, { target := 214, numerator := 78534219626784481955807232 }, { target := 492, numerator := 60755578536482641627054080 }, { target := 493, numerator := 2744555430780757904631791616 }, { target := 498, numerator := 2744090626695966717049307136 }, { target := 506, numerator := 60755578536482641627054080 }, { target := 508, numerator := 78518609620458634670505984 }, { target := 509, numerator := 2744025950995988108460163072 }, { target := 511, numerator := 33107636339374688652171935744 }, { target := 519, numerator := 2744090626695966717049307136 }, { target := 526, numerator := 78520919466886442120118272 }, { target := 890, numerator := 1738493562499897659228160 }, { target := 891, numerator := 78534219626784481955807232 }, { target := 896, numerator := 78520919466886442120118272 }, { target := 904, numerator := 1738493562499897659228160 }, { target := 906, numerator := 1738442421311379100139520 }, { target := 907, numerator := 60754146583204121972572160 }, { target := 909, numerator := 733020105169087798517432320 }, { target := 917, numerator := 60755578536482641627054080 }, { target := 924, numerator := 1738493562499897659228160 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent2
