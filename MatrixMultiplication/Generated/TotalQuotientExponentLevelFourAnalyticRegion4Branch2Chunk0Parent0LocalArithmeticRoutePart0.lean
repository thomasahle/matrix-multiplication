import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1913486838403264088637440 }, { target := 35, numerator := 90684848684675425833582592 }, { target := 40, numerator := 90660663102957224837775360 }, { target := 48, numerator := 1938047732662961585520640 }, { target := 79, numerator := 59308382326813442923560960 }, { target := 80, numerator := 2810770144375810261178646528 }, { target := 85, numerator := 2810020514068169150945034240 }, { target := 93, numerator := 60069645418781252266229760 }, { target := 121, numerator := 1913486838403264088637440 }, { target := 122, numerator := 59308382326813442923560960 }, { target := 124, numerator := 696154196550687504822435840 }, { target := 132, numerator := 59308821457331984101539840 }, { target := 139, numerator := 1913730799802453631959040 }, { target := 154, numerator := 696154196550687504822435840 }, { target := 155, numerator := 32992459999401478676872691712 }, { target := 160, numerator := 32983660934850193342290984960 }, { target := 168, numerator := 705089805234671927206871040 }, { target := 196, numerator := 90684848684675425833582592 }, { target := 197, numerator := 2810770144375810261178646528 }, { target := 199, numerator := 32992459999401478676872691712 }, { target := 207, numerator := 2810790955851398961967398912 }, { target := 214, numerator := 90696410615558037382889472 }, { target := 492, numerator := 59308821457331984101539840 }, { target := 493, numerator := 2810790955851398961967398912 }, { target := 498, numerator := 2810041319993352785976360960 }, { target := 506, numerator := 60070090185836202075095040 }, { target := 508, numerator := 90660663102957224837775360 }, { target := 509, numerator := 2810020514068169150945034240 }, { target := 511, numerator := 32983660934850193342290984960 }, { target := 519, numerator := 2810041319993352785976360960 }, { target := 526, numerator := 90672221950281466521845760 }, { target := 890, numerator := 1913730799802453631959040 }, { target := 891, numerator := 90696410615558037382889472 }, { target := 896, numerator := 90672221950281466521845760 }, { target := 904, numerator := 1938294825471267034890240 }, { target := 906, numerator := 1938047732662961585520640 }, { target := 907, numerator := 60069645418781252266229760 }, { target := 909, numerator := 705089805234671927206871040 }, { target := 917, numerator := 60070090185836202075095040 }, { target := 924, numerator := 1938294825471267034890240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent0
