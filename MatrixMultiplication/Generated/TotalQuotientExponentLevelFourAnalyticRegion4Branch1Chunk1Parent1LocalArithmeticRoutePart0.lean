import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent1

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 548462668914507194862403584 }, { target := 21, numerator := 19258509485254259000561631232 }, { target := 24, numerator := 19257482375074574602885660672 }, { target := 31, numerator := 549452000328961821589372928 }, { target := 35, numerator := 5635738813334392730739015680 }, { target := 38, numerator := 18622765668535380006259392512 }, { target := 40, numerator := 5628106283460734234147160064 }, { target := 71, numerator := 548462668914507194862403584 }, { target := 73, numerator := 548467507192385473955758080 }, { target := 90, numerator := 548467507192385473955758080 }, { target := 92, numerator := 19258679374702880084553891840 }, { target := 95, numerator := 19257652255462516186561904640 }, { target := 102, numerator := 549456847334253228573327360 }, { target := 106, numerator := 18622765668535380006259392512 }, { target := 109, numerator := 61503813830255459125677785088 }, { target := 111, numerator := 18597273299457504281408569344 }, { target := 116, numerator := 19258509485254259000561631232 }, { target := 118, numerator := 19258679374702880084553891840 }, { target := 140, numerator := 5628106283460734234147160064 }, { target := 143, numerator := 18597273299457504281408569344 }, { target := 145, numerator := 5620481882031586287040856064 }, { target := 150, numerator := 19257482375074574602885660672 }, { target := 152, numerator := 19257652255462516186561904640 }, { target := 232, numerator := 549452000328961821589372928 }, { target := 234, numerator := 549456847334253228573327360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent1
