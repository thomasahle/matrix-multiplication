import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent3

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
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1106096289450142650177945600 }, { target := 2, numerator := 38507966078216094668013174784 }, { target := 5, numerator := 38508008579514440494820098048 }, { target := 12, numerator := 1106091567083659780532731904 }, { target := 16, numerator := 64230660228206630276664655872 }, { target := 19, numerator := 228038986821464473535348998144 }, { target := 21, numerator := 64257051207953035271417626624 }, { target := 26, numerator := 64230660228206630276664655872 }, { target := 28, numerator := 64230671001843196711978139648 }, { target := 44, numerator := 1106096289450142650177945600 }, { target := 50, numerator := 64230671001843196711978139648 }, { target := 53, numerator := 228039031456635876804707483648 }, { target := 55, numerator := 64257061912275825741778649088 }, { target := 60, numerator := 228038986821464473535348998144 }, { target := 62, numerator := 228039031456635876804707483648 }, { target := 64, numerator := 38507966078216094668013174784 }, { target := 71, numerator := 64257051207953035271417626624 }, { target := 73, numerator := 64257061912275825741778649088 }, { target := 75, numerator := 38508008579514440494820098048 }, { target := 104, numerator := 1106091567083659780532731904 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent3
