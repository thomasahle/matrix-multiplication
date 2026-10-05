import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk11Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 88; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11.Parent3

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
  [{ target := 35, numerator := 177815115891435716896358400 }, { target := 37, numerator := 7141905854081297492738048000 }, { target := 40, numerator := 7143294128009599317861990400 }, { target := 47, numerator := 176439058075639376091545600 }, { target := 86, numerator := 177815115891435716896358400 }, { target := 89, numerator := 606698733977553341018800128 }, { target := 91, numerator := 177814714376670113377026048 }, { target := 145, numerator := 606698733977553341018800128 }, { target := 147, numerator := 24367924054912666718867292160 }, { target := 150, numerator := 24372660795265095489780973568 }, { target := 157, numerator := 602003674558458324217495552 }, { target := 161, numerator := 7141905854081297492738048000 }, { target := 164, numerator := 24367924054912666718867292160 }, { target := 166, numerator := 7141889727327165326357954560 }, { target := 216, numerator := 177814714376670113377026048 }, { target := 218, numerator := 7141889727327165326357954560 }, { target := 221, numerator := 7143277998120680335855321088 }, { target := 228, numerator := 176438659668076040481144832 }, { target := 232, numerator := 7143294128009599317861990400 }, { target := 235, numerator := 24372660795265095489780973568 }, { target := 237, numerator := 7143277998120680335855321088 }, { target := 406, numerator := 176439058075639376091545600 }, { target := 409, numerator := 602003674558458324217495552 }, { target := 411, numerator := 176438659668076040481144832 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11.Parent3
