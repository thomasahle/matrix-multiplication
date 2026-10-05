import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 203867376614638624293519360 }, { target := 37, numerator := 7158521497985348451728097280 }, { target := 40, numerator := 7158139714010441149453434880 }, { target := 47, numerator := 204235117960583818898309120 }, { target := 86, numerator := 203867376614638624293519360 }, { target := 89, numerator := 689343905702771796190691328 }, { target := 91, numerator := 203718893789482248333950976 }, { target := 145, numerator := 689343905702771796190691328 }, { target := 147, numerator := 24205359633416421664719110144 }, { target := 150, numerator := 24204068693881280605794074624 }, { target := 157, numerator := 690587362404436402373656576 }, { target := 161, numerator := 7158521497985348451728097280 }, { target := 164, numerator := 24205359633416421664719110144 }, { target := 166, numerator := 7153307728555368968668315648 }, { target := 216, numerator := 203718893789482248333950976 }, { target := 218, numerator := 7153307728555368968668315648 }, { target := 221, numerator := 7152926222645369034200055808 }, { target := 228, numerator := 204086367298194828890734592 }, { target := 232, numerator := 7158139714010441149453434880 }, { target := 235, numerator := 24204068693881280605794074624 }, { target := 237, numerator := 7152926222645369034200055808 }, { target := 406, numerator := 204235117960583818898309120 }, { target := 409, numerator := 690587362404436402373656576 }, { target := 411, numerator := 204086367298194828890734592 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent0
