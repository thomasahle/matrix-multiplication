import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent0LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot28.Left2.expected,
    Slot29.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1450710983537555009647411200 }, { target := 1, numerator := 29072248110092602393334120448 }, { target := 2, numerator := 48801917486203350524538912768 }, { target := 3, numerator := 46828950548592275711418433536 }, { target := 4, numerator := 1450710983537555009647411200 }, { target := 5, numerator := 46828950548592275711418433536 }, { target := 6, numerator := 31277328805069686007998185472 }, { target := 7, numerator := 1508739422879057210033307648 }, { target := 8, numerator := 29072248110092602393334120448 }, { target := 9, numerator := 1392682544196052809261514752 }, { target := 141, numerator := 21325451458002058641816944640 }, { target := 142, numerator := 21934750071087831745868857344 }, { target := 143, numerator := 21325451458002058641816944640 }, { target := 144, numerator := 18888257005658966225609293824 }, { target := 145, numerator := 884092287587456773979325333504 }, { target := 146, numerator := 240672952168880376100505518080 }, { target := 147, numerator := 21934750071087831745868857344 }, { target := 148, numerator := 884092287587456773979325333504 }, { target := 149, numerator := 21325451458002058641816944640 }, { target := 150, numerator := 21325451458002058641816944640 }, { target := 151, numerator := 18278958392573193121557381120 }, { target := 152, numerator := 21325451458002058641816944640 }, { target := 153, numerator := 240672952168880376100505518080 }, { target := 154, numerator := 18278958392573193121557381120 }, { target := 155, numerator := 21325451458002058641816944640 }, { target := 156, numerator := 18888257005658966225609293824 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0
