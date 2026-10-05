import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent1

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
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1857981386281780789641216 }, { target := 35, numerator := 93445510371127853693534208 }, { target := 40, numerator := 93407783649776851614695424 }, { target := 48, numerator := 1878713474949525081686016 }, { target := 79, numerator := 48837578673263821876887552 }, { target := 80, numerator := 2456242295056622843357822976 }, { target := 85, numerator := 2455250637263026177104150528 }, { target := 93, numerator := 49382527626384543320113152 }, { target := 121, numerator := 1857981386281780789641216 }, { target := 122, numerator := 48837578673263821876887552 }, { target := 124, numerator := 671201587884533853255106560 }, { target := 132, numerator := 48649105822216035495837696 }, { target := 139, numerator := 1815673972966461863362560 }, { target := 154, numerator := 671201587884533853255106560 }, { target := 155, numerator := 33757482935445017175816929280 }, { target := 160, numerator := 33743854039341194970755235840 }, { target := 168, numerator := 678691119769350331495874560 }, { target := 196, numerator := 93445510371127853693534208 }, { target := 197, numerator := 2456242295056622843357822976 }, { target := 199, numerator := 33757482935445017175816929280 }, { target := 207, numerator := 2446763221753037585224040448 }, { target := 214, numerator := 91317696896287880018657280 }, { target := 492, numerator := 48649105822216035495837696 }, { target := 493, numerator := 2446763221753037585224040448 }, { target := 498, numerator := 2445775390942200922996998144 }, { target := 506, numerator := 49191951720974514437226496 }, { target := 508, numerator := 93407783649776851614695424 }, { target := 509, numerator := 2455250637263026177104150528 }, { target := 511, numerator := 33743854039341194970755235840 }, { target := 519, numerator := 2445775390942200922996998144 }, { target := 526, numerator := 91280829236284323885219840 }, { target := 890, numerator := 1815673972966461863362560 }, { target := 891, numerator := 91317696896287880018657280 }, { target := 896, numerator := 91280829236284323885219840 }, { target := 904, numerator := 1835933978840141460930560 }, { target := 906, numerator := 1878713474949525081686016 }, { target := 907, numerator := 49382527626384543320113152 }, { target := 909, numerator := 678691119769350331495874560 }, { target := 917, numerator := 49191951720974514437226496 }, { target := 924, numerator := 1835933978840141460930560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent1
