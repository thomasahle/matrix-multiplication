import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk9Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 483210107964458896510156800 }, { target := 37, numerator := 21011705308297042667946115072 }, { target := 40, numerator := 21019717701948087144667938816 }, { target := 47, numerator := 488388332223220800223707136 }, { target := 86, numerator := 483210107964458896510156800 }, { target := 89, numerator := 1705455369055997816916148224 }, { target := 91, numerator := 482895301500973325091864576 }, { target := 145, numerator := 1705455369055997816916148224 }, { target := 147, numerator := 74125890919315495547731705856 }, { target := 150, numerator := 74154090021487113497210781696 }, { target := 157, numerator := 1723661212909093767159480320 }, { target := 161, numerator := 21011705308297042667946115072 }, { target := 164, numerator := 74125890919315495547731705856 }, { target := 166, numerator := 20996700931512027519748407296 }, { target := 216, numerator := 482895301500973325091864576 }, { target := 218, numerator := 20996700931512027519748407296 }, { target := 221, numerator := 21004704953068473581683343360 }, { target := 228, numerator := 488067383511028215742201856 }, { target := 232, numerator := 21019717701948087144667938816 }, { target := 235, numerator := 74154090021487113497210781696 }, { target := 237, numerator := 21004704953068473581683343360 }, { target := 406, numerator := 488388332223220800223707136 }, { target := 409, numerator := 1723661212909093767159480320 }, { target := 411, numerator := 488067383511028215742201856 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9.Parent0
