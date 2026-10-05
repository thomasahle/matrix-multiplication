import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 15; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 84974087765196529798372917248 }, { target := 3, numerator := 305400176980762274223869657088 }, { target := 5, numerator := 84994710339627221539021127680 }, { target := 10, numerator := 38724305088552412691210174464 }, { target := 11, numerator := 10348401315023195947506073600 }, { target := 12, numerator := 38724311853895801724188229632 }, { target := 13, numerator := 10348401315023195947506073600 }, { target := 14, numerator := 84974087765196529798372917248 }, { target := 15, numerator := 10348401315023195947506073600 }, { target := 17, numerator := 10348408716779255523463659520 }, { target := 21, numerator := 38724311853895801724188229632 }, { target := 22, numerator := 10348408716779255523463659520 }, { target := 23, numerator := 38724318619239190757166284800 }, { target := 24, numerator := 10348408716779255523463659520 }, { target := 25, numerator := 305400176980762274223869657088 }, { target := 27, numerator := 84994710339627221539021127680 }, { target := 28, numerator := 10348401315023195947506073600 }, { target := 30, numerator := 10348408716779255523463659520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent1
