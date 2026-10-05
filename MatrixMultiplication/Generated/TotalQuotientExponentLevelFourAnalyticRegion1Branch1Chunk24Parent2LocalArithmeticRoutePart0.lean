import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk24Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 100; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 84794156157466230576440672256 }, { target := 3, numerator := 305780643881187632929801502720 }, { target := 5, numerator := 84794175046932162055021527040 }, { target := 10, numerator := 38685623977165356598032334848 }, { target := 11, numerator := 10367746593083206863740207104 }, { target := 12, numerator := 38685626227668133590597632000 }, { target := 13, numerator := 10367746593083206863740207104 }, { target := 14, numerator := 84794156157466230576440672256 }, { target := 15, numerator := 10367746593083206863740207104 }, { target := 17, numerator := 10367749064946912740820123648 }, { target := 21, numerator := 38685626227668133590597632000 }, { target := 22, numerator := 10367749064946912740820123648 }, { target := 23, numerator := 38685628478170910583162929152 }, { target := 24, numerator := 10367749064946912740820123648 }, { target := 25, numerator := 305780643881187632929801502720 }, { target := 27, numerator := 84794175046932162055021527040 }, { target := 28, numerator := 10367746593083206863740207104 }, { target := 30, numerator := 10367749064946912740820123648 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent2
