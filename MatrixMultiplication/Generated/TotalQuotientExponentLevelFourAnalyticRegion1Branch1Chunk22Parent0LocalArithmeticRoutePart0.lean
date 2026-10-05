import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk22Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 90; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot1.Left0.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3623759843049501406478750187520 }, { target := 1, numerator := 20735495658030119604560330752 }, { target := 2, numerator := 3623760116946757412918172581888 }, { target := 3, numerator := 20735495658030119604560330752 }, { target := 4, numerator := 3742602082098531429999420899328 }, { target := 5, numerator := 20735495658030119604560330752 }, { target := 6, numerator := 3742602365440520402178133721088 }, { target := 7, numerator := 20735495658030119604560330752 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent0
