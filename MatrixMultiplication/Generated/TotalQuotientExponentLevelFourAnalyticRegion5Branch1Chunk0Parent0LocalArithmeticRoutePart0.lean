import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 8986019846040259133440000 }, { target := 82, numerator := 412899804008487655886028800 }, { target := 85, numerator := 412894120951302249145958400 }, { target := 92, numerator := 8988886520903694391705600 }, { target := 176, numerator := 412899804008487655886028800 }, { target := 178, numerator := 18972387227185265559287627776 }, { target := 181, numerator := 18972126095645582004760608768 }, { target := 188, numerator := 413031525227620068346560512 }, { target := 286, numerator := 412894120951302249145958400 }, { target := 288, numerator := 18972126095645582004760608768 }, { target := 291, numerator := 18971864967700052427851956224 }, { target := 298, numerator := 413025840357454336613154816 }, { target := 573, numerator := 8988886520903694391705600 }, { target := 575, numerator := 413031525227620068346560512 }, { target := 578, numerator := 413025840357454336613154816 }, { target := 585, numerator := 8991754110279328982892544 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent0
