import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 650817215808017111449600 }, { target := 72, numerator := 14895897938746253183549440 }, { target := 74, numerator := 195981900387784727807918080 }, { target := 82, numerator := 14895546035915619754311680 }, { target := 89, numerator := 650830750532272243343360 }, { target := 146, numerator := 14895897938746253183549440 }, { target := 147, numerator := 340937163326360093999497216 }, { target := 149, numerator := 4485631779720990955575181312 }, { target := 157, numerator := 340929108977885363780452352 }, { target := 164, numerator := 14896207721379896653512704 }, { target := 242, numerator := 195981900387784727807918080 }, { target := 243, numerator := 4485631779720990955575181312 }, { target := 245, numerator := 59016424806650657732804214784 }, { target := 253, numerator := 4485525810512088337234264064 }, { target := 260, numerator := 195985976126588674667184128 }, { target := 640, numerator := 14895546035915619754311680 }, { target := 641, numerator := 340929108977885363780452352 }, { target := 643, numerator := 4485525810512088337234264064 }, { target := 651, numerator := 340921054819687717817810944 }, { target := 658, numerator := 14895855811230913829797888 }, { target := 1017, numerator := 650830750532272243343360 }, { target := 1018, numerator := 14896207721379896653512704 }, { target := 1020, numerator := 195985976126588674667184128 }, { target := 1028, numerator := 14895855811230913829797888 }, { target := 1035, numerator := 650844285538002351947776 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent0
