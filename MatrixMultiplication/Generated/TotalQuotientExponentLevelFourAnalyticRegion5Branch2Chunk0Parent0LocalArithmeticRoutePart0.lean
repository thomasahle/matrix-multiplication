import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent0

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
  [{ target := 71, numerator := 621064045258205481140224 }, { target := 72, numerator := 17835960346344098818424832 }, { target := 74, numerator := 184910240550766720298516480 }, { target := 82, numerator := 17835127377726993950834688 }, { target := 89, numerator := 621328479739826074025984 }, { target := 146, numerator := 17835960346344098818424832 }, { target := 147, numerator := 512220090512728152789221376 }, { target := 149, numerator := 5310324665027531715001712640 }, { target := 157, numerator := 512196168993944603128233984 }, { target := 164, numerator := 17843554479291257440960512 }, { target := 242, numerator := 184910240550766720298516480 }, { target := 243, numerator := 5310324665027531715001712640 }, { target := 245, numerator := 55053576714986419650140569600 }, { target := 253, numerator := 5310076664151396524501237760 }, { target := 260, numerator := 184988970987635034743111680 }, { target := 640, numerator := 17835127377726993950834688 }, { target := 641, numerator := 512196168993944603128233984 }, { target := 643, numerator := 5310076664151396524501237760 }, { target := 651, numerator := 512172248592335236031840256 }, { target := 658, numerator := 17842721156015681917943808 }, { target := 1017, numerator := 621328479739826074025984 }, { target := 1018, numerator := 17843554479291257440960512 }, { target := 1020, numerator := 184988970987635034743111680 }, { target := 1028, numerator := 17842721156015681917943808 }, { target := 1035, numerator := 621593026811437351174144 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent0
