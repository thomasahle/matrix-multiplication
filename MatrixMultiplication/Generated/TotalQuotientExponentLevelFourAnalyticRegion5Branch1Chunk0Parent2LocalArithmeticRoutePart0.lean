import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent2

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
  [{ target := 71, numerator := 410761049984953332269056 }, { target := 72, numerator := 13728532994943561725116416 }, { target := 74, numerator := 152120942522018528996884480 }, { target := 82, numerator := 13728371705559781868568576 }, { target := 89, numerator := 410513739596490885562368 }, { target := 146, numerator := 13728532994943561725116416 }, { target := 147, numerator := 458837609359889448227045376 }, { target := 149, numerator := 5084214724623829195586273280 }, { target := 157, numerator := 458832218715798347119067136 }, { target := 164, numerator := 13720267340670540026216448 }, { target := 242, numerator := 152120942522018528996884480 }, { target := 243, numerator := 5084214724623829195586273280 }, { target := 245, numerator := 56336357000341048554579558400 }, { target := 253, numerator := 5084154992833095176112046080 }, { target := 260, numerator := 152029353776226365803069440 }, { target := 640, numerator := 13728371705559781868568576 }, { target := 641, numerator := 458832218715798347119067136 }, { target := 643, numerator := 5084154992833095176112046080 }, { target := 651, numerator := 458826828135039115770986496 }, { target := 658, numerator := 13720106148395627134844928 }, { target := 1017, numerator := 410513739596490885562368 }, { target := 1018, numerator := 13720267340670540026216448 }, { target := 1020, numerator := 152029353776226365803069440 }, { target := 1028, numerator := 13720106148395627134844928 }, { target := 1035, numerator := 410266578108291118792704 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent2
