import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14647538847476644736193789952 }, { target := 3, numerator := 49933061207478633772930301952 }, { target := 5, numerator := 14647562459309059084419858432 }, { target := 10, numerator := 79228238071550476855657103360 }, { target := 12, numerator := 79228162514841924245754216448 }, { target := 14, numerator := 14647538847476644736193789952 }, { target := 21, numerator := 79228162514841924245754216448 }, { target := 23, numerator := 79228086955823025027010265088 }, { target := 25, numerator := 49933061207478633772930301952 }, { target := 27, numerator := 14647562459309059084419858432 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent1
