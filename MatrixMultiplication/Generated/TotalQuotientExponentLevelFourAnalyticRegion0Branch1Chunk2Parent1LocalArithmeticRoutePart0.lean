import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 41; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent1

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
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7566869932730817038990180352 }, { target := 19, numerator := 24472420013596942904424660992 }, { target := 21, numerator := 7571244813575773749801648128 }, { target := 26, numerator := 7566869932730817038990180352 }, { target := 28, numerator := 7568224919903221347646439424 }, { target := 50, numerator := 7568224919903221347646439424 }, { target := 53, numerator := 24476802250306560463265071104 }, { target := 55, numerator := 7572600584151022089415950336 }, { target := 60, numerator := 24472420013596942904424660992 }, { target := 62, numerator := 24476802250306560463265071104 }, { target := 71, numerator := 7571244813575773749801648128 }, { target := 73, numerator := 7572600584151022089415950336 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent1
