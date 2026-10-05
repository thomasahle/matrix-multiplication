import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent3

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
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1059774596619674300276801536 }, { target := 2, numerator := 38536338056045175496457060352 }, { target := 5, numerator := 38554287771046563017914318848 }, { target := 12, numerator := 1077762090552924778895769600 }, { target := 16, numerator := 44304793300125035234641051648 }, { target := 19, numerator := 148963084005540260937933520896 }, { target := 21, numerator := 44326195808446694380795854848 }, { target := 26, numerator := 44304793300125035234641051648 }, { target := 28, numerator := 44338667669590866287677931520 }, { target := 44, numerator := 1059774596619674300276801536 }, { target := 50, numerator := 44338667669590866287677931520 }, { target := 53, numerator := 149076151443713782505539633152 }, { target := 55, numerator := 44360082858169386214675709952 }, { target := 60, numerator := 148963084005540260937933520896 }, { target := 62, numerator := 149076151443713782505539633152 }, { target := 64, numerator := 38536338056045175496457060352 }, { target := 71, numerator := 44326195808446694380795854848 }, { target := 73, numerator := 44360082858169386214675709952 }, { target := 75, numerator := 38554287771046563017914318848 }, { target := 104, numerator := 1077762090552924778895769600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent3
