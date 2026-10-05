import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 950325639770079845475680256 }, { target := 21, numerator := 38663864231906881168564289536 }, { target := 24, numerator := 38663788673831486071754457088 }, { target := 31, numerator := 950302027917962248879865856 }, { target := 35, numerator := 10359970279199863559453409280 }, { target := 38, numerator := 36573219417129483595570741248 }, { target := 40, numerator := 10363490624453304487138820096 }, { target := 71, numerator := 950325639770079845475680256 }, { target := 73, numerator := 950322977522329220842258432 }, { target := 90, numerator := 950322977522329220842258432 }, { target := 92, numerator := 38663748834761187621211209728 }, { target := 95, numerator := 38663673277109130889374203904 }, { target := 102, numerator := 950299365709618120985935872 }, { target := 106, numerator := 36573219417129483595570741248 }, { target := 109, numerator := 129142007949331204904857894912 }, { target := 111, numerator := 36585115914702085572823875584 }, { target := 116, numerator := 38663864231906881168564289536 }, { target := 118, numerator := 38663748834761187621211209728 }, { target := 140, numerator := 10363490624453304487138820096 }, { target := 143, numerator := 36585115914702085572823875584 }, { target := 145, numerator := 10367019915956534598797623296 }, { target := 150, numerator := 38663788673831486071754457088 }, { target := 152, numerator := 38663673277109130889374203904 }, { target := 232, numerator := 950302027917962248879865856 }, { target := 234, numerator := 950299365709618120985935872 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8.Parent1
