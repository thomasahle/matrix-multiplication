import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1078586755102585078107078656 }, { target := 21, numerator := 38516650712522289928527151104 }, { target := 24, numerator := 38525561040544188932271636480 }, { target := 31, numerator := 1087690627327638712677826560 }, { target := 35, numerator := 14078016125766027747941941248 }, { target := 38, numerator := 46506945488888380639902957568 }, { target := 40, numerator := 14083340492148794223096758272 }, { target := 71, numerator := 1078586755102585078107078656 }, { target := 73, numerator := 1079128604051315995063615488 }, { target := 90, numerator := 1079128604051315995063615488 }, { target := 92, numerator := 38535780614455998895355854848 }, { target := 95, numerator := 38544692497540449932647858176 }, { target := 102, numerator := 1088234176984207712436879360 }, { target := 106, numerator := 46506945488888380639902957568 }, { target := 109, numerator := 153745112844621951063965040640 }, { target := 111, numerator := 46524221948825259960174641152 }, { target := 116, numerator := 38516650712522289928527151104 }, { target := 118, numerator := 38535780614455998895355854848 }, { target := 140, numerator := 14083340492148794223096758272 }, { target := 143, numerator := 46524221948825259960174641152 }, { target := 145, numerator := 14088667741208839509464055808 }, { target := 150, numerator := 38525561040544188932271636480 }, { target := 152, numerator := 38544692497540449932647858176 }, { target := 232, numerator := 1087690627327638712677826560 }, { target := 234, numerator := 1088234176984207712436879360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent2
