import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent3

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
  [{ target := 19, numerator := 963610742373376452317937664 }, { target := 21, numerator := 38650642881156809184734347264 }, { target := 24, numerator := 38650298148547393413732892672 }, { target := 31, numerator := 963766580280693241050824704 }, { target := 35, numerator := 10829730335954416533027946496 }, { target := 38, numerator := 36919043822485677695859425280 }, { target := 40, numerator := 10835176041907994002076991488 }, { target := 71, numerator := 963610742373376452317937664 }, { target := 73, numerator := 963605908751657237972254720 }, { target := 90, numerator := 963605908751657237972254720 }, { target := 92, numerator := 38650491876641809504327958528 }, { target := 95, numerator := 38650147143744726307128213504 }, { target := 102, numerator := 963761747032209845823471616 }, { target := 106, numerator := 36919043822485677695859425280 }, { target := 109, numerator := 125858670753961056214896869376 }, { target := 111, numerator := 36937591124893747763583385600 }, { target := 116, numerator := 38650642881156809184734347264 }, { target := 118, numerator := 38650491876641809504327958528 }, { target := 140, numerator := 10835176041907994002076991488 }, { target := 143, numerator := 36937591124893747763583385600 }, { target := 145, numerator := 10840626988567038703211380736 }, { target := 150, numerator := 38650298148547393413732892672 }, { target := 152, numerator := 38650147143744726307128213504 }, { target := 232, numerator := 963766580280693241050824704 }, { target := 234, numerator := 963761747032209845823471616 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent3
