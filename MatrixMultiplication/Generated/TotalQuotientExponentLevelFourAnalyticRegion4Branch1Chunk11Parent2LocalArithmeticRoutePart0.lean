import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk11Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 87; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11.Parent2

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
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 481165486667126396204089344 }, { target := 21, numerator := 19325908198422961268121927680 }, { target := 24, numerator := 19329664850364444517769150464 }, { target := 31, numerator := 477441891373776877226295296 }, { target := 35, numerator := 5356529737199411026460672000 }, { target := 38, numerator := 18420448470157975359502417920 }, { target := 40, numerator := 5357142348393774098960875520 }, { target := 71, numerator := 481165486667126396204089344 }, { target := 73, numerator := 481163077578532775088095232 }, { target := 90, numerator := 481163077578532775088095232 }, { target := 92, numerator := 19325811437898168269841367040 }, { target := 95, numerator := 19329568071030930625729134592 }, { target := 102, numerator := 477439500928396863563890688 }, { target := 106, numerator := 18420448470157975359502417920 }, { target := 109, numerator := 63341781993763260042525540352 }, { target := 111, numerator := 18422538351834144324271996928 }, { target := 116, numerator := 19325908198422961268121927680 }, { target := 118, numerator := 19325811437898168269841367040 }, { target := 140, numerator := 5357142348393774098960875520 }, { target := 143, numerator := 18422538351834144324271996928 }, { target := 145, numerator := 5357754956794216552631107584 }, { target := 150, numerator := 19329664850364444517769150464 }, { target := 152, numerator := 19329568071030930625729134592 }, { target := 232, numerator := 477441891373776877226295296 }, { target := 234, numerator := 477439500928396863563890688 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk11.Parent2
