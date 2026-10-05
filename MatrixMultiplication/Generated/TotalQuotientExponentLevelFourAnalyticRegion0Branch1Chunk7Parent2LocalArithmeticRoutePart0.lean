import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent2

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1120508951955860807370145792 }, { target := 2, numerator := 38493591194642239467982684160 }, { target := 5, numerator := 38493534526244445032240119808 }, { target := 12, numerator := 1120527841421792285951000576 }, { target := 16, numerator := 43970484900115158104570593280 }, { target := 19, numerator := 149626582407421288883993706496 }, { target := 21, numerator := 43997156922302995393452965888 }, { target := 26, numerator := 43970484900115158104570593280 }, { target := 28, numerator := 44003698679816042949837324288 }, { target := 44, numerator := 1120508951955860807370145792 }, { target := 50, numerator := 44003698679816042949837324288 }, { target := 53, numerator := 149740662777045907577539395584 }, { target := 55, numerator := 44030389398884632651869716480 }, { target := 60, numerator := 149626582407421288883993706496 }, { target := 62, numerator := 149740662777045907577539395584 }, { target := 64, numerator := 38493591194642239467982684160 }, { target := 71, numerator := 43997156922302995393452965888 }, { target := 73, numerator := 44030389398884632651869716480 }, { target := 75, numerator := 38493534526244445032240119808 }, { target := 104, numerator := 1120527841421792285951000576 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent2
