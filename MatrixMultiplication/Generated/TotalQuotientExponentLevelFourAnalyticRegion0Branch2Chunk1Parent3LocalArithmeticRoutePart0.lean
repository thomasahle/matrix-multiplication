import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent3

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
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 446075372167640313292128256 }, { target := 37, numerator := 20982630242346083311551512576 }, { target := 40, numerator := 20985940655729007780087988224 }, { target := 47, numerator := 442775176790241203187613696 }, { target := 86, numerator := 446075372167640313292128256 }, { target := 89, numerator := 1581010574837379159470112768 }, { target := 91, numerator := 446069326105125291747704832 }, { target := 145, numerator := 1581010574837379159470112768 }, { target := 147, numerator := 74403994333860453977168019456 }, { target := 150, numerator := 74415701121725509931005640704 }, { target := 157, numerator := 1569340019454768416592756736 }, { target := 161, numerator := 20982630242346083311551512576 }, { target := 164, numerator := 74403994333860453977168019456 }, { target := 166, numerator := 20982435587880927119215165440 }, { target := 216, numerator := 446069326105125291747704832 }, { target := 218, numerator := 20982435587880927119215165440 }, { target := 221, numerator := 20985745890952963789915422720 }, { target := 228, numerator := 442769240942912487397785600 }, { target := 232, numerator := 20985940655729007780087988224 }, { target := 235, numerator := 74415701121725509931005640704 }, { target := 237, numerator := 20985745890952963789915422720 }, { target := 406, numerator := 442775176790241203187613696 }, { target := 409, numerator := 1569340019454768416592756736 }, { target := 411, numerator := 442769240942912487397785600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent3
