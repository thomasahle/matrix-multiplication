import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 25; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 88119453017677237080471633920 }, { target := 3, numerator := 299130073772598034269965647872 }, { target := 5, numerator := 88119448295310754210826420224 }, { target := 10, numerator := 39642383412382391046294732800 }, { target := 11, numerator := 9845491874941539998807097344 }, { target := 12, numerator := 39633423057327618397810196480 }, { target := 13, numerator := 9942205940510710332783591424 }, { target := 14, numerator := 88119453017677237080471633920 }, { target := 15, numerator := 9845491874941539998807097344 }, { target := 17, numerator := 9845491874941539998807097344 }, { target := 21, numerator := 39633423057327618397810196480 }, { target := 22, numerator := 9845491874941539998807097344 }, { target := 23, numerator := 39624466753946383612353970176 }, { target := 24, numerator := 9942205940510710332783591424 }, { target := 25, numerator := 299130073772598034269965647872 }, { target := 27, numerator := 88119448295310754210826420224 }, { target := 28, numerator := 9942205940510710332783591424 }, { target := 30, numerator := 9942205940510710332783591424 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent3
