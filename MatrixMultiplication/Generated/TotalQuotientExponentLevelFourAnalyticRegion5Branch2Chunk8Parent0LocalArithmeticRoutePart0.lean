import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8.Parent0

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
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 343348004120570057266823168 }, { target := 37, numerator := 13986832905865691116387434496 }, { target := 40, numerator := 13986805076196052953578078208 }, { target := 47, numerator := 343339540342534853401509888 }, { target := 86, numerator := 343348004120570057266823168 }, { target := 89, numerator := 1213752416084342292139212800 }, { target := 91, numerator := 343548197087496716911902720 }, { target := 145, numerator := 1213752416084342292139212800 }, { target := 147, numerator := 49344527960297300240013197312 }, { target := 150, numerator := 49344432557907284269157318656 }, { target := 157, numerator := 1213722120138839489909882880 }, { target := 161, numerator := 13986832905865691116387434496 }, { target := 164, numerator := 49344527960297300240013197312 }, { target := 166, numerator := 13996252200505077433374867456 }, { target := 216, numerator := 343548197087496716911902720 }, { target := 218, numerator := 13996252200505077433374867456 }, { target := 221, numerator := 13996224316837279738393264128 }, { target := 228, numerator := 343539733146206026554408960 }, { target := 232, numerator := 13986805076196052953578078208 }, { target := 235, numerator := 49344432557907284269157318656 }, { target := 237, numerator := 13996224316837279738393264128 }, { target := 406, numerator := 343339540342534853401509888 }, { target := 409, numerator := 1213722120138839489909882880 }, { target := 411, numerator := 343539733146206026554408960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8.Parent0
