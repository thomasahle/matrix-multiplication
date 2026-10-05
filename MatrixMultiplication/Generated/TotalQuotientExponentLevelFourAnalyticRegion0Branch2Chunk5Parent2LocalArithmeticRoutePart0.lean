import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 546497169356896457457664 }, { target := 72, numerator := 14880801778501190082887680 }, { target := 74, numerator := 177227110854760396780208128 }, { target := 82, numerator := 14880888596924481694334976 }, { target := 89, numerator := 546335935142212036198400 }, { target := 146, numerator := 14880801778501190082887680 }, { target := 147, numerator := 405195624035211240118681600 }, { target := 149, numerator := 4825791704483355006714511360 }, { target := 157, numerator := 405197988050653890603909120 }, { target := 164, numerator := 14876411464107696324608000 }, { target := 242, numerator := 177227110854760396780208128 }, { target := 243, numerator := 4825791704483355006714511360 }, { target := 245, numerator := 57474129022273521447501561856 }, { target := 253, numerator := 4825819859392825159059505152 }, { target := 260, numerator := 177174823165744399568076800 }, { target := 640, numerator := 14880888596924481694334976 }, { target := 641, numerator := 405197988050653890603909120 }, { target := 643, numerator := 4825819859392825159059505152 }, { target := 651, numerator := 405200352079888814947958784 }, { target := 658, numerator := 14876498256916765055385600 }, { target := 1017, numerator := 546335935142212036198400 }, { target := 1018, numerator := 14876411464107696324608000 }, { target := 1020, numerator := 177174823165744399568076800 }, { target := 1028, numerator := 14876498256916765055385600 }, { target := 1035, numerator := 546174748496798679040000 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent2
