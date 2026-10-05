import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent2

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
  [{ target := 0, numerator := 1156380047759738632413380608 }, { target := 2, numerator := 38457705931738913034003808256 }, { target := 5, numerator := 38457705931738913034003808256 }, { target := 12, numerator := 1156370603026772893122953216 }, { target := 16, numerator := 65941776264734370416866361344 }, { target := 19, numerator := 224653142999550483405490618368 }, { target := 21, numerator := 65931845106470045436107292672 }, { target := 26, numerator := 65941776264734370416866361344 }, { target := 28, numerator := 65941764230487913934882865152 }, { target := 44, numerator := 1156380047759738632413380608 }, { target := 50, numerator := 65941764230487913934882865152 }, { target := 53, numerator := 224653100911810935960675287040 }, { target := 55, numerator := 65931833115325289187873128448 }, { target := 60, numerator := 224653142999550483405490618368 }, { target := 62, numerator := 224653100911810935960675287040 }, { target := 64, numerator := 38457705931738913034003808256 }, { target := 71, numerator := 65931845106470045436107292672 }, { target := 73, numerator := 65931833115325289187873128448 }, { target := 75, numerator := 38457705931738913034003808256 }, { target := 104, numerator := 1156370603026772893122953216 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent2
