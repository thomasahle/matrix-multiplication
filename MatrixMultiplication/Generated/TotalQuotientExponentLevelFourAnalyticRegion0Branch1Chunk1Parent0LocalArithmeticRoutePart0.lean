import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 615139972859805529209307136 }, { target := 37, numerator := 21830219259266434246807388160 }, { target := 40, numerator := 21833484442871074343979319296 }, { target := 47, numerator := 618545645305687827535626240 }, { target := 86, numerator := 615139972859805529209307136 }, { target := 89, numerator := 2025138068272687606736617472 }, { target := 91, numerator := 615378080555634710118662144 }, { target := 145, numerator := 2025138068272687606736617472 }, { target := 147, numerator := 71899738860269108413618716672 }, { target := 150, numerator := 71910903303328136952916475904 }, { target := 157, numerator := 2036758145785361882299760640 }, { target := 161, numerator := 21830219259266434246807388160 }, { target := 164, numerator := 71899738860269108413618716672 }, { target := 166, numerator := 21838566478375859490882846720 }, { target := 216, numerator := 615378080555634710118662144 }, { target := 218, numerator := 21838566478375859490882846720 }, { target := 221, numerator := 21841831558923503415028875264 }, { target := 228, numerator := 618783726979718361498255360 }, { target := 232, numerator := 21833484442871074343979319296 }, { target := 235, numerator := 71910903303328136952916475904 }, { target := 237, numerator := 21841831558923503415028875264 }, { target := 406, numerator := 618545645305687827535626240 }, { target := 409, numerator := 2036758145785361882299760640 }, { target := 411, numerator := 618783726979718361498255360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent0
