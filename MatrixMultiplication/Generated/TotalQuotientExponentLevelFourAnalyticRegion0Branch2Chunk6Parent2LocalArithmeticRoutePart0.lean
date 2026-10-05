import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent2

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 3237959328867146199566647296 }, { target := 21, numerator := 115604518052107850122556080128 }, { target := 24, numerator := 115631563122966597326006648832 }, { target := 31, numerator := 3204950204265358865473732608 }, { target := 35, numerator := 40547883443785750983292747776 }, { target := 38, numerator := 145592337885964644915364233216 }, { target := 40, numerator := 40569850129072742368026820608 }, { target := 71, numerator := 3237959328867146199566647296 }, { target := 73, numerator := 3238105171080970460687499264 }, { target := 90, numerator := 3238105171080970460687499264 }, { target := 92, numerator := 115609869339604910359726522368 }, { target := 95, numerator := 115636914254440952072553627648 }, { target := 102, numerator := 3205095612252240154692943872 }, { target := 106, numerator := 145592337885964644915364233216 }, { target := 109, numerator := 522841354479024529438589059072 }, { target := 111, numerator := 145672566707094478940262105088 }, { target := 116, numerator := 115604518052107850122556080128 }, { target := 118, numerator := 115609869339604910359726522368 }, { target := 140, numerator := 40569850129072742368026820608 }, { target := 143, numerator := 145672566707094478940262105088 }, { target := 145, numerator := 40591852861155388627515080704 }, { target := 150, numerator := 115631563122966597326006648832 }, { target := 152, numerator := 115636914254440952072553627648 }, { target := 232, numerator := 3204950204265358865473732608 }, { target := 234, numerator := 3205095612252240154692943872 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent2
