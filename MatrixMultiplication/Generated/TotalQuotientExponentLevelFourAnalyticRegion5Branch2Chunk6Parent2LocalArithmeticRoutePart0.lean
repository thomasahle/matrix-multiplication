import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent2

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
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
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
  [{ target := 26, numerator := 44806428708250215535083520 }, { target := 27, numerator := 1134129704723175870115610624 }, { target := 29, numerator := 12103891517580050702683602944 }, { target := 37, numerator := 1135197612103564867269558272 }, { target := 44, numerator := 42437036142722085449367552 }, { target := 80, numerator := 44747784893736476504752128 }, { target := 82, numerator := 1855903628559832234401464320 }, { target := 85, numerator := 1855899014622013993328312320 }, { target := 92, numerator := 44746806509235428401348608 }, { target := 131, numerator := 44806428708250215535083520 }, { target := 134, numerator := 155820600169194232699944960 }, { target := 136, numerator := 44865192734534058198958080 }, { target := 157, numerator := 155820600169194232699944960 }, { target := 158, numerator := 3944094103334253834799153152 }, { target := 160, numerator := 42092969581056269609978560512 }, { target := 168, numerator := 3947807900075806814587846656 }, { target := 175, numerator := 147580707318081124193796096 }, { target := 176, numerator := 1855903628559832234401464320 }, { target := 178, numerator := 75471805811562152380042575872 }, { target := 181, numerator := 75471659310069756367875342336 }, { target := 188, numerator := 1855857383144396597231616000 }, { target := 227, numerator := 1134129704723175870115610624 }, { target := 230, numerator := 3944094103334253834799153152 }, { target := 232, numerator := 1135617125829901295913271296 }, { target := 267, numerator := 44865192734534058198958080 }, { target := 268, numerator := 1135617125829901295913271296 }, { target := 270, numerator := 12119765878018531430630424576 }, { target := 278, numerator := 1136686433780234809390399488 }, { target := 285, numerator := 42492692689766642098372608 }, { target := 286, numerator := 1855899014622013993328312320 }, { target := 288, numerator := 75471659310069756367875342336 }, { target := 291, numerator := 75471512807712669227252973568 }, { target := 298, numerator := 1855852769476794333800693760 }, { target := 302, numerator := 12103891517580050702683602944 }, { target := 305, numerator := 42092969581056269609978560512 }, { target := 307, numerator := 12119765878018531430630424576 }, { target := 573, numerator := 44746806509235428401348608 }, { target := 575, numerator := 1855857383144396597231616000 }, { target := 578, numerator := 1855852769476794333800693760 }, { target := 585, numerator := 44745828124734380297945088 }, { target := 589, numerator := 1135197612103564867269558272 }, { target := 592, numerator := 3947807900075806814587846656 }, { target := 594, numerator := 1136686433780234809390399488 }, { target := 763, numerator := 42437036142722085449367552 }, { target := 766, numerator := 147580707318081124193796096 }, { target := 768, numerator := 42492692689766642098372608 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6.Parent2
