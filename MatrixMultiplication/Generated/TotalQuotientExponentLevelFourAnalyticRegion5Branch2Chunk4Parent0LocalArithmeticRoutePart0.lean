import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2064810597217825443343761408 }, { target := 21, numerator := 77146474203350134343054917632 }, { target := 24, numerator := 77146488321940185465676103680 }, { target := 31, numerator := 2064853098798772146768183296 }, { target := 35, numerator := 15346248304490389042303598592 }, { target := 38, numerator := 54719840603535604352374800384 }, { target := 40, numerator := 15346191965482493652718583808 }, { target := 71, numerator := 2064810597217825443343761408 }, { target := 73, numerator := 2065767807484527310752710656 }, { target := 90, numerator := 1665170318333497184413024256 }, { target := 92, numerator := 57772779696289061930327343104 }, { target := 95, numerator := 57772930860232051369602711552 }, { target := 102, numerator := 1665146706360345347831627776 }, { target := 106, numerator := 54719840603535604352374800384 }, { target := 109, numerator := 195104251274734689028700897280 }, { target := 111, numerator := 54720151455105374778166345728 }, { target := 116, numerator := 77146474203350134343054917632 }, { target := 118, numerator := 77179215752078393654193946624 }, { target := 140, numerator := 15346191965482493652718583808 }, { target := 143, numerator := 54720151455105374778166345728 }, { target := 145, numerator := 15346107458114001923739746304 }, { target := 150, numerator := 77146488321940185465676103680 }, { target := 152, numerator := 77179229967687239749444042752 }, { target := 232, numerator := 2064853098798772146768183296 }, { target := 234, numerator := 2065810308500272260942135296 }]

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

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 90, numerator := 400597489151030126339686400 }, { target := 92, numerator := 19406436055789331723866603520 }, { target := 95, numerator := 19406299107455188379841331200 }, { target := 102, numerator := 400663602139926913110507520 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent0
