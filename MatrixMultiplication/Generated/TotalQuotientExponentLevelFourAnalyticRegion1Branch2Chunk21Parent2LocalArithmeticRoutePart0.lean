import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 88; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
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
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 6961550890215460825724912402432 }, { target := 1, numerator := 20658124405574783337379135488 }, { target := 2, numerator := 1160568786830044007717928960 }, { target := 3, numerator := 25236307859441975584110701182976 }, { target := 4, numerator := 31374042870638856341974679552 }, { target := 5, numerator := 6961550342420948812846067613696 }, { target := 6, numerator := 31374042870638856341974679552 }, { target := 7, numerator := 31374042870638856341974679552 }, { target := 8, numerator := 20658124405574783337379135488 }, { target := 9, numerator := 1160568786830044007717928960 }, { target := 10, numerator := 23857024827079306629748304642048 }, { target := 11, numerator := 10464461894584230136256659456 }, { target := 12, numerator := 23857019538028845815745665302528 }, { target := 13, numerator := 10464461894584230136256659456 }, { target := 14, numerator := 8292884179735592671389807542272 }, { target := 19, numerator := 20658124405574783337379135488 }, { target := 20, numerator := 1160568786830044007717928960 }, { target := 21, numerator := 23104351909140737916953383927808 }, { target := 22, numerator := 10464461894584230136256659456 }, { target := 23, numerator := 23104346620090277102950744588288 }, { target := 24, numerator := 10464461894584230136256659456 }, { target := 25, numerator := 29783404073922133096663055597568 }, { target := 26, numerator := 31374042870638856341974679552 }, { target := 27, numerator := 8292883627218714175641317539840 }, { target := 32, numerator := 31374042870638856341974679552 }, { target := 33, numerator := 31374042870638856341974679552 }, { target := 34, numerator := 20658124405574783337379135488 }, { target := 35, numerator := 1160568786830044007717928960 }]

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
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot16.Left0.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1430243434953762913712275980288 }, { target := 3, numerator := 4903873061212745739612400386048 }, { target := 5, numerator := 1430243430231396430842630766592 }, { target := 10, numerator := 9342578733981854262129328128 }, { target := 12, numerator := 9342578733981854262129328128 }, { target := 15, numerator := 10464461894584230136256659456 }, { target := 17, numerator := 10464461894584230136256659456 }, { target := 21, numerator := 762010122619493061400796856320 }, { target := 23, numerator := 762010122619493061400796856320 }, { target := 28, numerator := 10464461894584230136256659456 }, { target := 30, numerator := 10464461894584230136256659456 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent2
