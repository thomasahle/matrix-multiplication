import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
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
    Slot15.Left5.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 80264084653249257887760384 }, { target := 17, numerator := 2805025869485949096686518272 }, { target := 19, numerator := 33843621768872574290592006144 }, { target := 27, numerator := 2805091982931961245635444736 }, { target := 34, numerator := 80266445847749691778793472 }, { target := 35, numerator := 641890335700496658410242048 }, { target := 37, numerator := 27651981849905936278669492224 }, { target := 40, numerator := 27651948518597053548532334592 }, { target := 47, numerator := 641843512841116624166584320 }, { target := 86, numerator := 641890335700496658410242048 }, { target := 89, numerator := 2320860774584815498616111104 }, { target := 91, numerator := 641788724790742207780880384 }, { target := 122, numerator := 80264084653249257887760384 }, { target := 124, numerator := 80263319198938591861407744 }, { target := 145, numerator := 2320860774584815498616111104 }, { target := 147, numerator := 99552770462563832515182723072 }, { target := 150, numerator := 99552652945160589098725933056 }, { target := 157, numerator := 2320694680116375466555736064 }, { target := 161, numerator := 27651981849905936278669492224 }, { target := 164, numerator := 99552770462563832515182723072 }, { target := 166, numerator := 27647254832207546901753495552 }, { target := 197, numerator := 2805025869485949096686518272 }, { target := 199, numerator := 2804999118802220458182705152 }, { target := 216, numerator := 641788724790742207780880384 }, { target := 218, numerator := 27647254832207546901753495552 }, { target := 221, numerator := 27647221508626841132184109056 }, { target := 228, numerator := 641741911962004443598159872 }, { target := 232, numerator := 27651948518597053548532334592 }, { target := 235, numerator := 99552652945160589098725933056 }, { target := 237, numerator := 27647221508626841132184109056 }, { target := 242, numerator := 33843621768872574290592006144 }, { target := 244, numerator := 33843299012483045274003963904 }, { target := 406, numerator := 641843512841116624166584320 }, { target := 409, numerator := 2320694680116375466555736064 }, { target := 411, numerator := 641741911962004443598159872 }, { target := 416, numerator := 2805091982931961245635444736 }, { target := 418, numerator := 2805065231617728659299762176 }, { target := 498, numerator := 80266445847749691778793472 }, { target := 500, numerator := 80265680370921027615588352 }]

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
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 126, numerator := 80263319198938591861407744 }, { target := 127, numerator := 2804999118802220458182705152 }, { target := 129, numerator := 33843299012483045274003963904 }, { target := 137, numerator := 2805065231617728659299762176 }, { target := 144, numerator := 80265680370921027615588352 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10.Parent0
