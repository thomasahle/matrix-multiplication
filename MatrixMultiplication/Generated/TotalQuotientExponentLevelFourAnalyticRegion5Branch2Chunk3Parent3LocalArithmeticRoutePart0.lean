import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 584538988595656820162297856 }, { target := 37, numerator := 20857755037293874406158761984 }, { target := 40, numerator := 20857795935238695295031181312 }, { target := 47, numerator := 584513427380143764617035776 }, { target := 86, numerator := 1736982546026481072824385536 }, { target := 89, numerator := 6191031325490923411890765824 }, { target := 91, numerator := 1736597200030779493471748096 }, { target := 122, numerator := 239258873984179551724371968 }, { target := 124, numerator := 239367136154107599619358720 }, { target := 145, numerator := 2069892860357616705642430464 }, { target := 147, numerator := 73858748649950170024557674496 }, { target := 150, numerator := 73858893472392538561947107328 }, { target := 157, numerator := 2069802346331136369774034944 }, { target := 161, numerator := 62375236098710616536829132800 }, { target := 164, numerator := 222120697911990918084992958464 }, { target := 166, numerator := 62365931224149725610097246208 }, { target := 197, numerator := 6146454252871474338477375488 }, { target := 199, numerator := 6148949407351526031097856000 }, { target := 216, numerator := 585328787153515094470557696 }, { target := 218, numerator := 20885936946747327512517279744 }, { target := 221, numerator := 20885977899951315829225684992 }, { target := 228, numerator := 585303191401022396527804416 }, { target := 232, numerator := 41517532464479445922191769600 }, { target := 235, numerator := 148262139445943276373782036480 }, { target := 237, numerator := 41480045477159103910715064320 }, { target := 242, numerator := 66447364029282976555513937920 }, { target := 244, numerator := 66475540994620019489898496000 }, { target := 406, numerator := 1152467690930946037908504576 }, { target := 409, numerator := 4121222392743285304661639168 }, { target := 411, numerator := 1151292578028684365407453184 }, { target := 416, numerator := 6141082412050222590975803392 }, { target := 418, numerator := 6143573142057766466093056000 }, { target := 498, numerator := 237314102925023230667259904 }, { target := 500, numerator := 237420677231379333020385280 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 239258873984179551724371968 }, { target := 17, numerator := 6146454252871474338477375488 }, { target := 19, numerator := 66447364029282976555513937920 }, { target := 27, numerator := 6141082412050222590975803392 }, { target := 34, numerator := 237314102925023230667259904 }, { target := 35, numerator := 1152443557430824252662087680 }, { target := 37, numerator := 41517481061416742130670370816 }, { target := 40, numerator := 41517532464479445922191769600 }, { target := 47, numerator := 1152467690930946037908504576 }, { target := 126, numerator := 239367136154107599619358720 }, { target := 127, numerator := 6148949407351526031097856000 }, { target := 129, numerator := 66475540994620019489898496000 }, { target := 137, numerator := 6143573142057766466093056000 }, { target := 144, numerator := 237420677231379333020385280 }, { target := 145, numerator := 4121138465133306706248335360 }, { target := 147, numerator := 148261949262040748060435283968 }, { target := 150, numerator := 148262139445943276373782036480 }, { target := 157, numerator := 4121222392743285304661639168 }, { target := 216, numerator := 1151268412877264399001190400 }, { target := 218, numerator := 41479994277402398097579966464 }, { target := 221, numerator := 41480045477159103910715064320 }, { target := 228, numerator := 1151292578028684365407453184 }, { target := 232, numerator := 20857795935238695295031181312 }, { target := 235, numerator := 73858893472392538561947107328 }, { target := 237, numerator := 20885977899951315829225684992 }, { target := 406, numerator := 584513427380143764617035776 }, { target := 409, numerator := 2069802346331136369774034944 }, { target := 411, numerator := 585303191401022396527804416 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent3
