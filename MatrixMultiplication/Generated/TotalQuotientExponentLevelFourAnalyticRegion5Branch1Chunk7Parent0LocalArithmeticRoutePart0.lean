import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 113619893775477836139724800 }, { target := 17, numerator := 3113229951833415529822945280 }, { target := 19, numerator := 33160308369208564837441863680 }, { target := 27, numerator := 3121607411997908367782707200 }, { target := 34, numerator := 105230627720110571970887680 }, { target := 35, numerator := 1013942617763732434439897088 }, { target := 37, numerator := 35017287182598740530088116224 }, { target := 40, numerator := 35017356158162254766373076992 }, { target := 47, numerator := 1013966269062316217220464640 }, { target := 86, numerator := 829703332021461514362814464 }, { target := 89, numerator := 2923640818787261360457646080 }, { target := 91, numerator := 828980554011423010063384576 }, { target := 122, numerator := 113619893775477836139724800 }, { target := 124, numerator := 113620381380209491543326720 }, { target := 126, numerator := 113620381380209491543326720 }, { target := 127, numerator := 3113243312395591771951726592 }, { target := 129, numerator := 33160450678118797845412708352 }, { target := 137, numerator := 3121620808512320435210158080 }, { target := 144, numerator := 105231079321940906267901952 }, { target := 145, numerator := 3550491384381645727188647936 }, { target := 147, numerator := 122485619453593959956234633216 }, { target := 150, numerator := 122485859332405777894349996032 }, { target := 157, numerator := 3550576348754035543495409664 }, { target := 161, numerator := 27869774030914522796317999104 }, { target := 164, numerator := 98157867813449934760480604160 }, { target := 166, numerator := 27846245142548482873920323584 }, { target := 197, numerator := 3113229951833415529822945280 }, { target := 199, numerator := 3113243312395591771951726592 }, { target := 216, numerator := 383665416301210715717369856 }, { target := 218, numerator := 14239712282149492454647136256 }, { target := 221, numerator := 14239750633524896847617851392 }, { target := 228, numerator := 383658443323864462449967104 }, { target := 232, numerator := 27869775970757027168029507584 }, { target := 235, numerator := 98157878158064874968202608640 }, { target := 237, numerator := 27846247025190486903422451712 }, { target := 242, numerator := 33160308369208564837441863680 }, { target := 244, numerator := 33160450678118797845412708352 }, { target := 406, numerator := 829741779307493896652587008 }, { target := 409, numerator := 2923776466899822660298997760 }, { target := 411, numerator := 829018965104558461966876672 }, { target := 416, numerator := 3121607411997908367782707200 }, { target := 418, numerator := 3121620808512320435210158080 }, { target := 498, numerator := 105230627720110571970887680 }, { target := 500, numerator := 105231079321940906267901952 }]

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
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 199425387171141403822522368 }, { target := 37, numerator := 7092171539684575192308252672 }, { target := 40, numerator := 7092142855264660326853902336 }, { target := 47, numerator := 199433210194754548946436096 }, { target := 86, numerator := 383664672913412323899604992 }, { target := 89, numerator := 1311332855016040172676448256 }, { target := 91, numerator := 383665416301210715717369856 }, { target := 145, numerator := 684482289421655805945446400 }, { target := 147, numerator := 24342265953774672151157145600 }, { target := 150, numerator := 24342167501026541293063372800 }, { target := 157, numerator := 684509140171146039971020800 }, { target := 161, numerator := 14239684691368792926078369792 }, { target := 164, numerator := 48670017593918697346911174656 }, { target := 166, numerator := 14239712282149492454647136256 }, { target := 216, numerator := 828980554011423010063384576 }, { target := 218, numerator := 27846245142548482873920323584 }, { target := 221, numerator := 27846247025190486903422451712 }, { target := 228, numerator := 829018965104558461966876672 }, { target := 232, numerator := 14239723042669887925197471744 }, { target := 235, numerator := 48670148675367444219210760192 }, { target := 237, numerator := 14239750633524896847617851392 }, { target := 406, numerator := 383657699949576869514313728 }, { target := 409, numerator := 1311309022025358923167432704 }, { target := 411, numerator := 383658443323864462449967104 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent0
