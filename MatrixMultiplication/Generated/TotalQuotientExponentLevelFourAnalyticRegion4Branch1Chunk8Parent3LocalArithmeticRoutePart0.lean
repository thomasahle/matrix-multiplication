import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 3853275233110538775827578880 }, { target := 21, numerator := 134795891107556842607759851520 }, { target := 24, numerator := 134803404416813729362414141440 }, { target := 31, numerator := 3845804425418273175948492800 }, { target := 35, numerator := 51036934868744828303641149440 }, { target := 38, numerator := 175362220989615695994724286464 }, { target := 40, numerator := 51042538424927470486175088640 }, { target := 71, numerator := 4377404917594905404954902528 }, { target := 73, numerator := 4377409194463061335296966656 }, { target := 90, numerator := 3853282134179472728823693312 }, { target := 92, numerator := 134796077823779981638185779200 }, { target := 95, numerator := 134803591084671586094601469952 }, { target := 102, numerator := 3845811374319938771246645248 }, { target := 106, numerator := 174845369621135035674201686016 }, { target := 109, numerator := 600741533113655505913808683008 }, { target := 111, numerator := 174864475348735047984369106944 }, { target := 116, numerator := 154078851636486630508293259264 }, { target := 118, numerator := 154078941807214407298823749632 }, { target := 140, numerator := 51036996890706607783513423872 }, { target := 143, numerator := 175362418036124728593462853632 }, { target := 145, numerator := 51042600477377493543438778368 }, { target := 150, numerator := 115427028844478853085113876480 }, { target := 152, numerator := 115427367827878271472883466240 }, { target := 232, numerator := 3415028393468320077003620352 }, { target := 234, numerator := 3415038865135153797404819456 }]

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
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 524129684484366629127323648 }, { target := 21, numerator := 19282960528929787900533407744 }, { target := 24, numerator := 19282981779632159584535183360 }, { target := 31, numerator := 524108433781994945125548032 }, { target := 35, numerator := 2801543767948800519726694400 }, { target := 38, numerator := 9041914480396790099922124800 }, { target := 40, numerator := 2795995907712381283939123200 }, { target := 90, numerator := 524127060283588606473273344 }, { target := 92, numerator := 19282863983434425660637970432 }, { target := 95, numerator := 19282885234030399803443118080 }, { target := 102, numerator := 524105809687614463668125696 }, { target := 106, numerator := 9558765848877450420444725248 }, { target := 109, numerator := 30850684659111445079173103616 }, { target := 111, numerator := 9539836750724878374266732544 }, { target := 140, numerator := 2801537441933243986600787968 }, { target := 143, numerator := 9041894063335197765172985856 }, { target := 145, numerator := 2795989594224150064297672704 }, { target := 150, numerator := 38659357351967035861835448320 }, { target := 152, numerator := 38659108490823714425161121792 }, { target := 232, numerator := 954884465731948044070420480 }, { target := 234, numerator := 954878318872399437509951488 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent3
