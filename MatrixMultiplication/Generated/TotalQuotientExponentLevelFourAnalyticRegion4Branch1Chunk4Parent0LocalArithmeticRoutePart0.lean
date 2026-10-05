import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10001703898637008803725312 }, { target := 30, numerator := 514124231727475302246383616 }, { target := 35, numerator := 514243757824817143608246272 }, { target := 43, numerator := 9887051317025780942241792 }, { target := 71, numerator := 1757751102280896673218560 }, { target := 72, numerator := 73997946377362013566271488 }, { target := 74, numerator := 821716139968714773048066048 }, { target := 82, numerator := 73998451171770496689635328 }, { target := 89, numerator := 1757497467994132468203520 }, { target := 104, numerator := 367967064657283654810075136 }, { target := 105, numerator := 18914855542136272474444136448 }, { target := 110, numerator := 18919252959579795448729174016 }, { target := 118, numerator := 363748945990861983187992576 }, { target := 146, numerator := 27628265363940073726279680 }, { target := 147, numerator := 938985769524301366692937728 }, { target := 149, numerator := 10339076968406222145918599168 }, { target := 157, numerator := 939000399265028896517521408 }, { target := 164, numerator := 27624607928758191270133760 }, { target := 200, numerator := 9711137656510642477072384 }, { target := 202, numerator := 322963092436819712764018688 }, { target := 205, numerator := 322963092436819712764018688 }, { target := 212, numerator := 9711058340802855088160768 }, { target := 226, numerator := 367967470173779002224803840 }, { target := 227, numerator := 18914876387170152323607429120 }, { target := 232, numerator := 18919273809459829971919831040 }, { target := 240, numerator := 363749346858798090226237440 }, { target := 242, numerator := 299839701413725364771880960 }, { target := 243, numerator := 10190477362844919190379298816 }, { target := 245, numerator := 112206311553189213499604074496 }, { target := 253, numerator := 10190636134198593389672267776 }, { target := 260, numerator := 299800008575306814948638720 }, { target := 296, numerator := 568478886223358673729617920 }, { target := 298, numerator := 18905889873432636804237885440 }, { target := 301, numerator := 18905889873432636804237885440 }, { target := 308, numerator := 568474243172583591473315840 }, { target := 624, numerator := 10001298382141661388996608 }, { target := 625, numerator := 514103386693595453083090944 }, { target := 630, numerator := 514222907944782620417589248 }, { target := 638, numerator := 9886650449089673903996928 }, { target := 640, numerator := 27628222838700592280371200 }, { target := 641, numerator := 938984324243745649742315520 }, { target := 643, numerator := 10339061054568769562733445120 }, { target := 651, numerator := 938998953961955181430046720 }, { target := 658, numerator := 27624565409148209358438400 }, { target := 659, numerator := 568667604576318197191409664 }, { target := 661, numerator := 18912166075565404311307419648 }, { target := 664, numerator := 18912166075565404311307419648 }, { target := 671, numerator := 568662959984186142467555328 }, { target := 1017, numerator := 815591568014651078737920 }, { target := 1018, numerator := 27719035778095395983327232 }, { target := 1020, numerator := 305211488503092908069486592 }, { target := 1028, numerator := 27719467650781662677041152 }, { target := 1035, numerator := 815483599843084405309440 }, { target := 1036, numerator := 9522419303551119015280640 }, { target := 1038, numerator := 316686890304052205694484480 }, { target := 1041, numerator := 316686890304052205694484480 }, { target := 1048, numerator := 9522341529200304093921280 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 9711137656510642477072384 }, { target := 30, numerator := 568478886223358673729617920 }, { target := 35, numerator := 568667604576318197191409664 }, { target := 43, numerator := 9522419303551119015280640 }, { target := 71, numerator := 815782931592317585326080 }, { target := 72, numerator := 27628265363940073726279680 }, { target := 74, numerator := 299839701413725364771880960 }, { target := 82, numerator := 27628222838700592280371200 }, { target := 89, numerator := 815591568014651078737920 }, { target := 104, numerator := 322963092436819712764018688 }, { target := 105, numerator := 18905889873432636804237885440 }, { target := 110, numerator := 18912166075565404311307419648 }, { target := 118, numerator := 316686890304052205694484480 }, { target := 146, numerator := 73997946377362013566271488 }, { target := 147, numerator := 3212030338431558437839044608 }, { target := 149, numerator := 35559274777949265263880830976 }, { target := 157, numerator := 3212032470315150744999690240 }, { target := 164, numerator := 73984288286565239065935872 }, { target := 200, numerator := 10001703898637008803725312 }, { target := 202, numerator := 367967064657283654810075136 }, { target := 205, numerator := 367967470173779002224803840 }, { target := 212, numerator := 10001298382141661388996608 }, { target := 226, numerator := 322963092436819712764018688 }, { target := 227, numerator := 18905889873432636804237885440 }, { target := 232, numerator := 18912166075565404311307419648 }, { target := 240, numerator := 316686890304052205694484480 }, { target := 242, numerator := 516433039197085240645386240 }, { target := 243, numerator := 25368797415104346073501532160 }, { target := 245, numerator := 283133859798445339872193413120 }, { target := 253, numerator := 25368837338805725771637719040 }, { target := 260, numerator := 516353191794325844373012480 }, { target := 296, numerator := 514124231727475302246383616 }, { target := 298, numerator := 18914855542136272474444136448 }, { target := 301, numerator := 18914876387170152323607429120 }, { target := 308, numerator := 514103386693595453083090944 }, { target := 624, numerator := 9711058340802855088160768 }, { target := 625, numerator := 568474243172583591473315840 }, { target := 630, numerator := 568662959984186142467555328 }, { target := 638, numerator := 9522341529200304093921280 }, { target := 640, numerator := 46272479657157116118958080 }, { target := 641, numerator := 2273048146071405095257374720 }, { target := 643, numerator := 25368837338805725771637719040 }, { target := 651, numerator := 2273051723241182618902855680 }, { target := 658, numerator := 46265325317602068827996160 }, { target := 659, numerator := 514243757824817143608246272 }, { target := 661, numerator := 18919252959579795448729174016 }, { target := 664, numerator := 18919273809459829971919831040 }, { target := 671, numerator := 514222907944782620417589248 }, { target := 1017, numerator := 941822529906129460264960 }, { target := 1018, numerator := 46265252508469843082608640 }, { target := 1020, numerator := 516353191794325844373012480 }, { target := 1028, numerator := 46265325317602068827996160 }, { target := 1035, numerator := 941676911641677969489920 }, { target := 1036, numerator := 9887051317025780942241792 }, { target := 1038, numerator := 363748945990861983187992576 }, { target := 1041, numerator := 363749346858798090226237440 }, { target := 1048, numerator := 9886650449089673903996928 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 305283100771629532402679808 }, { target := 243, numerator := 10339076968406222145918599168 }, { target := 245, numerator := 112206311553189213499604074496 }, { target := 253, numerator := 10339061054568769562733445120 }, { target := 260, numerator := 305211488503092908069486592 }, { target := 640, numerator := 27725971514613380570677248 }, { target := 641, numerator := 939000399265028896517521408 }, { target := 643, numerator := 10190636134198593389672267776 }, { target := 651, numerator := 938998953961955181430046720 }, { target := 658, numerator := 27719467650781662677041152 }, { target := 1017, numerator := 815674938088003007938560 }, { target := 1018, numerator := 27624607928758191270133760 }, { target := 1020, numerator := 299800008575306814948638720 }, { target := 1028, numerator := 27624565409148209358438400 }, { target := 1035, numerator := 815483599843084405309440 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4.Parent0
