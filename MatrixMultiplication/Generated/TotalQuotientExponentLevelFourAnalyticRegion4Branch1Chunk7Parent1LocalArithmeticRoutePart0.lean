import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 178364356148719499241062400 }, { target := 17, numerator := 6061965527253331041362903040 }, { target := 19, numerator := 66747686919525073697363722240 }, { target := 27, numerator := 6062059974886981409114685440 }, { target := 34, numerator := 178340744240306907303116800 }, { target := 35, numerator := 552480761196804398716551168 }, { target := 37, numerator := 22190270848895768392064040960 }, { target := 40, numerator := 22194584287788815907771383808 }, { target := 47, numerator := 548205278397096081764646912 }, { target := 86, numerator := 1928678395737887873716715520 }, { target := 89, numerator := 6673485854142301746084446208 }, { target := 91, numerator := 1929076629138300169422372864 }, { target := 122, numerator := 273849844051739805116006400 }, { target := 124, numerator := 273850220631481646768455680 }, { target := 145, numerator := 1783118240720386077549920256 }, { target := 147, numerator := 71618560312359986334604984320 }, { target := 150, numerator := 71632481831642874014267867136 }, { target := 157, numerator := 1769319223807052406381871104 }, { target := 161, numerator := 70617054461546164113700290560 }, { target := 164, numerator := 244360848599578002243362750464 }, { target := 166, numerator := 70631706410110894778594885632 }, { target := 197, numerator := 12070294630228774076542877696 }, { target := 199, numerator := 12070320048672297645095518208 }, { target := 216, numerator := 551386690819787037610082304 }, { target := 218, numerator := 22146327747707633887220858880 }, { target := 221, numerator := 22150632644754435508455604224 }, { target := 228, numerator := 547119674702372734224039936 }, { target := 232, numerator := 70616744869383822634070835200 }, { target := 235, numerator := 244359796049145831606615801856 }, { target := 237, numerator := 70631396834970471040565641216 }, { target := 242, numerator := 133767906214922301080801902592 }, { target := 244, numerator := 133768194635196671730296815616 }, { target := 406, numerator := 1928974026628794514124308480 }, { target := 409, numerator := 6674490769222090949560107008 }, { target := 411, numerator := 1929372243038814265621348352 }, { target := 416, numerator := 12070304074917829719466442752 }, { target := 418, numerator := 12070329493449173480752807936 }, { target := 498, numerator := 273800259214647197932978176 }, { target := 500, numerator := 273800635772433991401996288 }]

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
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 183258099841250905546555392 }, { target := 17, numerator := 9002207946992829454853603328 }, { target := 19, numerator := 100471056669906182561329053696 }, { target := 27, numerator := 9002222114060189916444229632 }, { target := 34, numerator := 183229765706529982365302784 }, { target := 35, numerator := 4932829426146416705415413760 }, { target := 37, numerator := 170149723824468014995750256640 }, { target := 40, numerator := 170149793804372808207465185280 }, { target := 47, numerator := 4932733254401128366300200960 }, { target := 86, numerator := 3759318039978470343608107008 }, { target := 89, numerator := 12715139230131485768832516096 }, { target := 91, numerator := 3758229139023100887636639744 }, { target := 122, numerator := 178364356148719499241062400 }, { target := 124, numerator := 178363207967253500201533440 }, { target := 126, numerator := 361622137960964368625565696 }, { target := 127, numerator := 15064175231342443613418160128 }, { target := 129, numerator := 167218769046015765071446147072 }, { target := 137, numerator := 15064283845499644787755581440 }, { target := 144, numerator := 361570191941474751550062592 }, { target := 145, numerator := 16913948706517848563128467456 }, { target := 147, numerator := 583643721999894768363742691328 }, { target := 150, numerator := 583643964535605467944058880000 }, { target := 157, numerator := 16913616883535874394763034624 }, { target := 161, numerator := 106649717173213417140262010880 }, { target := 164, numerator := 363565982710314290899719290880 }, { target := 166, numerator := 106649889092555987470075822080 }, { target := 197, numerator := 6061965527253331041362903040 }, { target := 199, numerator := 6061926504678326683696103424 }, { target := 216, numerator := 4933233286643411338062200832 }, { target := 218, numerator := 170164563762998834201106579456 }, { target := 221, numerator := 170164633759068453850337771520 }, { target := 228, numerator := 4933137098691075314924126208 }, { target := 232, numerator := 106649717173213417140262010880 }, { target := 235, numerator := 363565982710314290899719290880 }, { target := 237, numerator := 106649889092555987470075822080 }, { target := 242, numerator := 66747686919525073697363722240 }, { target := 244, numerator := 66747257245913853951364562944 }, { target := 406, numerator := 3206811086941170817491271680 }, { target := 409, numerator := 10931931702139825103233351680 }, { target := 411, numerator := 3206816256320597476119674880 }, { target := 416, numerator := 6062059974886981409114685440 }, { target := 418, numerator := 6062020951703991101752868864 }, { target := 498, numerator := 178340744240306907303116800 }, { target := 500, numerator := 178339596210837395687342080 }]

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
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 90591744210488899569451008 }, { target := 17, numerator := 3068086683235944621689274368 }, { target := 19, numerator := 33296849545016118519472848896 }, { target := 27, numerator := 3068081960857639803022213120 }, { target := 34, numerator := 90570493508117215567675392 }, { target := 35, numerator := 202686248373137113192857600 }, { target := 37, numerator := 7117047810291566258212044800 }, { target := 40, numerator := 7116668238224431566867660800 }, { target := 47, numerator := 203051859168836965315379200 }, { target := 126, numerator := 90591290637770778344423424 }, { target := 127, numerator := 3068071322008180715373461504 }, { target := 129, numerator := 33296682835094760610215231488 }, { target := 137, numerator := 3068066599653519794750095360 }, { target := 144, numerator := 90570040041796635539275776 }, { target := 145, numerator := 691558137035552874238574592 }, { target := 147, numerator := 24283109309997524779339350016 }, { target := 150, numerator := 24281814223854654562276212736 }, { target := 157, numerator := 692805587826041658030424064 }, { target := 161, numerator := 22190270848895768392064040960 }, { target := 164, numerator := 71618560312359986334604984320 }, { target := 166, numerator := 22146327747707633887220858880 }, { target := 216, numerator := 202685790698202681386729472 }, { target := 218, numerator := 7117031739668048047564128256 }, { target := 221, numerator := 7116652168458004660303691776 }, { target := 228, numerator := 203051400668336426816897024 }, { target := 232, numerator := 22194584287788815907771383808 }, { target := 235, numerator := 71632481831642874014267867136 }, { target := 237, numerator := 22150632644754435508455604224 }, { target := 406, numerator := 548205278397096081764646912 }, { target := 409, numerator := 1769319223807052406381871104 }, { target := 411, numerator := 547119674702372734224039936 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent1
