import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent0

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
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2482545990865723693465600 }, { target := 57, numerator := 62837615778644357776670720 }, { target := 59, numerator := 670628484061912426159800320 }, { target := 67, numerator := 62896784278840234119004160 }, { target := 74, numerator := 2351267373401265206722560 }, { target := 110, numerator := 16983911895870028719849472 }, { target := 112, numerator := 590042612543365882889371648 }, { target := 115, numerator := 590044137714401289672065024 }, { target := 122, numerator := 16983647461388408126963712 }, { target := 152, numerator := 120263784302273494075310080 }, { target := 153, numerator := 3044088406771744469675933696 }, { target := 155, numerator := 32487744295950418129480318976 }, { target := 163, numerator := 3046954749538898780711026688 }, { target := 170, numerator := 113904158582412960551927808 }, { target := 206, numerator := 425999075765369725903699968 }, { target := 208, numerator := 14831881203014600298137124864 }, { target := 211, numerator := 14831918780896768690225152000 }, { target := 218, numerator := 425991481632422567281164288 }, { target := 257, numerator := 149321083635175042039414784 }, { target := 260, numerator := 536106733538701471897354240 }, { target := 262, numerator := 149118232411812927518015488 }, { target := 283, numerator := 120262935618626964475084800 }, { target := 284, numerator := 3044066925092414271793397760 }, { target := 286, numerator := 32487515034768786684704194560 }, { target := 294, numerator := 3046933247632213806447329280 }, { target := 301, numerator := 113903354777699667652116480 }, { target := 302, numerator := 4648687043483080738545336320 }, { target := 304, numerator := 161713564738563528320834600960 }, { target := 307, numerator := 161713977720912417008071475200 }, { target := 314, numerator := 4648608313046212424100741120 }, { target := 353, numerator := 6938692759787767506457853952 }, { target := 356, numerator := 24911953623153179408172318720 }, { target := 358, numerator := 6929266613924162012304113664 }, { target := 660, numerator := 2482955700212324190126080 }, { target := 661, numerator := 62847986244527901582032896 }, { target := 663, numerator := 670739161873734502948274176 }, { target := 671, numerator := 62907164509653669970444288 }, { target := 678, numerator := 2351655417055958330769408 }, { target := 679, numerator := 173656040661374169444777984 }, { target := 681, numerator := 6196464611476558263695179776 }, { target := 684, numerator := 6196476761521820164442554368 }, { target := 691, numerator := 173648446883085481477668864 }, { target := 695, numerator := 6938501801305509782125281280 }, { target := 698, numerator := 24911268025877346481130700800 }, { target := 700, numerator := 6929075914857124123860008960 }, { target := 966, numerator := 6049715343021008079552512 }, { target := 968, numerator := 215868373422350746064519168 }, { target := 971, numerator := 215868796697665324107956224 }, { target := 978, numerator := 6049450795949396802404352 }, { target := 982, numerator := 149376850271586589853351936 }, { target := 985, numerator := 536306952212174804573224960 }, { target := 987, numerator := 149173923289797443612311552 }]

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
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 16983911895870028719849472 }, { target := 57, numerator := 425999075765369725903699968 }, { target := 59, numerator := 4648687043483080738545336320 }, { target := 67, numerator := 425545892270564821394522112 }, { target := 74, numerator := 16816743430945909527019520 }, { target := 110, numerator := 2482545990865723693465600 }, { target := 112, numerator := 120263784302273494075310080 }, { target := 115, numerator := 120262935618626964475084800 }, { target := 122, numerator := 2482955700212324190126080 }, { target := 152, numerator := 590042612543365882889371648 }, { target := 153, numerator := 14831881203014600298137124864 }, { target := 155, numerator := 161713564738563528320834600960 }, { target := 163, numerator := 14816361004412044613492146176 }, { target := 170, numerator := 584325720889193119317229568 }, { target := 206, numerator := 62837615778644357776670720 }, { target := 208, numerator := 3044088406771744469675933696 }, { target := 211, numerator := 3044066925092414271793397760 }, { target := 218, numerator := 62847986244527901582032896 }, { target := 283, numerator := 590044137714401289672065024 }, { target := 284, numerator := 14831918780896768690225152000 }, { target := 286, numerator := 161713977720912417008071475200 }, { target := 294, numerator := 14816398536877662563362406400 }, { target := 301, numerator := 584327229135701126441598976 }, { target := 302, numerator := 670628484061912426159800320 }, { target := 304, numerator := 32487744295950418129480318976 }, { target := 307, numerator := 32487515034768786684704194560 }, { target := 314, numerator := 670739161873734502948274176 }, { target := 660, numerator := 10936771283273986489712640 }, { target := 661, numerator := 252334924703156914033262592 }, { target := 663, numerator := 2848263667091092356653383680 }, { target := 671, numerator := 251889851609190651949744128 }, { target := 678, numerator := 10767028087924901447467008 }, { target := 679, numerator := 314786635888030886068748288 }, { target := 681, numerator := 11666851142474385130507993088 }, { target := 684, numerator := 11666855022988056205367181312 }, { target := 691, numerator := 314797016118844321920188416 }, { target := 966, numerator := 13118295461326166654189568 }, { target := 968, numerator := 482361506049255333804638208 }, { target := 971, numerator := 482361787215735469985759232 }, { target := 978, numerator := 13118683504980859778236416 }]

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
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 149321083635175042039414784 }, { target := 15, numerator := 6938692759787767506457853952 }, { target := 20, numerator := 6938501801305509782125281280 }, { target := 28, numerator := 149376850271586589853351936 }, { target := 136, numerator := 536106733538701471897354240 }, { target := 137, numerator := 24911953623153179408172318720 }, { target := 142, numerator := 24911268025877346481130700800 }, { target := 150, numerator := 536306952212174804573224960 }, { target := 267, numerator := 149118232411812927518015488 }, { target := 268, numerator := 6929266613924162012304113664 }, { target := 273, numerator := 6929075914857124123860008960 }, { target := 281, numerator := 149173923289797443612311552 }, { target := 660, numerator := 6046876178114421637251072 }, { target := 661, numerator := 173656556929265653247901696 }, { target := 663, numerator := 1800344645955120067447357440 }, { target := 671, numerator := 173648446883085481477668864 }, { target := 678, numerator := 6049450795949396802404352 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent0
