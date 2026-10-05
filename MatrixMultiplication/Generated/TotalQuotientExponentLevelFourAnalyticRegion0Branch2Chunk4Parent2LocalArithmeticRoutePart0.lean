import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent2

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
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 153947311242841178454884352 }, { target := 82, numerator := 5710426036583012995256287232 }, { target := 85, numerator := 5710621467831003241292759040 }, { target := 92, numerator := 153526527229505003828805632 }, { target := 131, numerator := 251674286689740523359436800 }, { target := 134, numerator := 903634007795671322591232000 }, { target := 136, numerator := 251791634582841990148259840 }, { target := 176, numerator := 5521738468617127671669719040 }, { target := 178, numerator := 206491675108077263459052421120 }, { target := 181, numerator := 206502690572186719371908874240 }, { target := 188, numerator := 5510164444623760710833274880 }, { target := 227, numerator := 6335741091835949907311591424 }, { target := 230, numerator := 22768286450996112481018970112 }, { target := 232, numerator := 6339117965635149666348695552 }, { target := 286, numerator := 5524134971593375001314590720 }, { target := 288, numerator := 206579350437334353063853424640 }, { target := 291, numerator := 206590366022618786450647285760 }, { target := 298, numerator := 5512551831447419314325422080 }, { target := 302, numerator := 85970285894362947377543774208 }, { target := 305, numerator := 309027111228053348988699541504 }, { target := 307, numerator := 86017851836580406146549940224 }, { target := 573, numerator := 151553514645117222046924800 }, { target := 575, numerator := 5622851893196922533948948480 }, { target := 578, numerator := 5623047208615708063736791040 }, { target := 585, numerator := 151141841064798246813040640 }, { target := 589, numerator := 6318515116731009128315486208 }, { target := 592, numerator := 22705846582694398799437103104 }, { target := 594, numerator := 6321871404080353267851198464 }, { target := 763, numerator := 247819189120035951514484736 }, { target := 766, numerator := 889659007053769993688711168 }, { target := 768, numerator := 247931903638627610429227008 }]

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 244348797091944700431040512 }, { target := 27, numerator := 6493562667793995260881797120 }, { target := 29, numerator := 85501041003987526296633606144 }, { target := 37, numerator := 6476393102248652783996633088 }, { target := 44, numerator := 240469868764781344299417600 }, { target := 80, numerator := 146962274023242174446960640 }, { target := 82, numerator := 5124401667521013130954014720 }, { target := 85, numerator := 5126796483534689915507834880 }, { target := 92, numerator := 144569971592366415119646720 }, { target := 131, numerator := 74972347096636636551708672 }, { target := 134, numerator := 266218351228722902569320448 }, { target := 136, numerator := 74972570344010814981144576 }, { target := 157, numerator := 880211993978871235339091968 }, { target := 158, numerator := 23387972366451396983337779200 }, { target := 160, numerator := 308140799556694251447775133696 }, { target := 168, numerator := 23325731401712955697137713152 }, { target := 175, numerator := 866152426766614367567872000 }, { target := 176, numerator := 5375391814475682004808499200 }, { target := 178, numerator := 187433591108706068973853081600 }, { target := 181, numerator := 187521185523549279592277606400 }, { target := 188, numerator := 5287889338141884360006041600 }, { target := 227, numerator := 2041453640696629891317104640 }, { target := 230, numerator := 7248971699333545735235829760 }, { target := 232, numerator := 2041459719593482421136261120 }, { target := 267, numerator := 244552422009234474229825536 }, { target := 268, numerator := 6498915218474752731764490240 }, { target := 270, numerator := 85574592891859116731454717952 }, { target := 278, numerator := 6481725019984955032358354944 }, { target := 285, numerator := 240668862031314067600179200 }, { target := 286, numerator := 5375396422454674988917063680 }, { target := 288, numerator := 187433751783514569930587504640 }, { target := 291, numerator := 187521346273446860086113730560 }, { target := 298, numerator := 5287893871110610800491888640 }, { target := 302, numerator := 24313268604068240898857631744 }, { target := 305, numerator := 86333675433865293486931050496 }, { target := 307, numerator := 24313341002406878433459044352 }, { target := 573, numerator := 146400758868811396646174720 }, { target := 575, numerator := 5104822294427967974602178560 }, { target := 578, numerator := 5107207960300952595191562240 }, { target := 585, numerator := 144017596974701595915714560 }, { target := 589, numerator := 2041465551062008473266946048 }, { target := 592, numerator := 7249013991698082899303596032 }, { target := 594, numerator := 2041471629994326850151645184 }, { target := 763, numerator := 74950227846647841502003200 }, { target := 766, numerator := 266139808266011026443468800 }, { target := 768, numerator := 74950451028156875381145600 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 82297836694432459480104960 }, { target := 27, numerator := 1883632064738584537746898944 }, { target := 29, numerator := 24782513494443661979767799808 }, { target := 37, numerator := 1883587565544364817585799168 }, { target := 44, numerator := 82299548201902448717070336 }, { target := 80, numerator := 6985037219599004007923712 }, { target := 82, numerator := 397336801096114540715704320 }, { target := 85, numerator := 397338488058685085806755840 }, { target := 92, numerator := 6983543052750806927278080 }, { target := 157, numerator := 289640365045522989821460480 }, { target := 158, numerator := 6629285783878261232917020672 }, { target := 160, numerator := 87219987105224391027855458304 }, { target := 168, numerator := 6629129172679526001602985984 }, { target := 175, numerator := 289646388553166652564307968 }, { target := 176, numerator := 335034222107330990447788032 }, { target := 178, numerator := 19058083999371194485199339520 }, { target := 181, numerator := 19058164913785073471575818240 }, { target := 188, numerator := 334962555055038173942906880 }, { target := 267, numerator := 82211782917618330899578880 }, { target := 268, numerator := 1881662466753879355720466432 }, { target := 270, numerator := 24756599947128167848554266624 }, { target := 278, numerator := 1881618014089725085644488704 }, { target := 285, numerator := 82213492635470418210193408 }, { target := 286, numerator := 335225045376328252375695360 }, { target := 288, numerator := 19068938788672149441321369600 }, { target := 291, numerator := 19069019749171926364533555200 }, { target := 298, numerator := 335153337505097263244902400 }, { target := 573, numerator := 7125768360693607182630912 }, { target := 575, numerator := 405342150195792736231096320 }, { target := 578, numerator := 405343871146466719133859840 }, { target := 585, numerator := 7124244090096650897326080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent2
