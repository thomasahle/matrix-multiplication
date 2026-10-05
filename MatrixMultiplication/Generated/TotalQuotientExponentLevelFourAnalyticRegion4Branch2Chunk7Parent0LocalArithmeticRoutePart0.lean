import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent0

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
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 58736338927389776019456000 }, { target := 82, numerator := 2706509329333698353430528000 }, { target := 85, numerator := 2706505043982731049959424000 }, { target := 92, numerator := 58730735006894071480320000 }, { target := 131, numerator := 325598322450672378749911040 }, { target := 134, numerator := 1166603564804394789223006208 }, { target := 136, numerator := 325564475896496755199442944 }, { target := 176, numerator := 2044864419623822027485347840 }, { target := 178, numerator := 94225222919939348257224785920 }, { target := 181, numerator := 94225073728452805791171215360 }, { target := 188, numerator := 2044669323064497264184524800 }, { target := 227, numerator := 11014418101247546713681428480 }, { target := 230, numerator := 39445879292311080793844744192 }, { target := 232, numerator := 11013287747123328108279627776 }, { target := 263, numerator := 429003945689366623588188160 }, { target := 265, numerator := 429002820583219215288238080 }, { target := 286, numerator := 2044866676543665539100180480 }, { target := 288, numerator := 94225326916455364921906954240 }, { target := 291, numerator := 94225177724804159594477649920 }, { target := 298, numerator := 2044671579769012418615705600 }, { target := 302, numerator := 133481251236823744492412600320 }, { target := 305, numerator := 477902578800117857831226441728 }, { target := 307, numerator := 133467394517118254146675277824 }, { target := 338, numerator := 19379703680397046956511199232 }, { target := 340, numerator := 19379652855168130404807868416 }, { target := 573, numerator := 58736088158518274728919040 }, { target := 575, numerator := 2706497774165252057354731520 }, { target := 578, numerator := 2706493488832580627369820160 }, { target := 585, numerator := 58730484261947943210188800 }, { target := 589, numerator := 5993394867720967475722977280 }, { target := 592, numerator := 21437875291463879377045946368 }, { target := 594, numerator := 5992256153187021163723751424 }, { target := 599, numerator := 19376421631387700159181750272 }, { target := 601, numerator := 19376370814766288395290279936 }, { target := 763, numerator := 195517472756071642358087680 }, { target := 766, numerator := 699240873671175994718814208 }, { target := 768, numerator := 195480236373418744473452544 }, { target := 773, numerator := 429003945689366623588188160 }, { target := 775, numerator := 429002820583219215288238080 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 293874091599326884051025920 }, { target := 27, numerator := 10031127924072487772907110400 }, { target := 29, numerator := 121939517060101600247283712000 }, { target := 37, numerator := 10031250541292558003627622400 }, { target := 44, numerator := 307467236406680164646256640 }, { target := 80, numerator := 279655950338347291901952000 }, { target := 82, numerator := 9925579648222798400024739840 }, { target := 85, numerator := 9925581905142641911639572480 }, { target := 92, numerator := 279651836409862929871011840 }, { target := 157, numerator := 1044855719734865733615616000 }, { target := 158, numerator := 35672313883899562475147755520 }, { target := 160, numerator := 433608951289786610131549552640 }, { target := 168, numerator := 35672753393393197546586767360 }, { target := 175, numerator := 1092781819741463313530224640 }, { target := 176, numerator := 10587224557932674725969920000 }, { target := 178, numerator := 375348623950833078560012369920 }, { target := 181, numerator := 375348727947349095224694538240 }, { target := 188, numerator := 10587075194895578204072837120 }, { target := 267, numerator := 143674051839814147831234560 }, { target := 268, numerator := 5021043146827057729089044480 }, { target := 270, numerator := 60580648112719973288205352960 }, { target := 278, numerator := 5021161490999431888361226240 }, { target := 285, numerator := 143678278417398939233812480 }, { target := 286, numerator := 10587220272581707422498816000 }, { target := 288, numerator := 375348474759346536093958799360 }, { target := 291, numerator := 375348578755697889897265233920 }, { target := 298, numerator := 10587070909562906774087925760 }, { target := 573, numerator := 279646483258238726622412800 }, { target := 575, numerator := 9925246743794823410902630400 }, { target := 578, numerator := 9925249000499338565333811200 }, { target := 585, numerator := 279642369421233732022435840 }, { target := 589, numerator := 5021153131213734205131325440 }, { target := 592, numerator := 18008471450535283431183482880 }, { target := 594, numerator := 5021161490999431888361226240 }, { target := 763, numerator := 143678039205889981682810880 }, { target := 766, numerator := 515304313470064676055285760 }, { target := 768, numerator := 143678278417398939233812480 }]

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
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 429003945689366623588188160 }, { target := 11, numerator := 19379703680397046956511199232 }, { target := 16, numerator := 19376421631387700159181750272 }, { target := 24, numerator := 429003945689366623588188160 }, { target := 26, numerator := 31724230851345494698885120 }, { target := 27, numerator := 983290177175058940774318080 }, { target := 29, numerator := 11541734176722144245128888320 }, { target := 37, numerator := 983297457642143677226680320 }, { target := 44, numerator := 31728275555281459394641920 }, { target := 141, numerator := 429002820583219215288238080 }, { target := 142, numerator := 19379652855168130404807868416 }, { target := 147, numerator := 19376370814766288395290279936 }, { target := 155, numerator := 429002820583219215288238080 }, { target := 157, numerator := 121747845069529055607390208 }, { target := 158, numerator := 3773565408411518318696988672 }, { target := 160, numerator := 44293627510331247699676889088 }, { target := 168, numerator := 3773593348605965261642661888 }, { target := 175, numerator := 121763367399777357243875328 }, { target := 267, numerator := 181890424056682607368208384 }, { target := 268, numerator := 5992244600296270379190583296 }, { target := 270, numerator := 72886746404398280858469924864 }, { target := 278, numerator := 5992256153187021163723751424 }, { target := 285, numerator := 195480236373418744473452544 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent0
