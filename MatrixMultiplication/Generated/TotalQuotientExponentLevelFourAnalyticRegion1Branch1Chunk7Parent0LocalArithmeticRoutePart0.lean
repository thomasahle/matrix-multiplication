import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 174765338798039830068461568 }, { target := 1, numerator := 20656141011651978086389383168 }, { target := 3, numerator := 196022660674793528338780520448 }, { target := 11, numerator := 20656155178751426695325024256 }, { target := 18, numerator := 174765338798039830068461568 }, { target := 19, numerator := 3063719580440529277173104640 }, { target := 21, numerator := 119898543384202633340541468672 }, { target := 24, numerator := 119898543384202633340541468672 }, { target := 31, numerator := 3063719580440529277173104640 }, { target := 35, numerator := 6498895666153265498098237440 }, { target := 38, numerator := 24141777856795383551125094400 }, { target := 40, numerator := 6497527655612759197750394880 }, { target := 45, numerator := 3351922240359270272571801600 }, { target := 47, numerator := 131177342966356664288731463680 }, { target := 50, numerator := 131177342966356664288731463680 }, { target := 57, numerator := 3351922240359270272571801600 }, { target := 61, numerator := 135664447030949417272800706560 }, { target := 64, numerator := 503959612760603631629736345600 }, { target := 66, numerator := 135635889810916348253039493120 }, { target := 71, numerator := 73454324043346041166144471040 }, { target := 73, numerator := 73454341556223696144150036480 }, { target := 75, numerator := 7040470304999370956273090560 }, { target := 78, numerator := 26153592678194998847052185600 }, { target := 80, numerator := 7038988293580489130896261120 }, { target := 85, numerator := 82932301339261659381130854400 }, { target := 87, numerator := 82932321111865463388556492800 }, { target := 90, numerator := 3063719580440529277173104640 }, { target := 92, numerator := 119898543384202633340541468672 }, { target := 95, numerator := 119898543384202633340541468672 }, { target := 102, numerator := 3063719580440529277173104640 }, { target := 106, numerator := 145954365169025420978122915840 }, { target := 109, numerator := 542184094367196322252351078400 }, { target := 111, numerator := 145923641932303216982810951680 }, { target := 116, numerator := 71084829719367136612397875200 }, { target := 118, numerator := 71084846667313254333048422400 }, { target := 120, numerator := 218525366774403552373553233920 }, { target := 123, numerator := 811767280434744771906581299200 }, { target := 125, numerator := 218479367419979028024357027840 }, { target := 130, numerator := 935950257971667298729905356800 }, { target := 132, numerator := 935950481119624515385137561600 }, { target := 135, numerator := 82932301339261659381130854400 }, { target := 137, numerator := 82932321111865463388556492800 }, { target := 140, numerator := 6769682985576318227185664000 }, { target := 143, numerator := 25147685267495191199088640000 }, { target := 145, numerator := 6768257974596624164323328000 }, { target := 150, numerator := 71084829719367136612397875200 }, { target := 152, numerator := 71084846667313254333048422400 }, { target := 161, numerator := 3351922240359270272571801600 }, { target := 163, numerator := 131177342966356664288731463680 }, { target := 166, numerator := 131177342966356664288731463680 }, { target := 173, numerator := 3351922240359270272571801600 }, { target := 177, numerator := 218525366774403552373553233920 }, { target := 180, numerator := 811767280434744771906581299200 }, { target := 182, numerator := 218479367419979028024357027840 }, { target := 191, numerator := 227732135634787345162525736960 }, { target := 194, numerator := 845968132398538231937341849600 }, { target := 196, numerator := 227684198265430436887836753920 }, { target := 211, numerator := 135664447030949417272800706560 }, { target := 214, numerator := 503959612760603631629736345600 }, { target := 216, numerator := 135635889810916348253039493120 }, { target := 238, numerator := 6769682985576318227185664000 }, { target := 241, numerator := 25147685267495191199088640000 }, { target := 243, numerator := 6768257974596624164323328000 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 136193049365960567962992640 }, { target := 1, numerator := 43870690178529346642331566080 }, { target := 3, numerator := 466583238917798228384152551424 }, { target := 11, numerator := 43870822404790866992397549568 }, { target := 18, numerator := 136193049365960567962992640 }, { target := 19, numerator := 48362680734898679083922620416 }, { target := 21, numerator := 1892726606676704610120057749504 }, { target := 24, numerator := 1892727300864577591957904162816 }, { target := 31, numerator := 48363374922771660921769033728 }, { target := 35, numerator := 2079192478317791555167759368192 }, { target := 38, numerator := 7452646786910699455729908056064 }, { target := 40, numerator := 2079796688109646425128404254720 }, { target := 71, numerator := 241184862527310677750705029120 }, { target := 73, numerator := 241185035036229045448798633984 }, { target := 89, numerator := 6499185206248246443220402176 }, { target := 90, numerator := 48362680734898679083922620416 }, { target := 92, numerator := 1892726606676704610120057749504 }, { target := 95, numerator := 1892727300864577591957904162816 }, { target := 102, numerator := 48363374922771660921769033728 }, { target := 106, numerator := 7574000570450785284029899866112 }, { target := 109, numerator := 27148208549262738483473970888704 }, { target := 111, numerator := 7576201562112645883911649361920 }, { target := 134, numerator := 94238185490599573426695831552 }, { target := 139, numerator := 166812420293704992042656989184 }, { target := 140, numerator := 2079193876927301702248006942720 }, { target := 143, numerator := 7452651800079408287141058314240 }, { target := 145, numerator := 2079798087125590113030189875200 }, { target := 154, numerator := 5415987671873538702683668480 }, { target := 155, numerator := 82932301339261659381130854400 }, { target := 157, numerator := 82932321111865463388556492800 }, { target := 159, numerator := 103986963299971943091526434816 }, { target := 160, numerator := 5415987671873538702683668480 }, { target := 187, numerator := 82932301339261659381130854400 }, { target := 189, numerator := 82932321111865463388556492800 }, { target := 201, numerator := 3438136264093390507486310563840 }, { target := 203, numerator := 3438137083809051067908442030080 }, { target := 205, numerator := 165729222759330284302120255488 }, { target := 206, numerator := 85301795663240563934877450240 }, { target := 208, numerator := 85301816000775905199658106880 }, { target := 210, numerator := 173311605499953238485877391360 }, { target := 221, numerator := 935950257971667298729905356800 }, { target := 223, numerator := 935950481119624515385137561600 }, { target := 225, numerator := 103986963299971943091526434816 }, { target := 226, numerator := 3438136264093390507486310563840 }, { target := 228, numerator := 3438137083809051067908442030080 }, { target := 230, numerator := 2654917156752408672055534288896 }, { target := 231, numerator := 170062012896829115264267190272 }, { target := 232, numerator := 73454324043346041166144471040 }, { target := 234, numerator := 73454341556223696144150036480 }, { target := 236, numerator := 94238185490599573426695831552 }, { target := 237, numerator := 165729222759330284302120255488 }, { target := 248, numerator := 82932301339261659381130854400 }, { target := 250, numerator := 82932321111865463388556492800 }, { target := 252, numerator := 5415987671873538702683668480 }, { target := 253, numerator := 85301795663240563934877450240 }, { target := 255, numerator := 85301816000775905199658106880 }, { target := 257, numerator := 170062012896829115264267190272 }, { target := 258, numerator := 5415987671873538702683668480 }, { target := 259, numerator := 82932301339261659381130854400 }, { target := 261, numerator := 82932321111865463388556492800 }, { target := 263, numerator := 165729222759330284302120255488 }, { target := 264, numerator := 173311605499953238485877391360 }, { target := 265, numerator := 6499185206248246443220402176 }]

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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1060577398921762139963129856 }, { target := 1, numerator := 173808209559291810376549662720 }, { target := 3, numerator := 1789422813968709969992661073920 }, { target := 11, numerator := 173808209559291810376549662720 }, { target := 18, numerator := 1060577398921762139963129856 }, { target := 19, numerator := 240218189731610033751704207360 }, { target := 21, numerator := 9603878655649172246842184826880 }, { target := 24, numerator := 9603876308633869619009064796160 }, { target := 31, numerator := 240218189731610033751704207360 }, { target := 35, numerator := 2056565232483619700274760777728 }, { target := 38, numerator := 7491574929418068152764761899008 }, { target := 40, numerator := 2056566615872470123868040724480 }, { target := 71, numerator := 48362680734898679083922620416 }, { target := 73, numerator := 48362680734898679083922620416 }, { target := 89, numerator := 1177314298378299769645694976 }, { target := 90, numerator := 240218361549109890958021885952 }, { target := 92, numerator := 9603885524880937706657431945216 }, { target := 95, numerator := 9603883177863956362063209562112 }, { target := 102, numerator := 240218361549109890958021885952 }, { target := 106, numerator := 7371541803739966329851347992576 }, { target := 109, numerator := 26852762507009576879663492366336 }, { target := 111, numerator := 7371546762351821014366850908160 }, { target := 116, numerator := 11535252661342573727170863038464 }, { target := 118, numerator := 11535259558217122951411926040576 }, { target := 134, numerator := 211411658283745536069976719360 }, { target := 140, numerator := 2057162866836385460405120532480 }, { target := 143, numerator := 7493751968329074163288668897280 }, { target := 145, numerator := 2057164250627246327035907276800 }, { target := 150, numerator := 11535250999070414493136019521536 }, { target := 152, numerator := 11535257895943278245216539115520 }, { target := 154, numerator := 2189351304469679880036220403712 }, { target := 232, numerator := 289548237450082338672474062848 }, { target := 234, numerator := 289548409959000706370567667712 }, { target := 236, numerator := 211411771620541124941461848064 }, { target := 265, numerator := 1177314298378299769645694976 }]

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

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 6615242084931250843992195072 }, { target := 1, numerator := 95921010231503137237886828544 }, { target := 2, numerator := 169791213513235438329133006848 }, { target := 3, numerator := 5512701737442709036660162560 }, { target := 4, numerator := 105843873358900013503875121152 }, { target := 5, numerator := 5512701737442709036660162560 }, { target := 6, numerator := 168688673165746896521800974336 }, { target := 7, numerator := 176406455598166689173125201920 }, { target := 8, numerator := 105843873358900013503875121152 }, { target := 9, numerator := 2702326391694415969770811686912 }, { target := 10, numerator := 173098834555701063751129104384 }, { target := 11, numerator := 95921010231503137237886828544 }, { target := 12, numerator := 168688673165746896521800974336 }, { target := 13, numerator := 5512701737442709036660162560 }, { target := 14, numerator := 173098834555701063751129104384 }, { target := 15, numerator := 5512701737442709036660162560 }, { target := 16, numerator := 168688673165746896521800974336 }, { target := 17, numerator := 176406455598166689173125201920 }, { target := 18, numerator := 6615242084931250843992195072 }, { target := 19, numerator := 74053951178393763951174221824 }, { target := 20, numerator := 83609299717541346396487024640 }, { target := 21, numerator := 71665114043606868339846021120 }, { target := 22, numerator := 943590668240823766474639278080 }, { target := 23, numerator := 83609299717541346396487024640 }, { target := 24, numerator := 71665114043606868339846021120 }, { target := 25, numerator := 83609299717541346396487024640 }, { target := 26, numerator := 83609299717541346396487024640 }, { target := 27, numerator := 3466202682575785532037219221504 }, { target := 28, numerator := 85998136852328242007815225344 }, { target := 29, numerator := 943590668240823766474639278080 }, { target := 30, numerator := 3466202682575785532037219221504 }, { target := 31, numerator := 74053951178393763951174221824 }, { target := 32, numerator := 83609299717541346396487024640 }, { target := 33, numerator := 85998136852328242007815225344 }, { target := 34, numerator := 83609299717541346396487024640 }, { target := 35, numerator := 6580131861980181316824465408 }, { target := 36, numerator := 137360252618836284988710715392 }, { target := 37, numerator := 7128476183811863093226504192 }, { target := 38, numerator := 147778794733638238740349452288 }, { target := 39, numerator := 221256933859083596778222649344 }, { target := 40, numerator := 6854304022896022205025484800 }, { target := 41, numerator := 221256933859083596778222649344 }, { target := 42, numerator := 230578787330222186977057308672 }, { target := 43, numerator := 137360252618836284988710715392 }, { target := 44, numerator := 6854304022896022205025484800 }, { target := 90, numerator := 74053968834233685500428812288 }, { target := 91, numerator := 83609319651554161048871239680 }, { target := 92, numerator := 71665131129903566613318205440 }, { target := 93, numerator := 943590893210396960408689704960 }, { target := 94, numerator := 83609319651554161048871239680 }, { target := 95, numerator := 71665131129903566613318205440 }, { target := 96, numerator := 83609319651554161048871239680 }, { target := 97, numerator := 83609319651554161048871239680 }, { target := 98, numerator := 3466203508983002505197490536448 }, { target := 99, numerator := 85998157355884279935981846528 }, { target := 100, numerator := 943590893210396960408689704960 }, { target := 101, numerator := 3466203508983002505197490536448 }, { target := 102, numerator := 74053968834233685500428812288 }, { target := 103, numerator := 83609319651554161048871239680 }, { target := 104, numerator := 85998157355884279935981846528 }, { target := 105, numerator := 83609319651554161048871239680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 3299390317397493067724881920 }, { target := 72, numerator := 3609762412694598755077324800 }, { target := 73, numerator := 3299390317397493067724881920 }, { target := 74, numerator := 3609762412694598755077324800 }, { target := 89, numerator := 174765338798039830068461568 }, { target := 106, numerator := 24443550080005325845514158080 }, { target := 107, numerator := 510259107920111177025108049920 }, { target := 108, numerator := 26480512586672436332640337920 }, { target := 109, numerator := 548961395546786276280505466880 }, { target := 110, numerator := 821914371440179081555413565440 }, { target := 111, numerator := 25462031333338881089077248000 }, { target := 112, numerator := 821914371440179081555413565440 }, { target := 113, numerator := 856542734053519959836558622720 }, { target := 114, numerator := 510259107920111177025108049920 }, { target := 115, numerator := 25462031333338881089077248000 }, { target := 116, numerator := 129121508259910528212890812416 }, { target := 117, numerator := 141267907809922561541710807040 }, { target := 118, numerator := 129121508259910528212890812416 }, { target := 119, numerator := 141267907809922561541710807040 }, { target := 134, numerator := 20656141011651978086389383168 }, { target := 140, numerator := 6578746751307918687722274816 }, { target := 141, numerator := 137331338433552802606202486784 }, { target := 142, numerator := 7126975647250245245032464384 }, { target := 143, numerator := 147747687456457007195096088576 }, { target := 144, numerator := 221210359512728765874661490688 }, { target := 145, numerator := 6852861199279081966377369600 }, { target := 146, numerator := 221210359512728765874661490688 }, { target := 147, numerator := 230530250743748317348934713344 }, { target := 148, numerator := 137331338433552802606202486784 }, { target := 149, numerator := 6852861199279081966377369600 }, { target := 150, numerator := 129121508259910528212890812416 }, { target := 151, numerator := 141267907809922561541710807040 }, { target := 152, numerator := 129121508259910528212890812416 }, { target := 153, numerator := 141267907809922561541710807040 }, { target := 154, numerator := 196022660674793528338780520448 }, { target := 232, numerator := 3299390317397493067724881920 }, { target := 233, numerator := 3609762412694598755077324800 }, { target := 234, numerator := 3299390317397493067724881920 }, { target := 235, numerator := 3609762412694598755077324800 }, { target := 236, numerator := 20656155178751426695325024256 }, { target := 265, numerator := 174765338798039830068461568 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent0
