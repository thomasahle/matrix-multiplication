import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left6.expected,
    Slot1.Left14.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 646659191239882606840381440 }, { target := 87, numerator := 11510533604069910401758789632 }, { target := 88, numerator := 646659191239882606840381440 }, { target := 89, numerator := 10238770527964807941639372800 }, { target := 90, numerator := 17481353469851493138251644928 }, { target := 91, numerator := 646659191239882606840381440 }, { target := 92, numerator := 17481353469851493138251644928 }, { target := 93, numerator := 17481353469851493138251644928 }, { target := 94, numerator := 11510533604069910401758789632 }, { target := 95, numerator := 646659191239882606840381440 }, { target := 122, numerator := 1371289384701797962658873344 }, { target := 123, numerator := 62388022932046236702736384 }, { target := 124, numerator := 1371289384701797962658873344 }, { target := 125, numerator := 62388022932046236702736384 }, { target := 161, numerator := 23435143135483530553306644480 }, { target := 162, numerator := 417145547811606843848858271744 }, { target := 163, numerator := 23435143135483530553306644480 }, { target := 164, numerator := 371056432978489233760688537600 }, { target := 165, numerator := 633530036095904775957722955776 }, { target := 166, numerator := 23435143135483530553306644480 }, { target := 167, numerator := 633530036095904775957722955776 }, { target := 168, numerator := 633530036095904775957722955776 }, { target := 169, numerator := 417145547811606843848858271744 }, { target := 170, numerator := 23435143135483530553306644480 }, { target := 197, numerator := 200145734492061466241395589120 }, { target := 198, numerator := 6541271683436715706601701376 }, { target := 199, numerator := 200145734492061466241395589120 }, { target := 200, numerator := 6541271683436715706601701376 }, { target := 215, numerator := 3726452448197817125644009472 }, { target := 242, numerator := 2088165534348501908491159470080 }, { target := 243, numerator := 70508370754092045265010688000 }, { target := 244, numerator := 2088165534348501908491159470080 }, { target := 245, numerator := 70508370754092045265010688000 }, { target := 260, numerator := 313186197608859533248531791872 }, { target := 416, numerator := 200145738946950160042252304384 }, { target := 417, numerator := 6541276673280987645035413504 }, { target := 418, numerator := 200145738946950160042252304384 }, { target := 419, numerator := 6541276673280987645035413504 }, { target := 420, numerator := 313186145662828221682434441216 }, { target := 498, numerator := 1371289384701797962658873344 }, { target := 499, numerator := 62388022932046236702736384 }, { target := 500, numerator := 1371289384701797962658873344 }, { target := 501, numerator := 62388022932046236702736384 }, { target := 502, numerator := 3726504394229128691741360128 }]

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
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 290012802764609527270185369600 }, { target := 89, numerator := 1037501653717893266711720755200 }, { target := 91, numerator := 290012706352477571945752166400 }, { target := 122, numerator := 11774550248994892850730631168 }, { target := 124, numerator := 11774550248994892850730631168 }, { target := 161, numerator := 10896526021628084826750006067200 }, { target := 164, numerator := 38981602396343489140009363046400 }, { target := 166, numerator := 10896522399176611522228833484800 }, { target := 197, numerator := 1879773896825730983833188171776 }, { target := 199, numerator := 1879773896825730983833188171776 }, { target := 215, numerator := 20890238162940792138922721280 }, { target := 232, numerator := 10919137046060194960317716889600 }, { target := 233, numerator := 417145701110967625402873282560 }, { target := 234, numerator := 23435151747807169966453555200 }, { target := 235, numerator := 39349710704625088566192295116800 }, { target := 236, numerator := 633530268915720494759794442240 }, { target := 237, numerator := 10919133423882695324377861324800 }, { target := 238, numerator := 633530268915720494759794442240 }, { target := 239, numerator := 633530268915720494759794442240 }, { target := 240, numerator := 417145701110967625402873282560 }, { target := 241, numerator := 23435151747807169966453555200 }, { target := 242, numerator := 18757316684672016668409479561216 }, { target := 244, numerator := 18757316684672016668409479561216 }, { target := 260, numerator := 16247963015620616108051005440 }, { target := 265, numerator := 18569100589280704123486863360 }, { target := 355, numerator := 21818693192404827345097064448 }, { target := 400, numerator := 257646270676269769713380229120 }, { target := 405, numerator := 579355938385557968652790136832 }, { target := 406, numerator := 291483580659222806862621573120 }, { target := 407, numerator := 11510380304709128847743778816 }, { target := 408, numerator := 646650578916243193693470720 }, { target := 409, numerator := 1050688548942747882231116595200 }, { target := 410, numerator := 17481120650035774336180158464 }, { target := 411, numerator := 291483483973117182956871352320 }, { target := 412, numerator := 17481120650035774336180158464 }, { target := 413, numerator := 17481120650035774336180158464 }, { target := 414, numerator := 11510380304709128847743778816 }, { target := 415, numerator := 646650578916243193693470720 }, { target := 416, numerator := 1879773896825730983833188171776 }, { target := 418, numerator := 1879773896825730983833188171776 }, { target := 420, numerator := 16247963015620616108051005440 }, { target := 425, numerator := 257646270676269769713380229120 }, { target := 426, numerator := 18569100589280704123486863360 }, { target := 471, numerator := 18104873074548686520399691776 }, { target := 476, numerator := 18104873074548686520399691776 }, { target := 491, numerator := 18104873074548686520399691776 }, { target := 496, numerator := 579355938385557968652790136832 }, { target := 497, numerator := 18104873074548686520399691776 }, { target := 498, numerator := 11773206735730516436667334656 }, { target := 500, numerator := 11773206735730516436667334656 }, { target := 502, numerator := 20890238162940792138922721280 }, { target := 503, numerator := 21818693192404827345097064448 }]

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
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 91259146412864112739315875840 }, { target := 36, numerator := 108370236365276133877937602560 }, { target := 37, numerator := 82703601436658102170005012480 }, { target := 38, numerator := 852702649295199053407982714880 }, { target := 39, numerator := 102666539714472126831730360320 }, { target := 40, numerator := 82703601436658102170005012480 }, { target := 41, numerator := 102666539714472126831730360320 }, { target := 42, numerator := 102666539714472126831730360320 }, { target := 43, numerator := 4397550117769889432625783767040 }, { target := 44, numerator := 102666539714472126831730360320 }, { target := 45, numerator := 852702649295199053407982714880 }, { target := 46, numerator := 4397550117769889432625783767040 }, { target := 47, numerator := 91259146412864112739315875840 }, { target := 48, numerator := 102666539714472126831730360320 }, { target := 49, numerator := 102666539714472126831730360320 }, { target := 50, numerator := 108370236365276133877937602560 }, { target := 122, numerator := 22969596049055101201940480000 }, { target := 124, numerator := 22969585096300807436894208000 }, { target := 145, numerator := 313276692908066574618467500032 }, { target := 146, numerator := 372016072828329057359430156288 }, { target := 147, numerator := 283907002947935333247986171904 }, { target := 148, numerator := 2927179099359747056591305703424 }, { target := 149, numerator := 352436279521574896445775937536 }, { target := 150, numerator := 283907002947935333247986171904 }, { target := 151, numerator := 352436279521574896445775937536 }, { target := 152, numerator := 352436279521574896445775937536 }, { target := 153, numerator := 15096020639507458064427402657792 }, { target := 154, numerator := 352436279521574896445775937536 }, { target := 155, numerator := 2927179099359747056591305703424 }, { target := 156, numerator := 15096020639507458064427402657792 }, { target := 157, numerator := 313276692908066574618467500032 }, { target := 158, numerator := 352436279521574896445775937536 }, { target := 159, numerator := 352436279521574896445775937536 }, { target := 160, numerator := 372016072828329057359430156288 }, { target := 197, numerator := 385889213624125700192600064000 }, { target := 199, numerator := 385889029617853564939822694400 }, { target := 211, numerator := 836093296185605683750633472000 }, { target := 213, numerator := 836092897505349390702949171200 }, { target := 216, numerator := 91259146412864112739315875840 }, { target := 217, numerator := 108370236365276133877937602560 }, { target := 218, numerator := 82703601436658102170005012480 }, { target := 219, numerator := 852702649295199053407982714880 }, { target := 220, numerator := 102666539714472126831730360320 }, { target := 221, numerator := 82703601436658102170005012480 }, { target := 222, numerator := 102666539714472126831730360320 }, { target := 223, numerator := 102666539714472126831730360320 }, { target := 224, numerator := 4397550117769889432625783767040 }, { target := 225, numerator := 102666539714472126831730360320 }, { target := 226, numerator := 852702649295199053407982714880 }, { target := 227, numerator := 4397550117769889432625783767040 }, { target := 228, numerator := 91259146412864112739315875840 }, { target := 229, numerator := 102666539714472126831730360320 }, { target := 230, numerator := 102666539714472126831730360320 }, { target := 231, numerator := 108370236365276133877937602560 }, { target := 242, numerator := 27563515258866121442328576000 }, { target := 244, numerator := 27563502115560968924273049600 }, { target := 256, numerator := 441016244141857943077257216000 }, { target := 258, numerator := 441016033848975502788368793600 }, { target := 261, numerator := 32157434468677141682716672000 }, { target := 263, numerator := 32157419134821130411651891200 }, { target := 337, numerator := 836093296185605683750633472000 }, { target := 339, numerator := 836092897505349390702949171200 }, { target := 351, numerator := 836093296185605683750633472000 }, { target := 353, numerator := 836092897505349390702949171200 }]

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
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot10.Left16.expected,
    Slot10.Left17.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 630862122439272542101013790720 }, { target := 37, numerator := 23296898888154760775779064217600 }, { target := 40, numerator := 23296893183331979548182467051520 }, { target := 47, numerator := 630867827262053769697610956800 }, { target := 86, numerator := 631047397658784810101630828544 }, { target := 89, numerator := 2295255413747396816869712199680 }, { target := 91, numerator := 631047397658784810101630828544 }, { target := 145, numerator := 2294581527836138039178323558400 }, { target := 147, numerator := 84735843131510830078070095872000 }, { target := 150, numerator := 84735822381840644190979384934400 }, { target := 157, numerator := 2294602277506323926269034496000 }, { target := 161, numerator := 23303740855522794479384285675520 }, { target := 164, numerator := 84760728841681611525963802214400 }, { target := 166, numerator := 23303740855522794479384285675520 }, { target := 216, numerator := 630862122439272542101013790720 }, { target := 218, numerator := 23296898888154760775779064217600 }, { target := 221, numerator := 23296893183331979548182467051520 }, { target := 228, numerator := 630867827262053769697610956800 }, { target := 232, numerator := 23303735149024588059062990536704 }, { target := 235, numerator := 84760708085917543058583196794880 }, { target := 237, numerator := 23303735149024588059062990536704 }, { target := 382, numerator := 441016244141857943077257216000 }, { target := 384, numerator := 441016033848975502788368793600 }, { target := 396, numerator := 10317942545235551459911663616000 }, { target := 398, numerator := 10317937625258322700652878233600 }, { target := 401, numerator := 826905457765983643269857280000 }, { target := 403, numerator := 826905063466829067728191488000 }, { target := 406, numerator := 631053104156991230422925967360 }, { target := 409, numerator := 2295276169511465284250317619200 }, { target := 411, numerator := 631053104156991230422925967360 }, { target := 416, numerator := 385889213624125700192600064000 }, { target := 418, numerator := 385889029617853564939822694400 }, { target := 421, numerator := 836093296185605683750633472000 }, { target := 423, numerator := 836092897505349390702949171200 }, { target := 453, numerator := 32157434468677141682716672000 }, { target := 455, numerator := 32157419134821130411651891200 }, { target := 467, numerator := 826905457765983643269857280000 }, { target := 469, numerator := 826905063466829067728191488000 }, { target := 472, numerator := 32157434468677141682716672000 }, { target := 474, numerator := 32157419134821130411651891200 }, { target := 487, numerator := 836093296185605683750633472000 }, { target := 489, numerator := 836092897505349390702949171200 }, { target := 492, numerator := 836093296185605683750633472000 }, { target := 494, numerator := 836092897505349390702949171200 }, { target := 498, numerator := 27563515258866121442328576000 }, { target := 500, numerator := 27563502115560968924273049600 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 23114667181996501841110630400 }, { target := 17, numerator := 388326408657541230930658590720 }, { target := 18, numerator := 841373885424672667016426946560 }, { target := 19, numerator := 27737600618395802209332756480 }, { target := 20, numerator := 443801609894332835349324103680 }, { target := 21, numerator := 32360534054795102577554882560 }, { target := 22, numerator := 841373885424672667016426946560 }, { target := 23, numerator := 841373885424672667016426946560 }, { target := 24, numerator := 443801609894332835349324103680 }, { target := 25, numerator := 10383108498152828627026895175680 }, { target := 26, numerator := 832128018551874066279982694400 }, { target := 27, numerator := 388326408657541230930658590720 }, { target := 28, numerator := 841373885424672667016426946560 }, { target := 29, numerator := 32360534054795102577554882560 }, { target := 30, numerator := 832128018551874066279982694400 }, { target := 31, numerator := 32360534054795102577554882560 }, { target := 32, numerator := 841373885424672667016426946560 }, { target := 33, numerator := 841373885424672667016426946560 }, { target := 34, numerator := 27737600618395802209332756480 }, { target := 86, numerator := 91373077931481920620388679680 }, { target := 89, numerator := 313667799890473648993771454464 }, { target := 91, numerator := 91373077931481920620388679680 }, { target := 112, numerator := 108505530043634780736711557120 }, { target := 115, numerator := 372480512369937458180103602176 }, { target := 117, numerator := 108505530043634780736711557120 }, { target := 126, numerator := 23114656160066917799653539840 }, { target := 127, numerator := 388326223489124219034179469312 }, { target := 128, numerator := 841373484226435807907388850176 }, { target := 129, numerator := 27737587392080301359584247808 }, { target := 130, numerator := 443801398273284821753347964928 }, { target := 131, numerator := 32360518624093684919514955776 }, { target := 132, numerator := 841373484226435807907388850176 }, { target := 133, numerator := 841373484226435807907388850176 }, { target := 134, numerator := 443801398273284821753347964928 }, { target := 135, numerator := 10383103547102059475604370096128 }, { target := 136, numerator := 832127621762409040787527434240 }, { target := 137, numerator := 388326223489124219034179469312 }, { target := 138, numerator := 841373484226435807907388850176 }, { target := 139, numerator := 32360518624093684919514955776 }, { target := 140, numerator := 832127621762409040787527434240 }, { target := 141, numerator := 32360518624093684919514955776 }, { target := 142, numerator := 841373484226435807907388850176 }, { target := 143, numerator := 841373484226435807907388850176 }, { target := 144, numerator := 27737587392080301359584247808 }, { target := 161, numerator := 82806851875405490562227240960 }, { target := 164, numerator := 284261443650741744400605380608 }, { target := 166, numerator := 82806851875405490562227240960 }, { target := 187, numerator := 853767196922284195796756725760 }, { target := 190, numerator := 2930833505226613157785552027648 }, { target := 192, numerator := 853767196922284195796756725760 }, { target := 201, numerator := 102794712672917160697937264640 }, { target := 204, numerator := 352876274876782855117992886272 }, { target := 206, numerator := 102794712672917160697937264640 }, { target := 232, numerator := 82806851875405490562227240960 }, { target := 235, numerator := 284261443650741744400605380608 }, { target := 237, numerator := 82806851875405490562227240960 }, { target := 246, numerator := 102794712672917160697937264640 }, { target := 249, numerator := 352876274876782855117992886272 }, { target := 251, numerator := 102794712672917160697937264640 }, { target := 301, numerator := 102794712672917160697937264640 }, { target := 304, numerator := 352876274876782855117992886272 }, { target := 306, numerator := 102794712672917160697937264640 }]

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

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20890238162940792138922721280 }, { target := 1, numerator := 16247963015620616108051005440 }, { target := 2, numerator := 18569100589280704123486863360 }, { target := 3, numerator := 21818693192404827345097064448 }, { target := 4, numerator := 257646270676269769713380229120 }, { target := 5, numerator := 579355938385557968652790136832 }, { target := 6, numerator := 16247963015620616108051005440 }, { target := 7, numerator := 257646270676269769713380229120 }, { target := 8, numerator := 18569100589280704123486863360 }, { target := 9, numerator := 18104873074548686520399691776 }, { target := 10, numerator := 18104873074548686520399691776 }, { target := 11, numerator := 18104873074548686520399691776 }, { target := 12, numerator := 579355938385557968652790136832 }, { target := 13, numerator := 18104873074548686520399691776 }, { target := 14, numerator := 20890238162940792138922721280 }, { target := 15, numerator := 21818693192404827345097064448 }, { target := 16, numerator := 11753856839066958065404215296 }, { target := 17, numerator := 1876470252015843934652462006272 }, { target := 19, numerator := 18724351277493331226109990141952 }, { target := 27, numerator := 1876470252015843934652462006272 }, { target := 34, numerator := 11752515686985823086163525632 }, { target := 35, numerator := 290749343216075202260077903872 }, { target := 37, numerator := 10924199738508410121548101320704 }, { target := 40, numerator := 10923373518170958933945806225408 }, { target := 47, numerator := 291575563553526389862372999168 }, { target := 126, numerator := 11753856839066958065404215296 }, { target := 127, numerator := 1876470252015843934652462006272 }, { target := 129, numerator := 18724351277493331226109990141952 }, { target := 137, numerator := 1876470252015843934652462006272 }, { target := 144, numerator := 11752515686985823086163525632 }, { target := 145, numerator := 1040136578552732360722417188864 }, { target := 147, numerator := 39080603291318329747349069365248 }, { target := 150, numerator := 39077647542612515824898194538496 }, { target := 157, numerator := 1043092327258546283173292015616 }, { target := 216, numerator := 290749246559087038795138203648 }, { target := 218, numerator := 10924196106857060059428144807936 }, { target := 221, numerator := 10923369886794278346549595471872 }, { target := 228, numerator := 291575466621868751673687539712 }, { target := 327, numerator := 4403040192823285049894979502080 }, { target := 330, numerator := 15114867107222198960887361961984 }, { target := 332, numerator := 4403040192823285049894979502080 }, { target := 341, numerator := 102794712672917160697937264640 }, { target := 344, numerator := 352876274876782855117992886272 }, { target := 346, numerator := 102794712672917160697937264640 }, { target := 372, numerator := 853767196922284195796756725760 }, { target := 375, numerator := 2930833505226613157785552027648 }, { target := 377, numerator := 853767196922284195796756725760 }, { target := 386, numerator := 4403040192823285049894979502080 }, { target := 389, numerator := 15114867107222198960887361961984 }, { target := 391, numerator := 4403040192823285049894979502080 }, { target := 406, numerator := 91373077931481920620388679680 }, { target := 409, numerator := 313667799890473648993771454464 }, { target := 411, numerator := 91373077931481920620388679680 }, { target := 443, numerator := 102794712672917160697937264640 }, { target := 446, numerator := 352876274876782855117992886272 }, { target := 448, numerator := 102794712672917160697937264640 }, { target := 457, numerator := 102794712672917160697937264640 }, { target := 460, numerator := 352876274876782855117992886272 }, { target := 462, numerator := 102794712672917160697937264640 }, { target := 477, numerator := 108505530043634780736711557120 }, { target := 480, numerator := 372480512369937458180103602176 }, { target := 482, numerator := 108505530043634780736711557120 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3258914554561307901262036992 }, { target := 1, numerator := 274039654245363873676141789184 }, { target := 6, numerator := 274039588132233113501108797440 }, { target := 14, numerator := 3258980667692068076295028736 }, { target := 16, numerator := 1349722336974532292967923712 }, { target := 17, numerator := 196960394407303267412562935808 }, { target := 19, numerator := 2054965267356340668691434700800 }, { target := 27, numerator := 196960398862191961213419651072 }, { target := 34, numerator := 1349722336974532292967923712 }, { target := 35, numerator := 677823489612888997531484160 }, { target := 37, numerator := 24564547623940568170333470720 }, { target := 40, numerator := 24564556651315949241945292800 }, { target := 47, numerator := 677814462237507925919662080 }, { target := 51, numerator := 62388022932046236702736384 }, { target := 52, numerator := 6541271683436715706601701376 }, { target := 54, numerator := 70508370754092045265010688000 }, { target := 62, numerator := 6541276673280987645035413504 }, { target := 69, numerator := 62388022932046236702736384 }, { target := 70, numerator := 12065258115109424156060418048 }, { target := 72, numerator := 437248947706142113431935778816 }, { target := 75, numerator := 437249108393423896506626211840 }, { target := 82, numerator := 12065097427827641081369985024 }, { target := 96, numerator := 677823489612888997531484160 }, { target := 98, numerator := 24564547623940568170333470720 }, { target := 101, numerator := 24564556651315949241945292800 }, { target := 108, numerator := 677814462237507925919662080 }, { target := 126, numerator := 1294022863635940181456977920 }, { target := 127, numerator := 191120405085491929729959198720 }, { target := 129, numerator := 1992016019529674387983486156800 }, { target := 137, numerator := 191120405085491929729959198720 }, { target := 144, numerator := 1294022863635940181456977920 }, { target := 145, numerator := 10732205252204075794248499200 }, { target := 147, numerator := 388938670712392329363613286400 }, { target := 150, numerator := 388938813645835862997467136000 }, { target := 157, numerator := 10732062318760542160394649600 }, { target := 171, numerator := 18323828335868432566601121792 }, { target := 173, numerator := 664061604100526692871348158464 }, { target := 176, numerator := 664061848140574494507254415360 }, { target := 183, numerator := 18323584295820630930694864896 }, { target := 216, numerator := 677823489612888997531484160 }, { target := 218, numerator := 24564547623940568170333470720 }, { target := 221, numerator := 24564556651315949241945292800 }, { target := 228, numerator := 677814462237507925919662080 }, { target := 285, numerator := 18323828335868432566601121792 }, { target := 287, numerator := 664061604100526692871348158464 }, { target := 290, numerator := 664061848140574494507254415360 }, { target := 297, numerator := 18323584295820630930694864896 }, { target := 311, numerator := 18323828335868432566601121792 }, { target := 313, numerator := 664061604100526692871348158464 }, { target := 316, numerator := 664061848140574494507254415360 }, { target := 323, numerator := 18323584295820630930694864896 }, { target := 356, numerator := 12065258115109424156060418048 }, { target := 358, numerator := 437248947706142113431935778816 }, { target := 361, numerator := 437249108393423896506626211840 }, { target := 368, numerator := 12065097427827641081369985024 }, { target := 427, numerator := 677823489612888997531484160 }, { target := 429, numerator := 24564547623940568170333470720 }, { target := 432, numerator := 24564556651315949241945292800 }, { target := 439, numerator := 677814462237507925919662080 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 467537893636509224381972480 }, { target := 1, numerator := 39146543363495659572390002688 }, { target := 6, numerator := 39146557530595108181325643776 }, { target := 14, numerator := 467523726537060615446331392 }, { target := 126, numerator := 55699473338592111510945792 }, { target := 127, numerator := 5839989321811337682603737088 }, { target := 129, numerator := 62949247826666280707948544000 }, { target := 137, numerator := 5839993776700031483460452352 }, { target := 144, numerator := 55699473338592111510945792 }, { target := 266, numerator := 62388022932046236702736384 }, { target := 267, numerator := 6541271683436715706601701376 }, { target := 269, numerator := 70508370754092045265010688000 }, { target := 277, numerator := 6541276673280987645035413504 }, { target := 284, numerator := 62388022932046236702736384 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent1
