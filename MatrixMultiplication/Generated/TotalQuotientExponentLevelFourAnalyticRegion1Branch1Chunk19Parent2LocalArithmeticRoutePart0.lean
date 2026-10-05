import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk19Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 4848963951020203731373260800 }, { target := 36, numerator := 96979279020404074627465216000 }, { target := 37, numerator := 5022141234985211007493734400 }, { target := 38, numerator := 90225364945768790858766745600 }, { target := 39, numerator := 135078281492705675373969408000 }, { target := 40, numerator := 4848963951020203731373260800 }, { target := 41, numerator := 135251458776670682650089881600 }, { target := 42, numerator := 135251458776670682650089881600 }, { target := 43, numerator := 96806101736439067351344742400 }, { target := 44, numerator := 5022141234985211007493734400 }, { target := 71, numerator := 1151700422382887772230778880 }, { target := 72, numerator := 1264982431141860339991183360 }, { target := 73, numerator := 1151700422382887772230778880 }, { target := 74, numerator := 1264982431141860339991183360 }, { target := 89, numerator := 273179456301043236321886208 }, { target := 106, numerator := 17380601356664355562297753600 }, { target := 107, numerator := 347612027133287111245955072000 }, { target := 108, numerator := 18001337119402368260951244800 }, { target := 109, numerator := 323403332386504615998468915200 }, { target := 110, numerator := 484173894935649904949723136000 }, { target := 111, numerator := 17380601356664355562297753600 }, { target := 112, numerator := 484794630698387917648376627200 }, { target := 113, numerator := 484794630698387917648376627200 }, { target := 114, numerator := 346991291370549098547301580800 }, { target := 115, numerator := 18001337119402368260951244800 }, { target := 116, numerator := 46044769201629177689711575040 }, { target := 117, numerator := 50573762893592703364109434880 }, { target := 118, numerator := 46044769201629177689711575040 }, { target := 119, numerator := 50573762893592703364109434880 }, { target := 134, numerator := 27432189120057906089198354432 }, { target := 139, numerator := 2978793219530446286476017664 }, { target := 150, numerator := 46044757949115292726885089280 }, { target := 151, numerator := 50573750534274173978709852160 }, { target := 152, numerator := 46044757949115292726885089280 }, { target := 153, numerator := 50573750534274173978709852160 }, { target := 154, numerator := 265196390209081758481037393920 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 210, numerator := 3094850098213450687247810560 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 3036821658871948486861914112 }, { target := 232, numerator := 1151700422382887772230778880 }, { target := 233, numerator := 1264982431141860339991183360 }, { target := 234, numerator := 1151700422382887772230778880 }, { target := 235, numerator := 1264982431141860339991183360 }, { target := 236, numerator := 27432189120057906089198354432 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 257, numerator := 3036821658871948486861914112 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 263, numerator := 2959450406416612219680718848 }, { target := 264, numerator := 3094850098213450687247810560 }, { target := 265, numerator := 273179456301043236321886208 }]

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
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 90872525175941988518379651072 }, { target := 20, numerator := 103493709228156153590376824832 }, { target := 21, numerator := 80775577934170656460781912064 }, { target := 22, numerator := 1082897591679975363177357508608 }, { target := 23, numerator := 95920998796827654547178520576 }, { target := 24, numerator := 80775577934170656460781912064 }, { target := 25, numerator := 95920998796827654547178520576 }, { target := 26, numerator := 93396761986384821532779085824 }, { target := 27, numerator := 3528883060999080554130409783296 }, { target := 28, numerator := 93396761986384821532779085824 }, { target := 29, numerator := 1082897591679975363177357508608 }, { target := 30, numerator := 3528883060999080554130409783296 }, { target := 31, numerator := 90872525175941988518379651072 }, { target := 32, numerator := 93396761986384821532779085824 }, { target := 33, numerator := 93396761986384821532779085824 }, { target := 34, numerator := 103493709228156153590376824832 }, { target := 35, numerator := 3980841183105324519007595790336 }, { target := 38, numerator := 14540095329488803847205185126400 }, { target := 40, numerator := 3980839841894938094402556395520 }, { target := 71, numerator := 52804151414634272061017554944 }, { target := 73, numerator := 52804151414634272061017554944 }, { target := 89, numerator := 953351345561723975740948480 }, { target := 90, numerator := 90872546841642903090248024064 }, { target := 91, numerator := 103493733902982195186115805184 }, { target := 92, numerator := 80775597192571469413553799168 }, { target := 93, numerator := 1082897849862911261825455620096 }, { target := 94, numerator := 95921021666178619928595136512 }, { target := 95, numerator := 80775597192571469413553799168 }, { target := 96, numerator := 95921021666178619928595136512 }, { target := 97, numerator := 93396784253910761509421580288 }, { target := 98, numerator := 3528883902350466070004631601152 }, { target := 99, numerator := 93396784253910761509421580288 }, { target := 100, numerator := 1082897849862911261825455620096 }, { target := 101, numerator := 3528883902350466070004631601152 }, { target := 102, numerator := 90872546841642903090248024064 }, { target := 103, numerator := 93396784253910761509421580288 }, { target := 104, numerator := 93396784253910761509421580288 }, { target := 105, numerator := 103493733902982195186115805184 }, { target := 106, numerator := 14787832958487257518188118671360 }, { target := 109, numerator := 54012830716656173161553854464000 }, { target := 111, numerator := 14787827976224905327673553715200 }, { target := 116, numerator := 2066548437902116257988226318336 }, { target := 118, numerator := 2066548437902116257988226318336 }, { target := 134, numerator := 307094831249705426496320962560 }, { target := 140, numerator := 3984853593374048702372796956672 }, { target := 141, numerator := 97007461033662684394946560000 }, { target := 142, numerator := 5023600660671817584738304000 }, { target := 143, numerator := 14627286239360053425459743948800 }, { target := 144, numerator := 135117535011173024692961280000 }, { target := 145, numerator := 3984852252445985620058219479040 }, { target := 146, numerator := 135290762620161708057952256000 }, { target := 147, numerator := 135290762620161708057952256000 }, { target := 148, numerator := 96834233424674001029955584000 }, { target := 149, numerator := 5023600660671817584738304000 }, { target := 150, numerator := 2066549195841936758566283116544 }, { target := 152, numerator := 2066549195841936758566283116544 }, { target := 154, numerator := 3266082672424587598689067859968 }, { target := 232, numerator := 52804909354454772639074353152 }, { target := 234, numerator := 52804909354454772639074353152 }, { target := 236, numerator := 307095756833536068946782846976 }, { target := 265, numerator := 953351345561723975740948480 }]

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
    Slot8.Left0.expected,
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
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14274996078009541294930526208 }, { target := 1, numerator := 214124941170143119423957893120 }, { target := 2, numerator := 375908230054251254099837190144 }, { target := 3, numerator := 14274996078009541294930526208 }, { target := 4, numerator := 237916601300159021582175436800 }, { target := 5, numerator := 14274996078009541294930526208 }, { target := 6, numerator := 375908230054251254099837190144 }, { target := 7, numerator := 373529064041249663884015435776 }, { target := 8, numerator := 237916601300159021582175436800 }, { target := 9, numerator := 5764719249502853092936110833664 }, { target := 10, numerator := 368770732015246483452371927040 }, { target := 11, numerator := 214124941170143119423957893120 }, { target := 12, numerator := 375908230054251254099837190144 }, { target := 13, numerator := 14274996078009541294930526208 }, { target := 14, numerator := 368770732015246483452371927040 }, { target := 15, numerator := 14274996078009541294930526208 }, { target := 16, numerator := 375908230054251254099837190144 }, { target := 17, numerator := 375908230054251254099837190144 }, { target := 18, numerator := 14274996078009541294930526208 }, { target := 19, numerator := 937737372863725147493039603712 }, { target := 21, numerator := 36576806521803090371763945603072 }, { target := 24, numerator := 36576793105558313198284223545344 }, { target := 31, numerator := 937741844945317538652946956288 }, { target := 35, numerator := 13166722936233669673443628417024 }, { target := 38, numerator := 47360310850640998137168419356672 }, { target := 40, numerator := 13166727328724123131203899359232 }, { target := 71, numerator := 1618284039733008600259161489408 }, { target := 73, numerator := 1618283979122271719064017567744 }, { target := 89, numerator := 29420872093323971081590013952 }, { target := 90, numerator := 937737149289739790987533746176 }, { target := 92, numerator := 36576797801213890945949636755456 }, { target := 95, numerator := 36576784384972312454105254592512 }, { target := 102, numerator := 937741621370265954935661133824 }, { target := 106, numerator := 47360310850640998137168419356672 }, { target := 109, numerator := 170353629732483115989524405026816 }, { target := 111, numerator := 47360326650298535682292104298496 }, { target := 116, numerator := 63210165604404097348413392158720 }, { target := 118, numerator := 63210163261329229910597202608128 }, { target := 134, numerator := 1992293921352458300865021739008 }, { target := 139, numerator := 378964394526237036653494403072 }, { target := 140, numerator := 13166727328724123131203899359232 }, { target := 143, numerator := 47360326650298535682292104298496 }, { target := 145, numerator := 13166731721216041947692925976576 }, { target := 150, numerator := 63210152209409971881121863958528 }, { target := 152, numerator := 63210149866338298058391433510912 }, { target := 154, numerator := 16872339870988935982830827077632 }, { target := 159, numerator := 239850882611542428261705318400 }, { target := 160, numerator := 14391052956692545695702319104 }, { target := 205, numerator := 378964394526237036653494403072 }, { target := 232, numerator := 1618288504731050422689670889472 }, { target := 234, numerator := 1618288444119249003132607266816 }, { target := 236, numerator := 1776429345372622695797952086016 }, { target := 265, numerator := 15029819136631425385887694848 }]

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
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
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
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14913308910766065499175387136 }, { target := 1, numerator := 1762657366327635463371894030336 }, { target := 3, numerator := 16727267044249047751575937744896 }, { target := 11, numerator := 1762658575253455078001068736512 }, { target := 18, numerator := 14913308910766065499175387136 }, { target := 19, numerator := 682031995337388614034590269440 }, { target := 21, numerator := 26691294890185700361610001907712 }, { target := 24, numerator := 26691294890185700361610001907712 }, { target := 31, numerator := 682031995337388614034590269440 }, { target := 35, numerator := 3956313510997466696955792982016 }, { target := 38, numerator := 14696718768971008242044014428160 }, { target := 40, numerator := 3955480711263078041547054252032 }, { target := 71, numerator := 90176183986854310445441875968 }, { target := 73, numerator := 90176205486534528353924284416 }, { target := 85, numerator := 102700653985028520229531025408 }, { target := 87, numerator := 102700678470775435069747101696 }, { target := 90, numerator := 682032157946507228695788257280 }, { target := 92, numerator := 26691301253887061072798489247744 }, { target := 95, numerator := 26691301253887061072798489247744 }, { target := 102, numerator := 682032157946507228695788257280 }, { target := 106, numerator := 14450507557896143318263686758400 }, { target := 109, numerator := 53680034470712512205536886784000 }, { target := 111, numerator := 14447465741613751922229824716800 }, { target := 116, numerator := 80156607988314942618170556416 }, { target := 118, numerator := 80156627099141802981266030592 }, { target := 130, numerator := 1074599525843347199474849021952 }, { target := 132, numerator := 1074599782047869796217597722624 }, { target := 135, numerator := 95185971986123994359077535744 }, { target := 137, numerator := 95185994680230891040253411328 }, { target := 140, numerator := 3956312178050853448103095173120 }, { target := 143, numerator := 14696713817406514044077290291200 }, { target := 145, numerator := 3955479378597048619628746506240 }, { target := 150, numerator := 80156607988314942618170556416 }, { target := 152, numerator := 80156627099141802981266030592 }, { target := 155, numerator := 95185971986123994359077535744 }, { target := 157, numerator := 95185994680230891040253411328 }, { target := 187, numerator := 92681077986489152402259705856 }, { target := 189, numerator := 92681100083382709697088847872 }, { target := 201, numerator := 3501841811489509055631326183424 }, { target := 203, numerator := 3501842646393757517744059711488 }, { target := 206, numerator := 92681077986489152402259705856 }, { target := 208, numerator := 92681100083382709697088847872 }, { target := 210, numerator := 376565885700121612370877349888 }, { target := 221, numerator := 1074599525843347199474849021952 }, { target := 223, numerator := 1074599782047869796217597722624 }, { target := 225, numerator := 239850882611542428261705318400 }, { target := 226, numerator := 3501841811489509055631326183424 }, { target := 228, numerator := 3501842646393757517744059711488 }, { target := 230, numerator := 5811586885677673036781119864832 }, { target := 231, numerator := 371768868047890763805643243520 }, { target := 232, numerator := 90176183986854310445441875968 }, { target := 234, numerator := 90176205486534528353924284416 }, { target := 236, numerator := 215865794350388185435534786560 }, { target := 237, numerator := 378964394526237036653494403072 }, { target := 248, numerator := 92681077986489152402259705856 }, { target := 250, numerator := 92681100083382709697088847872 }, { target := 252, numerator := 14391052956692545695702319104 }, { target := 253, numerator := 92681077986489152402259705856 }, { target := 255, numerator := 92681100083382709697088847872 }, { target := 257, numerator := 371768868047890763805643243520 }, { target := 258, numerator := 14391052956692545695702319104 }, { target := 263, numerator := 378964394526237036653494403072 }, { target := 264, numerator := 378964394526237036653494403072 }, { target := 265, numerator := 14391052956692545695702319104 }]

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
    Slot18.Left15.expected,
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot21.Left4.expected,
    Slot21.Left5.expected,
    Slot21.Left6.expected,
    Slot21.Left7.expected,
    Slot21.Left8.expected,
    Slot21.Left9.expected,
    Slot22.Left0.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1052105473451493996449759232 }, { target := 1, numerator := 314042471266632905927614791680 }, { target := 3, numerator := 3331218103317615231814349094912 }, { target := 11, numerator := 314043340182065753942334111744 }, { target := 18, numerator := 1052105473451493996449759232 }, { target := 19, numerator := 54449348579210003497369993216 }, { target := 21, numerator := 2131906743906568952107734401024 }, { target := 24, numerator := 2131907497677425292027432534016 }, { target := 31, numerator := 54450113602580228379894611968 }, { target := 35, numerator := 4848963951020203731373260800 }, { target := 38, numerator := 17380601356664355562297753600 }, { target := 40, numerator := 4850373051683134219747328000 }, { target := 45, numerator := 1264982431141860339991183360 }, { target := 47, numerator := 50573762893592703364109434880 }, { target := 50, numerator := 50573750534274173978709852160 }, { target := 57, numerator := 1264982431141860339991183360 }, { target := 61, numerator := 96979279020404074627465216000 }, { target := 64, numerator := 347612027133287111245955072000 }, { target := 66, numerator := 97007461033662684394946560000 }, { target := 75, numerator := 5022141234985211007493734400 }, { target := 78, numerator := 18001337119402368260951244800 }, { target := 80, numerator := 5023600660671817584738304000 }, { target := 90, numerator := 54449348579210003497369993216 }, { target := 92, numerator := 2131906743906568952107734401024 }, { target := 95, numerator := 2131907497677425292027432534016 }, { target := 102, numerator := 54450113602580228379894611968 }, { target := 106, numerator := 90225364945768790858766745600 }, { target := 109, numerator := 323403332386504615998468915200 }, { target := 111, numerator := 90251584283104033160298496000 }, { target := 120, numerator := 135078281492705675373969408000 }, { target := 123, numerator := 484173894935649904949723136000 }, { target := 125, numerator := 135117535011173024692961280000 }, { target := 140, numerator := 4848963951020203731373260800 }, { target := 143, numerator := 17380601356664355562297753600 }, { target := 145, numerator := 4850373051683134219747328000 }, { target := 177, numerator := 135251458776670682650089881600 }, { target := 180, numerator := 484794630698387917648376627200 }, { target := 182, numerator := 135290762620161708057952256000 }, { target := 191, numerator := 135251458776670682650089881600 }, { target := 194, numerator := 484794630698387917648376627200 }, { target := 196, numerator := 135290762620161708057952256000 }, { target := 211, numerator := 96806101736439067351344742400 }, { target := 214, numerator := 346991291370549098547301580800 }, { target := 216, numerator := 96834233424674001029955584000 }, { target := 238, numerator := 5022141234985211007493734400 }, { target := 241, numerator := 18001337119402368260951244800 }, { target := 243, numerator := 5023600660671817584738304000 }, { target := 259, numerator := 102700653985028520229531025408 }, { target := 261, numerator := 102700678470775435069747101696 }]

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
    Slot23.Left3.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 1682824740903563811190996992 }, { target := 2, numerator := 2978793219530446286476017664 }, { target := 3, numerator := 96714065569170333976494080 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 3094850098213450687247810560 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 3036821658871948486861914112 }, { target := 11, numerator := 1682824740903563811190996992 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 3036821658871948486861914112 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2959450406416612219680718848 }, { target := 17, numerator := 3094850098213450687247810560 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 161, numerator := 1264982431141860339991183360 }, { target := 163, numerator := 50573762893592703364109434880 }, { target := 166, numerator := 50573750534274173978709852160 }, { target := 173, numerator := 1264982431141860339991183360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent2
