import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 87; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent1

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
    Slot0.Left3.expected,
    Slot0.Left11.expected,
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
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 7961147191037750235170340864 }, { target := 36, numerator := 159222943820755004703406817280 }, { target := 37, numerator := 8245473876431955600712138752 }, { target := 38, numerator := 148134203090380995447276699648 }, { target := 39, numerator := 221774814607480185122602352640 }, { target := 40, numerator := 7961147191037750235170340864 }, { target := 41, numerator := 222059141292874390488144150528 }, { target := 42, numerator := 222059141292874390488144150528 }, { target := 43, numerator := 158938617135360799337865019392 }, { target := 44, numerator := 8245473876431955600712138752 }, { target := 71, numerator := 54124172233923982946463645696 }, { target := 72, numerator := 3616405813881932476141535232 }, { target := 73, numerator := 54124172233923982946463645696 }, { target := 74, numerator := 3616405813881932476141535232 }, { target := 89, numerator := 273491132488912632905990144 }, { target := 106, numerator := 29573677874574344850128240640 }, { target := 107, numerator := 591473557491486897002564812800 }, { target := 108, numerator := 30629880655809142880489963520 }, { target := 109, numerator := 550281649023329773818457620480 }, { target := 110, numerator := 823838169363142463682143846400 }, { target := 111, numerator := 29573677874574344850128240640 }, { target := 112, numerator := 824894372144377261712505569280 }, { target := 113, numerator := 824894372144377261712505569280 }, { target := 114, numerator := 590417354710252098972203089920 }, { target := 115, numerator := 30629880655809142880489963520 }, { target := 116, numerator := 2118151064441538737588903346176 }, { target := 117, numerator := 141532011883191081337102532608 }, { target := 118, numerator := 2118151064441538737588903346176 }, { target := 119, numerator := 141532011883191081337102532608 }, { target := 134, numerator := 69449954916970724299741593600 }, { target := 140, numerator := 7959471378125630017244233728 }, { target := 141, numerator := 159189427562512600344884674560 }, { target := 142, numerator := 8243738213058688232145813504 }, { target := 143, numerator := 148103021000123329963723063296 }, { target := 144, numerator := 221728131247785407623232225280 }, { target := 145, numerator := 7959471378125630017244233728 }, { target := 146, numerator := 222012398082718465838133805056 }, { target := 147, numerator := 222012398082718465838133805056 }, { target := 148, numerator := 158905160727579542129983094784 }, { target := 149, numerator := 8243738213058688232145813504 }, { target := 150, numerator := 2118151111702097054432774586368 }, { target := 151, numerator := 141532063792328904755780780032 }, { target := 152, numerator := 2118151111702097054432774586368 }, { target := 153, numerator := 141532063792328904755780780032 }, { target := 154, numerator := 732062744442260987835041447936 }, { target := 232, numerator := 54124219494482299790334885888 }, { target := 233, numerator := 3616457723019755894819782656 }, { target := 234, numerator := 54124219494482299790334885888 }, { target := 235, numerator := 3616457723019755894819782656 }, { target := 236, numerator := 69450106032698176128388431872 }, { target := 265, numerator := 273491132488912632905990144 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 81471938547679844149877538816 }, { target := 20, numerator := 92787485568190933615138308096 }, { target := 21, numerator := 72419500931270972577668923392 }, { target := 22, numerator := 970873934359851476119374004224 }, { target := 23, numerator := 85998157355884279935981846528 }, { target := 24, numerator := 72419500931270972577668923392 }, { target := 25, numerator := 85998157355884279935981846528 }, { target := 26, numerator := 83735047951782062042929692672 }, { target := 27, numerator := 3163826946934900614486911090688 }, { target := 28, numerator := 83735047951782062042929692672 }, { target := 29, numerator := 970873934359851476119374004224 }, { target := 30, numerator := 3163826946934900614486911090688 }, { target := 31, numerator := 81471938547679844149877538816 }, { target := 32, numerator := 83735047951782062042929692672 }, { target := 33, numerator := 83735047951782062042929692672 }, { target := 34, numerator := 92787485568190933615138308096 }, { target := 35, numerator := 2133655015346548615756703072256 }, { target := 38, numerator := 7793214020957313108179052134400 }, { target := 40, numerator := 2133654296483339559665317969920 }, { target := 71, numerator := 253495998118451305694623694848 }, { target := 73, numerator := 253496058556614189818604158976 }, { target := 89, numerator := 7782157732314271654877331456 }, { target := 90, numerator := 81471919123258334533719687168 }, { target := 91, numerator := 92787463445933103218958532608 }, { target := 92, numerator := 72419483665118519585528610816 }, { target := 93, numerator := 970873702885495153193492938752 }, { target := 94, numerator := 85998136852328242007815225344 }, { target := 95, numerator := 72419483665118519585528610816 }, { target := 96, numerator := 85998136852328242007815225344 }, { target := 97, numerator := 83735027987793288270767456256 }, { target := 98, numerator := 3163826192619865324392781185024 }, { target := 99, numerator := 83735027987793288270767456256 }, { target := 100, numerator := 970873702885495153193492938752 }, { target := 101, numerator := 3163826192619865324392781185024 }, { target := 102, numerator := 81471919123258334533719687168 }, { target := 103, numerator := 83735027987793288270767456256 }, { target := 104, numerator := 83735027987793288270767456256 }, { target := 105, numerator := 92787463445933103218958532608 }, { target := 106, numerator := 7674693639733195692916151943168 }, { target := 109, numerator := 28031959079385763747802067763200 }, { target := 111, numerator := 7674691054003610216841357557760 }, { target := 116, numerator := 9887708803707239791090926092288 }, { target := 118, numerator := 9887711161121004366601446752256 }, { target := 134, numerator := 285055867995073627419876261888 }, { target := 139, numerator := 161976717015246475343832285184 }, { target := 140, numerator := 2133655727145477724449231863808 }, { target := 143, numerator := 7793216620815938112411874099200 }, { target := 145, numerator := 2133655008282028851677689282560 }, { target := 150, numerator := 9887705176930213292767629541376 }, { target := 152, numerator := 9887707534343113177149695066112 }, { target := 154, numerator := 1835695847534938831069523214336 }, { target := 159, numerator := 102516909503320554015083724800 }, { target := 160, numerator := 6151014570199233240905023488 }, { target := 205, numerator := 161976717015246475343832285184 }, { target := 210, numerator := 160951547920213269803681447936 }, { target := 225, numerator := 102516909503320554015083724800 }, { target := 230, numerator := 2483984717265457023785478651904 }, { target := 232, numerator := 253497207044126805135722545152 }, { target := 234, numerator := 253497267482577919635854721024 }, { target := 236, numerator := 192790781668346649156366893056 }, { target := 265, numerator := 1631143162115038413972307968 }]

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
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot9.Left16.expected,
    Slot9.Left17.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 6383128327565242042448609280 }, { target := 1, numerator := 95746924913478630636729139200 }, { target := 2, numerator := 168089045959218040451146711040 }, { target := 3, numerator := 6383128327565242042448609280 }, { target := 4, numerator := 106385472126087367374143488000 }, { target := 5, numerator := 6383128327565242042448609280 }, { target := 6, numerator := 168089045959218040451146711040 }, { target := 7, numerator := 167025191237957166777405276160 }, { target := 8, numerator := 106385472126087367374143488000 }, { target := 9, numerator := 2577719989615096911475496714240 }, { target := 10, numerator := 164897481795435419429922406400 }, { target := 11, numerator := 95746924913478630636729139200 }, { target := 12, numerator := 168089045959218040451146711040 }, { target := 13, numerator := 6383128327565242042448609280 }, { target := 14, numerator := 164897481795435419429922406400 }, { target := 15, numerator := 6383128327565242042448609280 }, { target := 16, numerator := 168089045959218040451146711040 }, { target := 17, numerator := 168089045959218040451146711040 }, { target := 18, numerator := 6383128327565242042448609280 }, { target := 19, numerator := 253991107489776405901058506752 }, { target := 21, numerator := 9907020734964480493807900557312 }, { target := 24, numerator := 9907017101103905115605066317824 }, { target := 31, numerator := 253992318776634865302003253248 }, { target := 35, numerator := 2098594956408929272305301848064 }, { target := 38, numerator := 7548583650347908439746168225792 }, { target := 40, numerator := 2098595656511631846347953405952 }, { target := 71, numerator := 78686573127246345204582580224 }, { target := 73, numerator := 78686554366907622241968586752 }, { target := 85, numerator := 89615263839363893149663494144 }, { target := 87, numerator := 89615242473422569775575334912 }, { target := 90, numerator := 253991168045982576908093620224 }, { target := 92, numerator := 9907023096982568828254965202944 }, { target := 95, numerator := 9907019463121127070073815564288 }, { target := 102, numerator := 253992379333129829635143499776 }, { target := 106, numerator := 7665156513570690592316955033600 }, { target := 109, numerator := 27571340033480363874011892940800 }, { target := 111, numerator := 7665159070708633965024824524800 }, { target := 116, numerator := 69943620557552306848517849088 }, { target := 118, numerator := 69943603881695664215083188224 }, { target := 130, numerator := 937681663099685613687942414336 }, { target := 132, numerator := 937681439538982498383458992128 }, { target := 135, numerator := 83058049412093364382614945792 }, { target := 137, numerator := 83058029609513601255411286016 }, { target := 140, numerator := 2098594249358026468309315092480 }, { target := 143, numerator := 7548581107106837279005936189440 }, { target := 145, numerator := 2098594949460493166321483120640 }, { target := 150, numerator := 69943620557552306848517849088 }, { target := 152, numerator := 69943603881695664215083188224 }, { target := 155, numerator := 83058049412093364382614945792 }, { target := 157, numerator := 83058029609513601255411286016 }, { target := 187, numerator := 80872311269669854793598763008 }, { target := 189, numerator := 80872291988210611748689936384 }, { target := 201, numerator := 3055661923108066405444623532032 }, { target := 203, numerator := 3055661194581579330396446785536 }, { target := 231, numerator := 158901209730146858723379773440 }, { target := 236, numerator := 92265218552988498613575352320 }, { target := 237, numerator := 161976717015246475343832285184 }, { target := 252, numerator := 6151014570199233240905023488 }, { target := 257, numerator := 158901209730146858723379773440 }, { target := 258, numerator := 6151014570199233240905023488 }, { target := 263, numerator := 161976717015246475343832285184 }, { target := 264, numerator := 161976717015246475343832285184 }, { target := 265, numerator := 6151014570199233240905023488 }]

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
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected,
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1825591324413678925291454464 }, { target := 1, numerator := 243546719957831801477428936704 }, { target := 3, numerator := 2361468958774135668992364249088 }, { target := 11, numerator := 243546989132721325047206117376 }, { target := 18, numerator := 1825591324413678925291454464 }, { target := 19, numerator := 51818645475690688671016550400 }, { target := 21, numerator := 2027920620523748173159512145920 }, { target := 24, numerator := 2027920620523748173159512145920 }, { target := 31, numerator := 51818645475690688671016550400 }, { target := 35, numerator := 8150698314633887145531539456 }, { target := 38, numerator := 30277813062064210203702722560 }, { target := 40, numerator := 8148982601414335493845286912 }, { target := 61, numerator := 163013966292677742910630789120 }, { target := 64, numerator := 605556261241284204074054451200 }, { target := 66, numerator := 162979652028286709876905738240 }, { target := 75, numerator := 8441794683013668829300523008 }, { target := 78, numerator := 31359163528566503425263534080 }, { target := 80, numerator := 8440017694321990332911190016 }, { target := 90, numerator := 51818645475690688671016550400 }, { target := 92, numerator := 2027920620523748173159512145920 }, { target := 95, numerator := 2027920620523748173159512145920 }, { target := 102, numerator := 51818645475690688671016550400 }, { target := 106, numerator := 151661207925866257243640430592 }, { target := 109, numerator := 563383593047694768433182801920 }, { target := 111, numerator := 151629283404888171153335517184 }, { target := 120, numerator := 227055167336229713339807170560 }, { target := 123, numerator := 843453363871788712817432985600 }, { target := 125, numerator := 227007372467970774471404421120 }, { target := 140, numerator := 8150698314633887145531539456 }, { target := 143, numerator := 30277813062064210203702722560 }, { target := 145, numerator := 8148982601414335493845286912 }, { target := 177, numerator := 227346263704609495023576154112 }, { target := 180, numerator := 844534714338291006038993797120 }, { target := 182, numerator := 227298407560878429310470324224 }, { target := 191, numerator := 227346263704609495023576154112 }, { target := 194, numerator := 844534714338291006038993797120 }, { target := 196, numerator := 227298407560878429310470324224 }, { target := 206, numerator := 80872311269669854793598763008 }, { target := 208, numerator := 80872291988210611748689936384 }, { target := 211, numerator := 162722869924297961226861805568 }, { target := 214, numerator := 604474910774781910852493639680 }, { target := 216, numerator := 162688616935379055037839835136 }, { target := 221, numerator := 937681663099685613687942414336 }, { target := 223, numerator := 937681439538982498383458992128 }, { target := 226, numerator := 3055661923108066405444623532032 }, { target := 228, numerator := 3055661194581579330396446785536 }, { target := 232, numerator := 78686573127246345204582580224 }, { target := 234, numerator := 78686554366907622241968586752 }, { target := 238, numerator := 8441794683013668829300523008 }, { target := 241, numerator := 31359163528566503425263534080 }, { target := 243, numerator := 8440017694321990332911190016 }, { target := 248, numerator := 80872311269669854793598763008 }, { target := 250, numerator := 80872291988210611748689936384 }, { target := 253, numerator := 80872311269669854793598763008 }, { target := 255, numerator := 80872291988210611748689936384 }, { target := 259, numerator := 89615263839363893149663494144 }, { target := 261, numerator := 89615242473422569775575334912 }]

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
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 117841933213529126662569984 }, { target := 1, numerator := 19312023284365756708505518080 }, { target := 3, numerator := 198824757107634441110295674880 }, { target := 11, numerator := 19312023284365756708505518080 }, { target := 18, numerator := 117841933213529126662569984 }, { target := 19, numerator := 3527730618019155880244674560 }, { target := 21, numerator := 138061610738933730728623472640 }, { target := 24, numerator := 138061661375246213061342658560 }, { target := 31, numerator := 3527781254331638212963860480 }, { target := 45, numerator := 3874720514873499081580216320 }, { target := 47, numerator := 151641441303419015718324142080 }, { target := 50, numerator := 151641496920352397952622264320 }, { target := 57, numerator := 3874776131806881315878338560 }, { target := 90, numerator := 3527730618019155880244674560 }, { target := 92, numerator := 138061610738933730728623472640 }, { target := 95, numerator := 138061661375246213061342658560 }, { target := 102, numerator := 3527781254331638212963860480 }, { target := 161, numerator := 3874720514873499081580216320 }, { target := 163, numerator := 151641441303419015718324142080 }, { target := 166, numerator := 151641496920352397952622264320 }, { target := 173, numerator := 3874776131806881315878338560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent1
