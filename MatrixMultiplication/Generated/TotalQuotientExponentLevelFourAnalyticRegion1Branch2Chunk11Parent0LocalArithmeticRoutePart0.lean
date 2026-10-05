import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk11Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent0

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
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 4573883969335341870401716224 }, { target := 38, numerator := 16636201942070127297329889280 }, { target := 40, numerator := 4573883969335341870401716224 }, { target := 61, numerator := 112133929570801929725977559040 }, { target := 64, numerator := 407855273418493443418410188800 }, { target := 66, numerator := 112133929570801929725977559040 }, { target := 71, numerator := 131840645617144900877832683520 }, { target := 73, numerator := 131840582750641097675680776192 }, { target := 75, numerator := 4573883969335341870401716224 }, { target := 78, numerator := 16636201942070127297329889280 }, { target := 80, numerator := 4573883969335341870401716224 }, { target := 85, numerator := 129093965500121048776211169280 }, { target := 87, numerator := 129093903943336074807437426688 }, { target := 89, numerator := 19265441861378730528117620736 }, { target := 106, numerator := 93985938337632670046641717248 }, { target := 109, numerator := 341847117325763583496746434560 }, { target := 111, numerator := 93985938337632670046641717248 }, { target := 116, numerator := 101627164329882527759996026880 }, { target := 118, numerator := 101627115870285846125003931648 }, { target := 130, numerator := 3194388976098739994185821061120 }, { target := 132, numerator := 3194387452895741595767015473152 }, { target := 134, numerator := 513745116303432814083136552960 }, { target := 135, numerator := 101627164329882527759996026880 }, { target := 137, numerator := 101627115870285846125003931648 }, { target := 139, numerator := 491268767465157628466999328768 }, { target := 150, numerator := 101627164329882527759996026880 }, { target := 152, numerator := 101627115870285846125003931648 }, { target := 154, numerator := 16054534884482275440098017280 }, { target := 155, numerator := 104373844446906379861617541120 }, { target := 157, numerator := 104373794677590868993247281152 }, { target := 159, numerator := 504112395372743448819077742592 }, { target := 160, numerator := 16054534884482275440098017280 }, { target := 187, numerator := 104373844446906379861617541120 }, { target := 189, numerator := 104373794677590868993247281152 }, { target := 201, numerator := 1766115315246336901342633656320 }, { target := 203, numerator := 1766114473097129704280473731072 }, { target := 205, numerator := 491268767465157628466999328768 }, { target := 206, numerator := 96133804095834823556752998400 }, { target := 208, numerator := 96133758255675800388517232640 }, { target := 210, numerator := 279348906989991592657705500672 }, { target := 221, numerator := 3194388976098739994185821061120 }, { target := 223, numerator := 3194387452895741595767015473152 }, { target := 225, numerator := 504112395372743448819077742592 }, { target := 226, numerator := 1766115315246336901342633656320 }, { target := 228, numerator := 1766114473097129704280473731072 }, { target := 230, numerator := 7869933000373211420736048070656 }, { target := 231, numerator := 308247069782059688449881931776 }, { target := 232, numerator := 131840645617144900877832683520 }, { target := 234, numerator := 131840582750641097675680776192 }, { target := 236, numerator := 513745116303432814083136552960 }, { target := 237, numerator := 491268767465157628466999328768 }, { target := 248, numerator := 101627164329882527759996026880 }, { target := 250, numerator := 101627115870285846125003931648 }, { target := 252, numerator := 16054534884482275440098017280 }, { target := 253, numerator := 96133804095834823556752998400 }, { target := 255, numerator := 96133758255675800388517232640 }, { target := 257, numerator := 308247069782059688449881931776 }, { target := 258, numerator := 16054534884482275440098017280 }, { target := 259, numerator := 129093965500121048776211169280 }, { target := 261, numerator := 129093903943336074807437426688 }, { target := 263, numerator := 494479674442054083555018932224 }, { target := 264, numerator := 279348906989991592657705500672 }, { target := 265, numerator := 19265441861378730528117620736 }]

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
    Slot4.Left0.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 96714065569170333976494080 }, { target := 1, numerator := 1624796301562061610805100544 }, { target := 2, numerator := 3520391986717800156744384512 }, { target := 3, numerator := 116056878683004400771792896 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 135399691796838467567091712 }, { target := 6, numerator := 3520391986717800156744384512 }, { target := 7, numerator := 3520391986717800156744384512 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 43443958253671314022241140736 }, { target := 10, numerator := 3481706360490132023153786880 }, { target := 11, numerator := 1624796301562061610805100544 }, { target := 12, numerator := 3520391986717800156744384512 }, { target := 13, numerator := 135399691796838467567091712 }, { target := 14, numerator := 3481706360490132023153786880 }, { target := 15, numerator := 135399691796838467567091712 }, { target := 16, numerator := 3520391986717800156744384512 }, { target := 17, numerator := 3520391986717800156744384512 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 19, numerator := 1306820384570796551438336000 }, { target := 21, numerator := 48259138219628999611514880000 }, { target := 24, numerator := 48259126402183577391333376000 }, { target := 31, numerator := 1306832202016218771619840000 }, { target := 45, numerator := 1297895757554215501818757120 }, { target := 47, numerator := 47929563617153484492216729600 }, { target := 50, numerator := 47929551880412567594514513920 }, { target := 57, numerator := 1297907494295132399520972800 }, { target := 71, numerator := 1441061835855054982322476548096 }, { target := 73, numerator := 1441061835855054982322476548096 }, { target := 89, numerator := 13639105819258729218680291328 }, { target := 90, numerator := 1306820384570796551438336000 }, { target := 92, numerator := 48259138219628999611514880000 }, { target := 95, numerator := 48259126402183577391333376000 }, { target := 102, numerator := 1306832202016218771619840000 }, { target := 116, numerator := 50433571386420610739250017599488 }, { target := 118, numerator := 50433571386420610739250017599488 }, { target := 120, numerator := 92362947251739484221660463104 }, { target := 123, numerator := 335943948894706441552532602880 }, { target := 125, numerator := 92362947251739484221660463104 }, { target := 134, numerator := 1430035646106150166453228142592 }, { target := 140, numerator := 4573883969335341870401716224 }, { target := 143, numerator := 16636201942070127297329889280 }, { target := 145, numerator := 4573883969335341870401716224 }, { target := 150, numerator := 50433596122176248010451646939136 }, { target := 152, numerator := 50433596122176248010451646939136 }, { target := 154, numerator := 15414354946077586649876791296000 }, { target := 161, numerator := 1310645224720759858418155520 }, { target := 163, numerator := 48400384477832791805499801600 }, { target := 166, numerator := 48400372625799724447112888320 }, { target := 173, numerator := 1310657076753827216805068800 }, { target := 177, numerator := 92510491895911592023931486208 }, { target := 180, numerator := 336480600570257090820188405760 }, { target := 182, numerator := 92510491895911592023931486208 }, { target := 191, numerator := 82920090024724584876314984448 }, { target := 194, numerator := 301598241659464888422561218560 }, { target := 196, numerator := 82920090024724584876314984448 }, { target := 211, numerator := 112133929570801929725977559040 }, { target := 214, numerator := 407855273418493443418410188800 }, { target := 216, numerator := 112133929570801929725977559040 }, { target := 236, numerator := 1430036736972807709341272506368 }, { target := 238, numerator := 4573883969335341870401716224 }, { target := 241, numerator := 16636201942070127297329889280 }, { target := 243, numerator := 4573883969335341870401716224 }, { target := 265, numerator := 13639105819258729218680291328 }]

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
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2018566108369664107303927808 }, { target := 1, numerator := 300605015218559193429204533248 }, { target := 3, numerator := 3118476499128398566171774812160 }, { target := 11, numerator := 300605015218559193429204533248 }, { target := 18, numerator := 2018542496537249759077859328 }, { target := 19, numerator := 592034366396450127746313486336 }, { target := 21, numerator := 21512999224910456216965204672512 }, { target := 24, numerator := 21512883933670513038731048386560 }, { target := 31, numerator := 592149657636393305980469772288 }, { target := 35, numerator := 18136628262566605915051171774464 }, { target := 38, numerator := 61619179320229389363142956417024 }, { target := 40, numerator := 18136628262566605915051171774464 }, { target := 71, numerator := 552613649229715454772151058432 }, { target := 73, numerator := 552613649229715454772151058432 }, { target := 89, numerator := 1975432012915132767922028544 }, { target := 90, numerator := 592014857722922741031669596160 }, { target := 92, numerator := 21512266233929671291454336532480 }, { target := 95, numerator := 21512150998127386705087741034496 }, { target := 102, numerator := 592130093525207327398265094144 }, { target := 106, numerator := 61574197002172799942544246964224 }, { target := 109, numerator := 209201671362690548813603813720064 }, { target := 111, numerator := 61574197002172799942544246964224 }, { target := 116, numerator := 20026901563850446235150890041344 }, { target := 118, numerator := 20026901563850446235150890041344 }, { target := 134, numerator := 294234335049042795771539226624 }, { target := 140, numerator := 18136627206453972243202298609664 }, { target := 143, numerator := 61619175694779380020221768105984 }, { target := 145, numerator := 18136627206453972243202298609664 }, { target := 150, numerator := 20026908923658609787492955586560 }, { target := 152, numerator := 20026908923658609787492955586560 }, { target := 154, numerator := 3052075965144076086572325273600 }, { target := 232, numerator := 1993655757398788249151747391488 }, { target := 234, numerator := 1993655757398788249151747391488 }, { target := 236, numerator := 294234335049042795771539226624 }, { target := 265, numerator := 1975408401082718419695960064 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot20.Left16.expected,
    Slot20.Left17.expected,
    Slot20.Left18.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 13225799582311494999932403712 }, { target := 1, numerator := 1386701232587781979591009107968 }, { target := 3, numerator := 14947253281044932508971433984000 }, { target := 11, numerator := 1386702290397874142391536975872 }, { target := 18, numerator := 13225799582311494999932403712 }, { target := 19, numerator := 1441612069469356263339018158080 }, { target := 21, numerator := 50452828191073692301197039370240 }, { target := 24, numerator := 50452852936274062538137959137280 }, { target := 31, numerator := 1441599696869171144868558274560 }, { target := 35, numerator := 3272373566025283819451659059200 }, { target := 38, numerator := 11188466934755855611245038141440 }, { target := 40, numerator := 3272372509043421642523074887680 }, { target := 71, numerator := 44450632396933966333497835520 }, { target := 72, numerator := 1297895757554215501818757120 }, { target := 73, numerator := 44431123723406579618853945344 }, { target := 74, numerator := 1310645224720759858418155520 }, { target := 89, numerator := 96714065569170333976494080 }, { target := 90, numerator := 1441612069469356263339018158080 }, { target := 92, numerator := 50452828191073692301197039370240 }, { target := 95, numerator := 50452852936274062538137959137280 }, { target := 102, numerator := 1441599696869171144868558274560 }, { target := 106, numerator := 11233486275296442224782511964160 }, { target := 109, numerator := 38408050675537346733376287014912 }, { target := 111, numerator := 11233482646862523409151100452864 }, { target := 116, numerator := 1669282988833973075406634352640 }, { target := 117, numerator := 47929563617153484492216729600 }, { target := 118, numerator := 1668549997853188149895766212608 }, { target := 119, numerator := 48400384477832791805499801600 }, { target := 134, numerator := 1624796301562061610805100544 }, { target := 139, numerator := 3520391986717800156744384512 }, { target := 140, numerator := 3272373566025283819451659059200 }, { target := 143, numerator := 11188466934755855611245038141440 }, { target := 145, numerator := 3272372509043421642523074887680 }, { target := 150, numerator := 1669160375553268992741505761280 }, { target := 151, numerator := 47929551880412567594514513920 }, { target := 152, numerator := 1668427440010142659098198409216 }, { target := 153, numerator := 48400372625799724447112888320 }, { target := 154, numerator := 116056878683004400771792896 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 135399691796838467567091712 }, { target := 205, numerator := 3520391986717800156744384512 }, { target := 210, numerator := 3520391986717800156744384512 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 230, numerator := 43443958253671314022241140736 }, { target := 231, numerator := 3481706360490132023153786880 }, { target := 232, numerator := 43266413475621830227006586880 }, { target := 234, numerator := 43246849364435851644801908736 }, { target := 236, numerator := 1624796301562061610805100544 }, { target := 237, numerator := 3520391986717800156744384512 }, { target := 252, numerator := 135399691796838467567091712 }, { target := 257, numerator := 3481706360490132023153786880 }, { target := 258, numerator := 135399691796838467567091712 }, { target := 263, numerator := 3520391986717800156744384512 }, { target := 264, numerator := 3520391986717800156744384512 }, { target := 265, numerator := 116056878683004400771792896 }]

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
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 129055279864670008605765795840 }, { target := 20, numerator := 126366628200822716759812341760 }, { target := 21, numerator := 99480111562349798300277800960 }, { target := 22, numerator := 3126901885054400416843867095040 }, { target := 23, numerator := 99480111562349798300277800960 }, { target := 24, numerator := 99480111562349798300277800960 }, { target := 25, numerator := 102168763226197090146231255040 }, { target := 26, numerator := 102168763226197090146231255040 }, { target := 27, numerator := 1728803019853808656948070973440 }, { target := 28, numerator := 94102808234655214608370892800 }, { target := 29, numerator := 3126901885054400416843867095040 }, { target := 30, numerator := 1728803019853808656948070973440 }, { target := 31, numerator := 129055279864670008605765795840 }, { target := 32, numerator := 99480111562349798300277800960 }, { target := 33, numerator := 94102808234655214608370892800 }, { target := 34, numerator := 126366628200822716759812341760 }, { target := 35, numerator := 4573883969335341870401716224 }, { target := 36, numerator := 112133929570801929725977559040 }, { target := 37, numerator := 4573883969335341870401716224 }, { target := 38, numerator := 93985938337632670046641717248 }, { target := 39, numerator := 92362947251739484221660463104 }, { target := 40, numerator := 4573883969335341870401716224 }, { target := 41, numerator := 92510491895911592023931486208 }, { target := 42, numerator := 82920090024724584876314984448 }, { target := 43, numerator := 112133929570801929725977559040 }, { target := 44, numerator := 4573883969335341870401716224 }, { target := 106, numerator := 16636201942070127297329889280 }, { target := 107, numerator := 407855273418493443418410188800 }, { target := 108, numerator := 16636201942070127297329889280 }, { target := 109, numerator := 341847117325763583496746434560 }, { target := 110, numerator := 335943948894706441552532602880 }, { target := 111, numerator := 16636201942070127297329889280 }, { target := 112, numerator := 336480600570257090820188405760 }, { target := 113, numerator := 301598241659464888422561218560 }, { target := 114, numerator := 407855273418493443418410188800 }, { target := 115, numerator := 16636201942070127297329889280 }, { target := 140, numerator := 4573883969335341870401716224 }, { target := 141, numerator := 112133929570801929725977559040 }, { target := 142, numerator := 4573883969335341870401716224 }, { target := 143, numerator := 93985938337632670046641717248 }, { target := 144, numerator := 92362947251739484221660463104 }, { target := 145, numerator := 4573883969335341870401716224 }, { target := 146, numerator := 92510491895911592023931486208 }, { target := 147, numerator := 82920090024724584876314984448 }, { target := 148, numerator := 112133929570801929725977559040 }, { target := 149, numerator := 4573883969335341870401716224 }, { target := 232, numerator := 1306832202016218771619840000 }, { target := 233, numerator := 1297907494295132399520972800 }, { target := 234, numerator := 1306832202016218771619840000 }, { target := 235, numerator := 1310657076753827216805068800 }]

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
    Slot23.Left2.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20077840012159761333520171008 }, { target := 1, numerator := 535409066990926968893871226880 }, { target := 2, numerator := 511984920310073914004764360704 }, { target := 3, numerator := 16731533343466467777933475840 }, { target := 4, numerator := 525370146984847088227111141376 }, { target := 5, numerator := 16731533343466467777933475840 }, { target := 6, numerator := 511984920310073914004764360704 }, { target := 7, numerator := 291128680176316539336042479616 }, { target := 8, numerator := 525370146984847088227111141376 }, { target := 9, numerator := 8201797644967262504742989856768 }, { target := 10, numerator := 321245440194556181336322736128 }, { target := 11, numerator := 535409066990926968893871226880 }, { target := 12, numerator := 511984920310073914004764360704 }, { target := 13, numerator := 16731533343466467777933475840 }, { target := 14, numerator := 321245440194556181336322736128 }, { target := 15, numerator := 16731533343466467777933475840 }, { target := 16, numerator := 515331226978767207560351055872 }, { target := 17, numerator := 291128680176316539336042479616 }, { target := 18, numerator := 20077840012159761333520171008 }, { target := 90, numerator := 129055218326331778710701604864 }, { target := 91, numerator := 126366567944533199987561988096 }, { target := 92, numerator := 99480064126547412756165820416 }, { target := 93, numerator := 3126900394031747055011374301184 }, { target := 94, numerator := 99480064126547412756165820416 }, { target := 95, numerator := 99480064126547412756165820416 }, { target := 96, numerator := 102168714508345991479305437184 }, { target := 97, numerator := 102168714508345991479305437184 }, { target := 98, numerator := 1728802195496486118978773581824 }, { target := 99, numerator := 94102763362950255309886586880 }, { target := 100, numerator := 3126900394031747055011374301184 }, { target := 101, numerator := 1728802195496486118978773581824 }, { target := 102, numerator := 129055218326331778710701604864 }, { target := 103, numerator := 99480064126547412756165820416 }, { target := 104, numerator := 94102763362950255309886586880 }, { target := 105, numerator := 126366567944533199987561988096 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent0
