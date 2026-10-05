import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3

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
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 22975676181217987211059789824 }, { target := 134, numerator := 77881337192329721201383440384 }, { target := 136, numerator := 22975676181217987211059789824 }, { target := 227, numerator := 612684698165812992294927728640 }, { target := 230, numerator := 2076835658462125898703558410240 }, { target := 232, numerator := 612684698165812992294927728640 }, { target := 253, numerator := 585879742621058673882024640512 }, { target := 256, numerator := 1985974098404407890635277729792 }, { target := 258, numerator := 585879742621058673882024640512 }, { target := 263, numerator := 16924961474604808445886464000 }, { target := 265, numerator := 16924961474604808445886464000 }, { target := 302, numerator := 19146396817681656009216491520 }, { target := 305, numerator := 64901114326941434334486200320 }, { target := 307, numerator := 19146396817681656009216491520 }, { target := 328, numerator := 601196860075203998689397833728 }, { target := 331, numerator := 2037894989865961038102866690048 }, { target := 333, numerator := 601196860075203998689397833728 }, { target := 338, numerator := 17408531802450660115768934400 }, { target := 340, numerator := 17408531802450660115768934400 }, { target := 342, numerator := 19146396817681656009216491520 }, { target := 345, numerator := 64901114326941434334486200320 }, { target := 347, numerator := 19146396817681656009216491520 }, { target := 352, numerator := 16924961474604808445886464000 }, { target := 354, numerator := 16924961474604808445886464000 }, { target := 443, numerator := 585879742621058673882024640512 }, { target := 446, numerator := 1985974098404407890635277729792 }, { target := 448, numerator := 585879742621058673882024640512 }, { target := 469, numerator := 333147304627660814560366952448 }, { target := 472, numerator := 1129279389288780957420059885568 }, { target := 474, numerator := 333147304627660814560366952448 }, { target := 479, numerator := 14990680163221401766356582400 }, { target := 481, numerator := 14990680163221401766356582400 }, { target := 518, numerator := 601196860075203998689397833728 }, { target := 521, numerator := 2037894989865961038102866690048 }, { target := 523, numerator := 601196860075203998689397833728 }, { target := 544, numerator := 9385563720027547775717924143104 }, { target := 547, numerator := 31814526243066691110765135396864 }, { target := 549, numerator := 9385563720027547775717924143104 }, { target := 554, numerator := 701660545704330772999464550400 }, { target := 556, numerator := 701660545704330772999464550400 }, { target := 568, numerator := 191010279499111409603575808000 }, { target := 570, numerator := 191010279499111409603575808000 }, { target := 599, numerator := 17408531802450660115768934400 }, { target := 601, numerator := 17408531802450660115768934400 }, { target := 613, numerator := 701660545704330772999464550400 }, { target := 615, numerator := 701660545704330772999464550400 }, { target := 618, numerator := 16924961474604808445886464000 }, { target := 620, numerator := 16924961474604808445886464000 }, { target := 694, numerator := 16924961474604808445886464000 }, { target := 696, numerator := 16924961474604808445886464000 }, { target := 708, numerator := 14507109835375550096474112000 }, { target := 710, numerator := 14507109835375550096474112000 }, { target := 739, numerator := 16924961474604808445886464000 }, { target := 741, numerator := 16924961474604808445886464000 }, { target := 753, numerator := 191010279499111409603575808000 }, { target := 755, numerator := 191010279499111409603575808000 }, { target := 758, numerator := 14507109835375550096474112000 }, { target := 760, numerator := 14507109835375550096474112000 }, { target := 773, numerator := 16924961474604808445886464000 }, { target := 775, numerator := 16924961474604808445886464000 }, { target := 778, numerator := 14990680163221401766356582400 }, { target := 780, numerator := 14990680163221401766356582400 }]

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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7591623083664356772352622592 }, { target := 82, numerator := 275122933388134363507734872064 }, { target := 85, numerator := 275123034494738631509787279360 }, { target := 92, numerator := 7591521977060088770300215296 }, { target := 115, numerator := 7433464269421349339595276288 }, { target := 117, numerator := 269391205609214897601323728896 }, { target := 120, numerator := 269391304609431576686666711040 }, { target := 127, numerator := 7433365269204670254252294144 }, { target := 176, numerator := 5851876126991275012021813248 }, { target := 178, numerator := 212073927820020238537212297216 }, { target := 181, numerator := 212074005756361028455461027840 }, { target := 188, numerator := 5851798190650485093773082624 }, { target := 211, numerator := 183938700964617644296793751552 }, { target := 213, numerator := 6665999406883338849156159504384 }, { target := 216, numerator := 6666001856612104759289220956160 }, { target := 223, numerator := 183936251235851734163732299776 }, { target := 237, numerator := 5851876126991275012021813248 }, { target := 239, numerator := 212073927820020238537212297216 }, { target := 242, numerator := 212074005756361028455461027840 }, { target := 249, numerator := 5851798190650485093773082624 }, { target := 286, numerator := 5851876126991275012021813248 }, { target := 288, numerator := 212073927820020238537212297216 }, { target := 291, numerator := 212074005756361028455461027840 }, { target := 298, numerator := 5851798190650485093773082624 }, { target := 312, numerator := 6010034941234282444779159552 }, { target := 314, numerator := 217805655598939704443623440384 }, { target := 317, numerator := 217805735641668083278581596160 }, { target := 324, numerator := 6009954898505903609821003776 }, { target := 392, numerator := 6010034941234282444779159552 }, { target := 394, numerator := 217805655598939704443623440384 }, { target := 397, numerator := 217805735641668083278581596160 }, { target := 404, numerator := 6009954898505903609821003776 }, { target := 427, numerator := 101696117558253779262973673472 }, { target := 429, numerator := 3685500961845216577822365057024 }, { target := 432, numerator := 3685502316252436251266525429760 }, { target := 439, numerator := 101694763151034105818813300736 }, { target := 558, numerator := 367610818899487795376956637184 }, { target := 561, numerator := 1246101395077275539222135046144 }, { target := 563, numerator := 367610818899487795376956637184 }, { target := 589, numerator := 612684698165812992294927728640 }, { target := 592, numerator := 2076835658462125898703558410240 }, { target := 594, numerator := 612684698165812992294927728640 }, { target := 603, numerator := 585879742621058673882024640512 }, { target := 606, numerator := 1985974098404407890635277729792 }, { target := 608, numerator := 585879742621058673882024640512 }, { target := 658, numerator := 19146396817681656009216491520 }, { target := 661, numerator := 64901114326941434334486200320 }, { target := 663, numerator := 19146396817681656009216491520 }, { target := 684, numerator := 367610818899487795376956637184 }, { target := 687, numerator := 1246101395077275539222135046144 }, { target := 689, numerator := 367610818899487795376956637184 }, { target := 698, numerator := 19146396817681656009216491520 }, { target := 701, numerator := 64901114326941434334486200320 }, { target := 703, numerator := 19146396817681656009216491520 }, { target := 729, numerator := 589709021984595005083867938816 }, { target := 732, numerator := 1998954321269796177502174969856 }, { target := 734, numerator := 589709021984595005083867938816 }, { target := 743, numerator := 333147304627660814560366952448 }, { target := 746, numerator := 1129279389288780957420059885568 }, { target := 748, numerator := 333147304627660814560366952448 }, { target := 763, numerator := 22975676181217987211059789824 }, { target := 766, numerator := 77881337192329721201383440384 }, { target := 768, numerator := 22975676181217987211059789824 }]

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
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 13384627764333333094334464 }, { target := 27, numerator := 1976839476429526714573389824 }, { target := 29, numerator := 20604267259295378801489346560 }, { target := 37, numerator := 1976839476429526714573389824 }, { target := 44, numerator := 13384627764333333094334464 }, { target := 61, numerator := 328139261319139779086909440 }, { target := 62, numerator := 48464451680207751712121815040 }, { target := 64, numerator := 505136874744015738359093657600 }, { target := 72, numerator := 48464451680207751712121815040 }, { target := 79, numerator := 328139261319139779086909440 }, { target := 96, numerator := 13384627764333333094334464 }, { target := 97, numerator := 1976839476429526714573389824 }, { target := 99, numerator := 20604267259295378801489346560 }, { target := 107, numerator := 1976839476429526714573389824 }, { target := 114, numerator := 13384627764333333094334464 }, { target := 157, numerator := 275032512447752683261001728 }, { target := 158, numerator := 40620862789858339263975784448 }, { target := 160, numerator := 423384459489392138598345605120 }, { target := 168, numerator := 40620862789858339263975784448 }, { target := 175, numerator := 275032512447752683261001728 }, { target := 192, numerator := 270283128402344081195270144 }, { target := 193, numerator := 39919403620802700752352968704 }, { target := 195, numerator := 416073267881255068701042933760 }, { target := 203, numerator := 39919403620802700752352968704 }, { target := 210, numerator := 270283128402344081195270144 }, { target := 267, numerator := 13384627764333333094334464 }, { target := 268, numerator := 1976839476429526714573389824 }, { target := 270, numerator := 20604267259295378801489346560 }, { target := 278, numerator := 1976839476429526714573389824 }, { target := 285, numerator := 13384627764333333094334464 }, { target := 373, numerator := 270714890588290317746700288 }, { target := 374, numerator := 39983172636171395162500497408 }, { target := 376, numerator := 416737921663812984146252267520 }, { target := 384, numerator := 39983172636171395162500497408 }, { target := 391, numerator := 270714890588290317746700288 }, { target := 453, numerator := 5535558498505260146507120640 }, { target := 455, numerator := 200610472262181306724390010880 }, { target := 458, numerator := 200610545985746918809219891200 }, { target := 465, numerator := 5535484774939648061677240320 }, { target := 502, numerator := 183938700964617644296793751552 }, { target := 504, numerator := 6665999406883338849156159504384 }, { target := 507, numerator := 6666001856612104759289220956160 }, { target := 514, numerator := 183936251235851734163732299776 }, { target := 528, numerator := 101696117558253779262973673472 }, { target := 530, numerator := 3685500961845216577822365057024 }, { target := 533, numerator := 3685502316252436251266525429760 }, { target := 540, numerator := 101694763151034105818813300736 }, { target := 573, numerator := 7591623083664356772352622592 }, { target := 575, numerator := 275122933388134363507734872064 }, { target := 578, numerator := 275123034494738631509787279360 }, { target := 585, numerator := 7591521977060088770300215296 }, { target := 642, numerator := 5851876126991275012021813248 }, { target := 644, numerator := 212073927820020238537212297216 }, { target := 647, numerator := 212074005756361028455461027840 }, { target := 654, numerator := 5851798190650485093773082624 }, { target := 668, numerator := 5535558498505260146507120640 }, { target := 670, numerator := 200610472262181306724390010880 }, { target := 673, numerator := 200610545985746918809219891200 }, { target := 680, numerator := 5535484774939648061677240320 }, { target := 713, numerator := 7433464269421349339595276288 }, { target := 715, numerator := 269391205609214897601323728896 }, { target := 718, numerator := 269391304609431576686666711040 }, { target := 725, numerator := 7433365269204670254252294144 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
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
    Slot10.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 116503467439499881375334400 }, { target := 11, numerator := 9796688253400459351215308800 }, { target := 16, numerator := 9796685889911374907179008000 }, { target := 24, numerator := 116505830928584325411635200 }, { target := 45, numerator := 115707834003327687063502848 }, { target := 46, numerator := 9729784040938212311743594496 }, { target := 51, numerator := 9729781693590028932203151360 }, { target := 59, numerator := 115710181351511066603945984 }, { target := 80, numerator := 35828799079466660313060868096 }, { target := 82, numerator := 1253918639092841909583754559488 }, { target := 85, numerator := 1253919254092418441090628059136 }, { target := 92, numerator := 35828491579678394559624118272 }, { target := 131, numerator := 5240762035336967878271303680 }, { target := 134, numerator := 17918520475189052853060632576 }, { target := 136, numerator := 5240760342562502014058627072 }, { target := 141, numerator := 116503467439499881375334400 }, { target := 142, numerator := 9796688253400459351215308800 }, { target := 147, numerator := 9796685889911374907179008000 }, { target := 155, numerator := 116505830928584325411635200 }, { target := 176, numerator := 1253918639092841909583754559488 }, { target := 178, numerator := 43884026086867375281233213784064 }, { target := 181, numerator := 43884047610319231333241462980608 }, { target := 188, numerator := 1253907877366913883579629961216 }, { target := 227, numerator := 549484447338865225952154091520 }, { target := 230, numerator := 1878724554568776101653657944064 }, { target := 232, numerator := 549484269854515512498095915008 }, { target := 263, numerator := 1870574490664767660962611200 }, { target := 265, numerator := 1869728658427306134093168640 }, { target := 302, numerator := 5922893133253987641600245760000 }, { target := 305, numerator := 20250772915268296625495212032000 }, { target := 307, numerator := 5922891220150093129401237504000 }, { target := 338, numerator := 156621583854735922394006814720 }, { target := 340, numerator := 156550763053229354185113206784 }, { target := 357, numerator := 116844453197859393223262208 }, { target := 358, numerator := 9825361487312850939560329216 }, { target := 363, numerator := 9825359116906237467882946560 }, { target := 371, numerator := 116846823604472864900644864 }, { target := 408, numerator := 242650348501784941903740928 }, { target := 409, numerator := 35838186637206258502911131648 }, { target := 411, numerator := 373535425797548480207645573120 }, { target := 419, numerator := 35838186637206258502911131648 }, { target := 426, numerator := 242650348501784941903740928 }, { target := 483, numerator := 328139261319139779086909440 }, { target := 484, numerator := 48464451680207751712121815040 }, { target := 486, numerator := 505136874744015738359093657600 }, { target := 494, numerator := 48464451680207751712121815040 }, { target := 501, numerator := 328139261319139779086909440 }, { target := 589, numerator := 549484866499229565468100526080 }, { target := 592, numerator := 1878725987706461072384910688256 }, { target := 594, numerator := 549484689014744462550244524032 }, { target := 599, numerator := 156621640535948709569432125440 }, { target := 601, numerator := 156550819708812155881173024768 }, { target := 623, numerator := 13384627764333333094334464 }, { target := 624, numerator := 1976839476429526714573389824 }, { target := 626, numerator := 20604267259295378801489346560 }, { target := 634, numerator := 1976839476429526714573389824 }, { target := 641, numerator := 13384627764333333094334464 }, { target := 763, numerator := 5240762035336967878271303680 }, { target := 766, numerator := 17918520475189052853060632576 }, { target := 768, numerator := 5240760342562502014058627072 }, { target := 773, numerator := 1870517809451980485537300480 }, { target := 775, numerator := 1869672002844504438033350656 }]

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
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left6.expected,
    Slot15.Left14.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1870574490664767660962611200 }, { target := 11, numerator := 156621583854735922394006814720 }, { target := 16, numerator := 156621640535948709569432125440 }, { target := 24, numerator := 1870517809451980485537300480 }, { target := 26, numerator := 5251657590503988601510952960 }, { target := 27, numerator := 550626826647262035153717821440 }, { target := 29, numerator := 5935206840391729819649310720000 }, { target := 37, numerator := 550627246679061643566786805760 }, { target := 44, numerator := 5251657590503988601510952960 }, { target := 131, numerator := 13384627764333333094334464 }, { target := 132, numerator := 328139261319139779086909440 }, { target := 133, numerator := 13384627764333333094334464 }, { target := 134, numerator := 275032512447752683261001728 }, { target := 135, numerator := 270283128402344081195270144 }, { target := 136, numerator := 13384627764333333094334464 }, { target := 137, numerator := 270714890588290317746700288 }, { target := 138, numerator := 242650348501784941903740928 }, { target := 139, numerator := 328139261319139779086909440 }, { target := 140, numerator := 13384627764333333094334464 }, { target := 141, numerator := 1869728658427306134093168640 }, { target := 142, numerator := 156550763053229354185113206784 }, { target := 147, numerator := 156550819708812155881173024768 }, { target := 155, numerator := 1869672002844504438033350656 }, { target := 157, numerator := 17955773116509612214501507072 }, { target := 158, numerator := 1882630426823596841989736235008 }, { target := 160, numerator := 20292874314260538406421397504000 }, { target := 168, numerator := 1882631862940778039271365804032 }, { target := 175, numerator := 17955773116509612214501507072 }, { target := 263, numerator := 116503467439499881375334400 }, { target := 264, numerator := 115707834003327687063502848 }, { target := 265, numerator := 116503467439499881375334400 }, { target := 266, numerator := 116844453197859393223262208 }, { target := 267, numerator := 5251655894210241103484944384 }, { target := 268, numerator := 550626648793921989655056613376 }, { target := 270, numerator := 5935204923310488333412466688000 }, { target := 278, numerator := 550627068825585927129351061504 }, { target := 285, numerator := 5251655894210241103484944384 }, { target := 286, numerator := 1253919254092418441090628059136 }, { target := 288, numerator := 43884047610319231333241462980608 }, { target := 291, numerator := 43884069133781643822776268619776 }, { target := 298, numerator := 1253908492361212196323225239552 }, { target := 338, numerator := 9796688253400459351215308800 }, { target := 339, numerator := 9729784040938212311743594496 }, { target := 340, numerator := 9796688253400459351215308800 }, { target := 341, numerator := 9825361487312850939560329216 }, { target := 573, numerator := 35828491579678394559624118272 }, { target := 575, numerator := 1253907877366913883579629961216 }, { target := 578, numerator := 1253908492361212196323225239552 }, { target := 585, numerator := 35828184082529238187826479104 }, { target := 599, numerator := 9796685889911374907179008000 }, { target := 600, numerator := 9729781693590028932203151360 }, { target := 601, numerator := 9796685889911374907179008000 }, { target := 602, numerator := 9825359116906237467882946560 }, { target := 773, numerator := 116505830928584325411635200 }, { target := 774, numerator := 115710181351511066603945984 }, { target := 775, numerator := 116505830928584325411635200 }, { target := 776, numerator := 116846823604472864900644864 }]

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
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7504363048219938878417534976 }, { target := 81, numerator := 7348022151382023485117169664 }, { target := 82, numerator := 5784613183002869552113516544 }, { target := 83, numerator := 181824463022495602408324857856 }, { target := 84, numerator := 5784613183002869552113516544 }, { target := 85, numerator := 5784613183002869552113516544 }, { target := 86, numerator := 5940954079840784945413881856 }, { target := 87, numerator := 5940954079840784945413881856 }, { target := 88, numerator := 100527196666779597892134895616 }, { target := 89, numerator := 5471931389327038765512785920 }, { target := 90, numerator := 181824463022495602408324857856 }, { target := 91, numerator := 100527196666779597892134895616 }, { target := 92, numerator := 7504363048219938878417534976 }, { target := 93, numerator := 5784613183002869552113516544 }, { target := 94, numerator := 5471931389327038765512785920 }, { target := 95, numerator := 7348022151382023485117169664 }, { target := 227, numerator := 1976839476429526714573389824 }, { target := 228, numerator := 48464451680207751712121815040 }, { target := 229, numerator := 1976839476429526714573389824 }, { target := 230, numerator := 40620862789858339263975784448 }, { target := 231, numerator := 39919403620802700752352968704 }, { target := 232, numerator := 1976839476429526714573389824 }, { target := 233, numerator := 39983172636171395162500497408 }, { target := 234, numerator := 35838186637206258502911131648 }, { target := 235, numerator := 48464451680207751712121815040 }, { target := 236, numerator := 1976839476429526714573389824 }, { target := 302, numerator := 20604267259295378801489346560 }, { target := 303, numerator := 505136874744015738359093657600 }, { target := 304, numerator := 20604267259295378801489346560 }, { target := 305, numerator := 423384459489392138598345605120 }, { target := 306, numerator := 416073267881255068701042933760 }, { target := 307, numerator := 20604267259295378801489346560 }, { target := 308, numerator := 416737921663812984146252267520 }, { target := 309, numerator := 373535425797548480207645573120 }, { target := 310, numerator := 505136874744015738359093657600 }, { target := 311, numerator := 20604267259295378801489346560 }, { target := 589, numerator := 1976839476429526714573389824 }, { target := 590, numerator := 48464451680207751712121815040 }, { target := 591, numerator := 1976839476429526714573389824 }, { target := 592, numerator := 40620862789858339263975784448 }, { target := 593, numerator := 39919403620802700752352968704 }, { target := 594, numerator := 1976839476429526714573389824 }, { target := 595, numerator := 39983172636171395162500497408 }, { target := 596, numerator := 35838186637206258502911131648 }, { target := 597, numerator := 48464451680207751712121815040 }, { target := 598, numerator := 1976839476429526714573389824 }, { target := 763, numerator := 13384627764333333094334464 }, { target := 764, numerator := 328139261319139779086909440 }, { target := 765, numerator := 13384627764333333094334464 }, { target := 766, numerator := 275032512447752683261001728 }, { target := 767, numerator := 270283128402344081195270144 }, { target := 768, numerator := 13384627764333333094334464 }, { target := 769, numerator := 270714890588290317746700288 }, { target := 770, numerator := 242650348501784941903740928 }, { target := 771, numerator := 328139261319139779086909440 }, { target := 772, numerator := 13384627764333333094334464 }]

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
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 176, numerator := 271960600820454658180059758592 }, { target := 177, numerator := 266294754970028519467975180288 }, { target := 178, numerator := 209636296465767132347129397248 }, { target := 179, numerator := 6589378724045599322154364567552 }, { target := 180, numerator := 209636296465767132347129397248 }, { target := 181, numerator := 209636296465767132347129397248 }, { target := 182, numerator := 215302142316193271059213975552 }, { target := 183, numerator := 215302142316193271059213975552 }, { target := 184, numerator := 3643138881824007191870383849472 }, { target := 185, numerator := 198304604764914854922960240640 }, { target := 186, numerator := 6589378724045599322154364567552 }, { target := 187, numerator := 3643138881824007191870383849472 }, { target := 188, numerator := 271960600820454658180059758592 }, { target := 189, numerator := 209636296465767132347129397248 }, { target := 190, numerator := 198304604764914854922960240640 }, { target := 191, numerator := 266294754970028519467975180288 }, { target := 286, numerator := 271960700764914049538410414080 }, { target := 287, numerator := 266294852832311673506360197120 }, { target := 288, numerator := 209636373506287913185858027520 }, { target := 289, numerator := 6589381145616563325274402324480 }, { target := 290, numerator := 209636373506287913185858027520 }, { target := 291, numerator := 209636373506287913185858027520 }, { target := 292, numerator := 215302221438890289217908244480 }, { target := 293, numerator := 215302221438890289217908244480 }, { target := 294, numerator := 3643140220663327788608289505280 }, { target := 295, numerator := 198304677641083161121757593600 }, { target := 296, numerator := 6589381145616563325274402324480 }, { target := 297, numerator := 3643140220663327788608289505280 }, { target := 298, numerator := 271960700764914049538410414080 }, { target := 299, numerator := 209636373506287913185858027520 }, { target := 300, numerator := 198304677641083161121757593600 }, { target := 301, numerator := 266294852832311673506360197120 }, { target := 573, numerator := 7504263103760547520066879488 }, { target := 574, numerator := 7347924289098869446732152832 }, { target := 575, numerator := 5784536142482088713384886272 }, { target := 576, numerator := 181822041451531599288287100928 }, { target := 577, numerator := 5784536142482088713384886272 }, { target := 578, numerator := 5784536142482088713384886272 }, { target := 579, numerator := 5940874957143766786719612928 }, { target := 580, numerator := 5940874957143766786719612928 }, { target := 581, numerator := 100525857827459001154229239808 }, { target := 582, numerator := 5471858513158732566715432960 }, { target := 583, numerator := 181822041451531599288287100928 }, { target := 584, numerator := 100525857827459001154229239808 }, { target := 585, numerator := 7504263103760547520066879488 }, { target := 586, numerator := 5784536142482088713384886272 }, { target := 587, numerator := 5471858513158732566715432960 }, { target := 588, numerator := 7347924289098869446732152832 }]

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
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 22911077279115218737176772608 }, { target := 27, numerator := 610962060776405832991380602880 }, { target := 28, numerator := 584232470617438077798007701504 }, { target := 29, numerator := 19092564399262682280980643840 }, { target := 30, numerator := 599506522136848223622792216576 }, { target := 31, numerator := 19092564399262682280980643840 }, { target := 32, numerator := 584232470617438077798007701504 }, { target := 33, numerator := 332210620547170671689063202816 }, { target := 34, numerator := 599506522136848223622792216576 }, { target := 35, numerator := 9359175068518566854136711610368 }, { target := 36, numerator := 366577236465843499794828361728 }, { target := 37, numerator := 610962060776405832991380602880 }, { target := 38, numerator := 584232470617438077798007701504 }, { target := 39, numerator := 19092564399262682280980643840 }, { target := 40, numerator := 366577236465843499794828361728 }, { target := 41, numerator := 19092564399262682280980643840 }, { target := 42, numerator := 588050983497290614254203830272 }, { target := 43, numerator := 332210620547170671689063202816 }, { target := 44, numerator := 22911077279115218737176772608 }, { target := 157, numerator := 77662364360486244946834096128 }, { target := 158, numerator := 2070996382946299865248909230080 }, { target := 159, numerator := 1980390291192399246144269451264 }, { target := 160, numerator := 64718636967071870789028413440 }, { target := 161, numerator := 2032165200766056742775492182016 }, { target := 162, numerator := 64718636967071870789028413440 }, { target := 163, numerator := 1980390291192399246144269451264 }, { target := 164, numerator := 1126104283227050551729094393856 }, { target := 165, numerator := 2032165200766056742775492182016 }, { target := 166, numerator := 31725075841258631060781728268288 }, { target := 167, numerator := 1242597829767779919149345538048 }, { target := 168, numerator := 2070996382946299865248909230080 }, { target := 169, numerator := 1980390291192399246144269451264 }, { target := 170, numerator := 64718636967071870789028413440 }, { target := 171, numerator := 1242597829767779919149345538048 }, { target := 172, numerator := 64718636967071870789028413440 }, { target := 173, numerator := 1993334018585813620302075133952 }, { target := 174, numerator := 1126104283227050551729094393856 }, { target := 175, numerator := 77662364360486244946834096128 }, { target := 267, numerator := 22911077279115218737176772608 }, { target := 268, numerator := 610962060776405832991380602880 }, { target := 269, numerator := 584232470617438077798007701504 }, { target := 270, numerator := 19092564399262682280980643840 }, { target := 271, numerator := 599506522136848223622792216576 }, { target := 272, numerator := 19092564399262682280980643840 }, { target := 273, numerator := 584232470617438077798007701504 }, { target := 274, numerator := 332210620547170671689063202816 }, { target := 275, numerator := 599506522136848223622792216576 }, { target := 276, numerator := 9359175068518566854136711610368 }, { target := 277, numerator := 366577236465843499794828361728 }, { target := 278, numerator := 610962060776405832991380602880 }, { target := 279, numerator := 584232470617438077798007701504 }, { target := 280, numerator := 19092564399262682280980643840 }, { target := 281, numerator := 366577236465843499794828361728 }, { target := 282, numerator := 19092564399262682280980643840 }, { target := 283, numerator := 588050983497290614254203830272 }, { target := 284, numerator := 332210620547170671689063202816 }, { target := 285, numerator := 22911077279115218737176772608 }]

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

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 17601959933589000783721922560 }, { target := 11, numerator := 18104873074548686520399691776 }, { target := 12, numerator := 17601959933589000783721922560 }, { target := 13, numerator := 15590307369750257837010845696 }, { target := 14, numerator := 729726967532504003919443132416 }, { target := 15, numerator := 198650690679075865987718840320 }, { target := 16, numerator := 18104873074548686520399691776 }, { target := 17, numerator := 729726967532504003919443132416 }, { target := 18, numerator := 17601959933589000783721922560 }, { target := 19, numerator := 17601959933589000783721922560 }, { target := 20, numerator := 15087394228790572100333076480 }, { target := 21, numerator := 17601959933589000783721922560 }, { target := 22, numerator := 198650690679075865987718840320 }, { target := 23, numerator := 15087394228790572100333076480 }, { target := 24, numerator := 17601959933589000783721922560 }, { target := 25, numerator := 15590307369750257837010845696 }, { target := 141, numerator := 17601959933589000783721922560 }, { target := 142, numerator := 18104873074548686520399691776 }, { target := 143, numerator := 17601959933589000783721922560 }, { target := 144, numerator := 15590307369750257837010845696 }, { target := 145, numerator := 729726967532504003919443132416 }, { target := 146, numerator := 198650690679075865987718840320 }, { target := 147, numerator := 18104873074548686520399691776 }, { target := 148, numerator := 729726967532504003919443132416 }, { target := 149, numerator := 17601959933589000783721922560 }, { target := 150, numerator := 17601959933589000783721922560 }, { target := 151, numerator := 15087394228790572100333076480 }, { target := 152, numerator := 17601959933589000783721922560 }, { target := 153, numerator := 198650690679075865987718840320 }, { target := 154, numerator := 15087394228790572100333076480 }, { target := 155, numerator := 17601959933589000783721922560 }, { target := 156, numerator := 15590307369750257837010845696 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3
