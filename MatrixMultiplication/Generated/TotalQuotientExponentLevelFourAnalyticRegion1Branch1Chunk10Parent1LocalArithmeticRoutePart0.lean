import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent1

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
    Slot0.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 27710846521479078113968128 }, { target := 17, numerator := 415662697822186171709521920 }, { target := 18, numerator := 729718958398949057001160704 }, { target := 19, numerator := 27710846521479078113968128 }, { target := 20, numerator := 461847442024651301899468800 }, { target := 21, numerator := 27710846521479078113968128 }, { target := 22, numerator := 729718958398949057001160704 }, { target := 23, numerator := 725100483978702543982166016 }, { target := 24, numerator := 461847442024651301899468800 }, { target := 25, numerator := 11190563520257301045024129024 }, { target := 26, numerator := 715863535138209517944176640 }, { target := 27, numerator := 415662697822186171709521920 }, { target := 28, numerator := 729718958398949057001160704 }, { target := 29, numerator := 27710846521479078113968128 }, { target := 30, numerator := 715863535138209517944176640 }, { target := 31, numerator := 27710846521479078113968128 }, { target := 32, numerator := 729718958398949057001160704 }, { target := 33, numerator := 729718958398949057001160704 }, { target := 34, numerator := 27710846521479078113968128 }, { target := 51, numerator := 30317592820023122271928320 }, { target := 52, numerator := 454763892300346834078924800 }, { target := 53, numerator := 798363277593942219827445760 }, { target := 54, numerator := 30317592820023122271928320 }, { target := 55, numerator := 505293213667052037865472000 }, { target := 56, numerator := 30317592820023122271928320 }, { target := 57, numerator := 798363277593942219827445760 }, { target := 58, numerator := 793310345457271699448791040 }, { target := 59, numerator := 505293213667052037865472000 }, { target := 60, numerator := 12243254567152670877480386560 }, { target := 61, numerator := 783204481183930658691481600 }, { target := 62, numerator := 454763892300346834078924800 }, { target := 63, numerator := 798363277593942219827445760 }, { target := 64, numerator := 30317592820023122271928320 }, { target := 65, numerator := 783204481183930658691481600 }, { target := 66, numerator := 30317592820023122271928320 }, { target := 67, numerator := 798363277593942219827445760 }, { target := 68, numerator := 798363277593942219827445760 }, { target := 69, numerator := 30317592820023122271928320 }, { target := 126, numerator := 27710846521479078113968128 }, { target := 127, numerator := 415662697822186171709521920 }, { target := 128, numerator := 729718958398949057001160704 }, { target := 129, numerator := 27710846521479078113968128 }, { target := 130, numerator := 461847442024651301899468800 }, { target := 131, numerator := 27710846521479078113968128 }, { target := 132, numerator := 729718958398949057001160704 }, { target := 133, numerator := 725100483978702543982166016 }, { target := 134, numerator := 461847442024651301899468800 }, { target := 135, numerator := 11190563520257301045024129024 }, { target := 136, numerator := 715863535138209517944176640 }, { target := 137, numerator := 415662697822186171709521920 }, { target := 138, numerator := 729718958398949057001160704 }, { target := 139, numerator := 27710846521479078113968128 }, { target := 140, numerator := 715863535138209517944176640 }, { target := 141, numerator := 27710846521479078113968128 }, { target := 142, numerator := 729718958398949057001160704 }, { target := 143, numerator := 729718958398949057001160704 }, { target := 144, numerator := 27710846521479078113968128 }]

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
    Slot0.Left3.expected,
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
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 179863972743152965861244928 }, { target := 37, numerator := 7015663363376719309484064768 }, { target := 40, numerator := 7015660790055921027001614336 }, { target := 47, numerator := 179864830516752393355395072 }, { target := 70, numerator := 3754660431013318162353487872 }, { target := 72, numerator := 146451972710489015585479852032 }, { target := 75, numerator := 146451918992417351438658699264 }, { target := 82, numerator := 3754678337037206211293872128 }, { target := 86, numerator := 70172929009019483700896727040 }, { target := 89, numerator := 252409938848290607834721157120 }, { target := 91, numerator := 70172952419090634742924574720 }, { target := 96, numerator := 194852637138415713016348672 }, { target := 98, numerator := 7600301976991445918607736832 }, { target := 101, numerator := 7600299189227247779251748864 }, { target := 108, numerator := 194853566393148426135011328 }, { target := 145, numerator := 4039445054523310358300459008 }, { target := 147, numerator := 157560106369168821158829621248 }, { target := 150, numerator := 157560048576672559731411255296 }, { target := 157, numerator := 4039464318688730834106580992 }, { target := 171, numerator := 6047926083488518477084360704 }, { target := 173, numerator := 235901680593542186781401677824 }, { target := 176, numerator := 235901594065630344532929282048 }, { target := 183, numerator := 6047954926125799226575159296 }, { target := 216, numerator := 187358304940784339438796800 }, { target := 218, numerator := 7307982670184082614045900800 }, { target := 221, numerator := 7307979989641584403126681600 }, { target := 228, numerator := 187359198454950409745203200 }, { target := 266, numerator := 30317592820023122271928320 }, { target := 267, numerator := 454763892300346834078924800 }, { target := 268, numerator := 798363277593942219827445760 }, { target := 269, numerator := 30317592820023122271928320 }, { target := 270, numerator := 505293213667052037865472000 }, { target := 271, numerator := 30317592820023122271928320 }, { target := 272, numerator := 798363277593942219827445760 }, { target := 273, numerator := 793310345457271699448791040 }, { target := 274, numerator := 505293213667052037865472000 }, { target := 275, numerator := 12243254567152670877480386560 }, { target := 276, numerator := 783204481183930658691481600 }, { target := 277, numerator := 454763892300346834078924800 }, { target := 278, numerator := 798363277593942219827445760 }, { target := 279, numerator := 30317592820023122271928320 }, { target := 280, numerator := 783204481183930658691481600 }, { target := 281, numerator := 30317592820023122271928320 }, { target := 282, numerator := 798363277593942219827445760 }, { target := 283, numerator := 798363277593942219827445760 }, { target := 284, numerator := 30317592820023122271928320 }, { target := 285, numerator := 6047926083488518477084360704 }, { target := 287, numerator := 235901680593542186781401677824 }, { target := 290, numerator := 235901594065630344532929282048 }, { target := 297, numerator := 6047954926125799226575159296 }, { target := 311, numerator := 6302733378207985178721124352 }, { target := 313, numerator := 245840537024992539136504102912 }, { target := 316, numerator := 245840446851542899321181569024 }, { target := 323, numerator := 6302763436024531783828635648 }, { target := 356, numerator := 3754660431013318162353487872 }, { target := 358, numerator := 146451972710489015585479852032 }, { target := 361, numerator := 146451918992417351438658699264 }, { target := 368, numerator := 3754678337037206211293872128 }, { target := 427, numerator := 187358304940784339438796800 }, { target := 429, numerator := 7307982670184082614045900800 }, { target := 432, numerator := 7307979989641584403126681600 }, { target := 439, numerator := 187359198454950409745203200 }]

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
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
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
  [{ target := 112, numerator := 79227500494054255791335014400 }, { target := 115, numerator := 284978963215811976587588403200 }, { target := 117, numerator := 79227526924779748903301939200 }, { target := 122, numerator := 40039627918731547338615029760 }, { target := 124, numerator := 40039618372541489193922068480 }, { target := 161, numerator := 67909286137760790678287155200 }, { target := 164, numerator := 244267682756410265646504345600 }, { target := 166, numerator := 67909308792668356202830233600 }, { target := 187, numerator := 894138934147183743930780876800 }, { target := 190, numerator := 3216191156292735164345640550400 }, { target := 192, numerator := 894139232436800023337264742400 }, { target := 197, numerator := 580574604821607436409917931520 }, { target := 199, numerator := 580574466401851593311869992960 }, { target := 201, numerator := 79227500494054255791335014400 }, { target := 204, numerator := 284978963215811976587588403200 }, { target := 206, numerator := 79227526924779748903301939200 }, { target := 211, numerator := 1027683783247443048357785763840 }, { target := 213, numerator := 1027683538228564889310666424320 }, { target := 232, numerator := 67909286137760790678287155200 }, { target := 235, numerator := 244267682756410265646504345600 }, { target := 237, numerator := 67909308792668356202830233600 }, { target := 242, numerator := 33366356598942956115512524800 }, { target := 244, numerator := 33366348643784574328268390400 }, { target := 246, numerator := 79227500494054255791335014400 }, { target := 249, numerator := 284978963215811976587588403200 }, { target := 251, numerator := 79227526924779748903301939200 }, { target := 256, numerator := 640634046699704757417840476160 }, { target := 258, numerator := 640633893960663827102753095680 }, { target := 261, numerator := 33366356598942956115512524800 }, { target := 263, numerator := 33366348643784574328268390400 }, { target := 301, numerator := 79227500494054255791335014400 }, { target := 304, numerator := 284978963215811976587588403200 }, { target := 306, numerator := 79227526924779748903301939200 }, { target := 327, numerator := 3284545806196363575806488739840 }, { target := 330, numerator := 11814413589318376515102593515520 }, { target := 332, numerator := 3284546901938726161676888965120 }, { target := 337, numerator := 1021010511927654457134683258880 }, { target := 339, numerator := 1021010268499807974445012746240 }, { target := 341, numerator := 81491143365312948813944586240 }, { target := 344, numerator := 293121219307692318775805214720 }, { target := 346, numerator := 81491170551202027443396280320 }, { target := 351, numerator := 1067723411166174595696400793600 }, { target := 353, numerator := 1067723156601106378504588492800 }, { target := 372, numerator := 894138934147183743930780876800 }, { target := 375, numerator := 3216191156292735164345640550400 }, { target := 377, numerator := 894139232436800023337264742400 }, { target := 382, numerator := 640634046699704757417840476160 }, { target := 384, numerator := 640633893960663827102753095680 }, { target := 386, numerator := 3284545806196363575806488739840 }, { target := 389, numerator := 11814413589318376515102593515520 }, { target := 391, numerator := 3284546901938726161676888965120 }, { target := 406, numerator := 70172929009019483700896727040 }, { target := 409, numerator := 252409938848290607834721157120 }, { target := 411, numerator := 70172952419090634742924574720 }, { target := 443, numerator := 79227500494054255791335014400 }, { target := 446, numerator := 284978963215811976587588403200 }, { target := 448, numerator := 79227526924779748903301939200 }, { target := 457, numerator := 81491143365312948813944586240 }, { target := 460, numerator := 293121219307692318775805214720 }, { target := 462, numerator := 81491170551202027443396280320 }, { target := 477, numerator := 79227500494054255791335014400 }, { target := 480, numerator := 284978963215811976587588403200 }, { target := 482, numerator := 79227526924779748903301939200 }]

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
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
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
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 1048592032788238980410769408 }, { target := 17, numerator := 123936846069911868518336299008 }, { target := 19, numerator := 1176135964048761170032683122688 }, { target := 27, numerator := 123936931072508560171950145536 }, { target := 34, numerator := 1048592032788238980410769408 }, { target := 35, numerator := 238938300598737320568296570880 }, { target := 37, numerator := 9350840848288744987540297089024 }, { target := 40, numerator := 9350840848288744987540297089024 }, { target := 47, numerator := 238938300598737320568296570880 }, { target := 86, numerator := 1171603983511688419930739310592 }, { target := 89, numerator := 4352216831758674131301611601920 }, { target := 91, numerator := 1171357362134599618867373277184 }, { target := 126, numerator := 1048592032788238980410769408 }, { target := 127, numerator := 123936846069911868518336299008 }, { target := 129, numerator := 1176135964048761170032683122688 }, { target := 137, numerator := 123936931072508560171950145536 }, { target := 144, numerator := 1048592032788238980410769408 }, { target := 145, numerator := 870395042262543950428168519680 }, { target := 147, numerator := 34062875206452418409809800331264 }, { target := 150, numerator := 34062875206452418409809800331264 }, { target := 157, numerator := 870395042262543950428168519680 }, { target := 161, numerator := 46840509882673631068624661774336 }, { target := 164, numerator := 174000821428153586414098170511360 }, { target := 166, numerator := 46830650005775481788782893596672 }, { target := 215, numerator := 51819396331961464944605528064 }, { target := 216, numerator := 238938461325261218996079820800 }, { target := 218, numerator := 9350847138314836689047875747840 }, { target := 221, numerator := 9350847138314836689047875747840 }, { target := 228, numerator := 238938461325261218996079820800 }, { target := 260, numerator := 38588912162098963256621137920 }, { target := 265, numerator := 40793992857076046871285202944 }, { target := 355, numerator := 52921936679450006751937560576 }, { target := 396, numerator := 16356188004801837087824239656960 }, { target := 398, numerator := 16356184105183198335717164974080 }, { target := 400, numerator := 708933443435132382114496905216 }, { target := 401, numerator := 1047703597206808822027093278720 }, { target := 403, numerator := 1047703347414835633907627458560 }, { target := 405, numerator := 1282254424129174121927153811456 }, { target := 416, numerator := 580574604821607436409917931520 }, { target := 418, numerator := 580574466401851593311869992960 }, { target := 420, numerator := 38588912162098963256621137920 }, { target := 421, numerator := 1021010511927654457134683258880 }, { target := 423, numerator := 1021010268499807974445012746240 }, { target := 425, numerator := 708933443435132382114496905216 }, { target := 426, numerator := 41896533204564588678617235456 }, { target := 453, numerator := 33366356598942956115512524800 }, { target := 455, numerator := 33366348643784574328268390400 }, { target := 467, numerator := 1047703597206808822027093278720 }, { target := 469, numerator := 1047703347414835633907627458560 }, { target := 471, numerator := 41896533204564588678617235456 }, { target := 472, numerator := 33366356598942956115512524800 }, { target := 474, numerator := 33366348643784574328268390400 }, { target := 476, numerator := 40793992857076046871285202944 }, { target := 487, numerator := 1021010511927654457134683258880 }, { target := 489, numerator := 1021010268499807974445012746240 }, { target := 491, numerator := 40793992857076046871285202944 }, { target := 492, numerator := 1067723411166174595696400793600 }, { target := 494, numerator := 1067723156601106378504588492800 }, { target := 496, numerator := 1282254424129174121927153811456 }, { target := 497, numerator := 40793992857076046871285202944 }, { target := 498, numerator := 40039627918731547338615029760 }, { target := 500, numerator := 40039618372541489193922068480 }, { target := 502, numerator := 51819396331961464944605528064 }, { target := 503, numerator := 52921936679450006751937560576 }]

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
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1122907914129158587138703360 }, { target := 1, numerator := 196947498371531685396721172480 }, { target := 6, numerator := 196947521983364099744947240960 }, { target := 14, numerator := 1122884302296744238912634880 }, { target := 16, numerator := 5554728812613712245004697600 }, { target := 17, numerator := 1789296795235961667193090867200 }, { target := 19, numerator := 19029923867370937697783943004160 }, { target := 27, numerator := 1789302188176556437787503493120 }, { target := 34, numerator := 5554728812613712245004697600 }, { target := 35, numerator := 1559661255543371630934333849600 }, { target := 37, numerator := 61039055546802061854137280102400 }, { target := 40, numerator := 61039077933855738482885499289600 }, { target := 47, numerator := 1559683642597048259682553036800 }, { target := 86, numerator := 1564433023690643136207447392256 }, { target := 89, numerator := 5607545654829476098271977930752 }, { target := 91, numerator := 1564887645261984995130432552960 }, { target := 122, numerator := 40426577167997293196547719168 }, { target := 124, numerator := 40426589431954352272190734336 }, { target := 126, numerator := 5554732785666785513119416320 }, { target := 127, numerator := 1789298075041217894631384023040 }, { target := 129, numerator := 19029937478638032074694786547712 }, { target := 137, numerator := 1789303467985669998306639478784 }, { target := 144, numerator := 5554732785666785513119416320 }, { target := 145, numerator := 5590441753713299431456191283200 }, { target := 147, numerator := 218788075630681985717203946700800 }, { target := 150, numerator := 218788155874721626776218579763200 }, { target := 157, numerator := 5590521997752940490470824345600 }, { target := 161, numerator := 61225803932044402439979966398464 }, { target := 164, numerator := 219457455578787188393052615999488 }, { target := 166, numerator := 61243596046355944040084789002240 }, { target := 197, numerator := 7496424248260702483332317839360 }, { target := 199, numerator := 7496426881280204116321904885760 }, { target := 215, numerator := 9737836086231560696870469632 }, { target := 216, numerator := 1560114490447019609356763136000 }, { target := 218, numerator := 61056793392351017414567133184000 }, { target := 221, numerator := 61056815785910333700661313536000 }, { target := 228, numerator := 1560136884006335895450943488000 }, { target := 232, numerator := 108066324823286075840900636868608 }, { target := 235, numerator := 393458314973813368249926729859072 }, { target := 237, numerator := 108074257069634588429768525348864 }, { target := 242, numerator := 77781683055197562821292452741120 }, { target := 244, numerator := 77781710594518610790851880681472 }, { target := 260, numerator := 1931352145513244710344956313600 }, { target := 406, numerator := 2736059462748976940577760215040 }, { target := 409, numerator := 9959842976133634949618635636736 }, { target := 411, numerator := 2736267469468773595811481124864 }, { target := 416, numerator := 5722795551056579359634788188160 }, { target := 418, numerator := 5722796915477525782939482193920 }, { target := 420, numerator := 1931352145513244710344956313600 }, { target := 498, numerator := 34920488712761984736525549568 }, { target := 500, numerator := 34920497038456277665490927616 }, { target := 502, numerator := 9737836086231560696870469632 }]

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
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected,
    Slot16.Left14.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected,
    Slot21.Left11.expected,
    Slot21.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 9737836086231560696870469632 }, { target := 1, numerator := 1931352145513244710344956313600 }, { target := 6, numerator := 1931352145513244710344956313600 }, { target := 14, numerator := 9737836086231560696870469632 }, { target := 16, numerator := 35018690312066714727348174848 }, { target := 17, numerator := 5738888901875073677294053621760 }, { target := 19, numerator := 59084083277112937224024212111360 }, { target := 27, numerator := 5738888901875073677294053621760 }, { target := 34, numerator := 35018690312066714727348174848 }, { target := 35, numerator := 1171603983511688419930739310592 }, { target := 37, numerator := 46840509882673631068624661774336 }, { target := 40, numerator := 46840498435695028016481096957952 }, { target := 47, numerator := 1171603983511688419930739310592 }, { target := 86, numerator := 238063709454525251312922132480 }, { target := 89, numerator := 867209116046356015031286497280 }, { target := 91, numerator := 238063869592738300917763276800 }, { target := 122, numerator := 1077719589254578952088846336 }, { target := 124, numerator := 1077719589254578952088846336 }, { target := 126, numerator := 35018698661174096219105918976 }, { target := 127, numerator := 5738890270132974393127725957120 }, { target := 129, numerator := 59084097363857798942528183992320 }, { target := 137, numerator := 5738890270132974393127725957120 }, { target := 144, numerator := 35018698661174096219105918976 }, { target := 145, numerator := 4352216831758674131301611601920 }, { target := 147, numerator := 174000821428153586414098170511360 }, { target := 150, numerator := 174000778905480695136829067755520 }, { target := 157, numerator := 4352216831758674131301611601920 }, { target := 161, numerator := 9316613758800133183047104200704 }, { target := 164, numerator := 33938194111260425663068183199744 }, { target := 166, numerator := 9316620025802703319029398896640 }, { target := 197, numerator := 127379536238520531532734529536 }, { target := 199, numerator := 127379536238520531532734529536 }, { target := 215, numerator := 1347489496954990304566444032 }, { target := 216, numerator := 1171357362134599618867373277184 }, { target := 218, numerator := 46830650005775481788782893596672 }, { target := 221, numerator := 46830638561206455407870061051904 }, { target := 228, numerator := 1171357362134599618867373277184 }, { target := 232, numerator := 9316613758800133183047104200704 }, { target := 235, numerator := 33938194111260425663068183199744 }, { target := 237, numerator := 9316620025802703319029398896640 }, { target := 242, numerator := 1208806407494560091422479876096 }, { target := 244, numerator := 1208806407494560091422479876096 }, { target := 260, numerator := 236336998045838022476065406976 }, { target := 406, numerator := 238063709454525251312922132480 }, { target := 409, numerator := 867209116046356015031286497280 }, { target := 411, numerator := 238063869592738300917763276800 }, { target := 416, numerator := 1901013666523370418715263762432 }, { target := 418, numerator := 1901014935125749184483794354176 }, { target := 420, numerator := 236337026380036919693936689152 }, { target := 498, numerator := 6583808044489887412111015936 }, { target := 500, numerator := 6583811982752653558788653056 }, { target := 502, numerator := 1347461162756093086695161856 }]

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
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 52728508548311666083984572416 }, { target := 1, numerator := 39265910621083155594456596480 }, { target := 2, numerator := 41509676942287907342711259136 }, { target := 3, numerator := 53850391708914041958111903744 }, { target := 4, numerator := 721370872267327687063874043904 }, { target := 5, numerator := 1304750115780563141610086334464 }, { target := 6, numerator := 39265910621083155594456596480 }, { target := 7, numerator := 721370872267327687063874043904 }, { target := 8, numerator := 42631560102890283216838590464 }, { target := 9, numerator := 42631560102890283216838590464 }, { target := 10, numerator := 41509676942287907342711259136 }, { target := 11, numerator := 41509676942287907342711259136 }, { target := 12, numerator := 1304750115780563141610086334464 }, { target := 13, numerator := 41509676942287907342711259136 }, { target := 14, numerator := 52728508548311666083984572416 }, { target := 15, numerator := 53850391708914041958111903744 }, { target := 16, numerator := 40329770150026703478749921280 }, { target := 17, numerator := 584781667175387200441873858560 }, { target := 18, numerator := 1035130767184018722621247979520 }, { target := 19, numerator := 33608141791688919565624934400 }, { target := 20, numerator := 645276322400427255659998740480 }, { target := 21, numerator := 33608141791688919565624934400 }, { target := 22, numerator := 1028409138825680938708122992640 }, { target := 23, numerator := 1075460537334045426099997900800 }, { target := 24, numerator := 645276322400427255659998740480 }, { target := 25, numerator := 16474711106285908371069342842880 }, { target := 26, numerator := 1055295652259032074360622940160 }, { target := 27, numerator := 584781667175387200441873858560 }, { target := 28, numerator := 1028409138825680938708122992640 }, { target := 29, numerator := 33608141791688919565624934400 }, { target := 30, numerator := 1055295652259032074360622940160 }, { target := 31, numerator := 33608141791688919565624934400 }, { target := 32, numerator := 1028409138825680938708122992640 }, { target := 33, numerator := 1075460537334045426099997900800 }, { target := 34, numerator := 40329770150026703478749921280 }, { target := 126, numerator := 40329760534661355057646141440 }, { target := 127, numerator := 584781527752589648335869050880 }, { target := 128, numerator := 1035130520389641446479584296960 }, { target := 129, numerator := 33608133778884462548038451200 }, { target := 130, numerator := 645276168554581680922338263040 }, { target := 131, numerator := 33608133778884462548038451200 }, { target := 132, numerator := 1028408893633864553969976606720 }, { target := 133, numerator := 1075460280924302801537230438400 }, { target := 134, numerator := 645276168554581680922338263040 }, { target := 135, numerator := 16474707178409163541048448778240 }, { target := 136, numerator := 1055295400656972124008407367680 }, { target := 137, numerator := 584781527752589648335869050880 }, { target := 138, numerator := 1028408893633864553969976606720 }, { target := 139, numerator := 33608133778884462548038451200 }, { target := 140, numerator := 1055295400656972124008407367680 }, { target := 141, numerator := 33608133778884462548038451200 }, { target := 142, numerator := 1028408893633864553969976606720 }, { target := 143, numerator := 1075460280924302801537230438400 }, { target := 144, numerator := 40329760534661355057646141440 }]

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
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 69744392037972036472188960768 }, { target := 36, numerator := 78743668429968428275052052480 }, { target := 37, numerator := 67494572939972938521473187840 }, { target := 38, numerator := 888678543709643690532730306560 }, { target := 39, numerator := 78743668429968428275052052480 }, { target := 40, numerator := 67494572939972938521473187840 }, { target := 41, numerator := 78743668429968428275052052480 }, { target := 42, numerator := 78743668429968428275052052480 }, { target := 43, numerator := 3264487511196691126488586518528 }, { target := 44, numerator := 80993487527967526225767825408 }, { target := 45, numerator := 888678543709643690532730306560 }, { target := 46, numerator := 3264487511196691126488586518528 }, { target := 47, numerator := 69744392037972036472188960768 }, { target := 48, numerator := 78743668429968428275052052480 }, { target := 49, numerator := 80993487527967526225767825408 }, { target := 50, numerator := 78743668429968428275052052480 }, { target := 86, numerator := 185666036380028867985801216 }, { target := 87, numerator := 3875778509433102619203600384 }, { target := 88, numerator := 201138206078364606984617984 }, { target := 89, numerator := 4169749733701481660181118976 }, { target := 90, numerator := 6243020473278470686022565888 }, { target := 91, numerator := 193402121229196737485209600 }, { target := 92, numerator := 6243020473278470686022565888 }, { target := 93, numerator := 6506047358150178249002450944 }, { target := 94, numerator := 3875778509433102619203600384 }, { target := 95, numerator := 193402121229196737485209600 }, { target := 145, numerator := 250868504107232344580768661504 }, { target := 146, numerator := 283238633669455872913771069440 }, { target := 147, numerator := 242775971716676462497518059520 }, { target := 148, numerator := 3196550294269573422883987783680 }, { target := 149, numerator := 283238633669455872913771069440 }, { target := 150, numerator := 242775971716676462497518059520 }, { target := 151, numerator := 283238633669455872913771069440 }, { target := 152, numerator := 283238633669455872913771069440 }, { target := 153, numerator := 11742264498696584902796623478784 }, { target := 154, numerator := 291331166060011754997021671424 }, { target := 155, numerator := 3196550294269573422883987783680 }, { target := 156, numerator := 11742264498696584902796623478784 }, { target := 157, numerator := 250868504107232344580768661504 }, { target := 158, numerator := 283238633669455872913771069440 }, { target := 159, numerator := 291331166060011754997021671424 }, { target := 160, numerator := 283238633669455872913771069440 }, { target := 216, numerator := 69744415305080920942967783424 }, { target := 217, numerator := 78743694699284910742060400640 }, { target := 218, numerator := 67494595456529923493194629120 }, { target := 219, numerator := 888678840177643992660395950080 }, { target := 220, numerator := 78743694699284910742060400640 }, { target := 221, numerator := 67494595456529923493194629120 }, { target := 222, numerator := 78743694699284910742060400640 }, { target := 223, numerator := 78743694699284910742060400640 }, { target := 224, numerator := 3264488600247497299620846895104 }, { target := 225, numerator := 80993514547835908191833554944 }, { target := 226, numerator := 888678840177643992660395950080 }, { target := 227, numerator := 3264488600247497299620846895104 }, { target := 228, numerator := 69744415305080920942967783424 }, { target := 229, numerator := 78743694699284910742060400640 }, { target := 230, numerator := 80993514547835908191833554944 }, { target := 231, numerator := 78743694699284910742060400640 }]

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
    Slot26.Left2.expected,
    Slot26.Left5.expected,
    Slot26.Left12.expected,
    Slot27.Left0.expected,
    Slot27.Left1.expected,
    Slot27.Left2.expected,
    Slot27.Left3.expected,
    Slot27.Left4.expected,
    Slot27.Left5.expected,
    Slot27.Left6.expected,
    Slot27.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 122, numerator := 27710846521479078113968128 }, { target := 123, numerator := 30317592820023122271928320 }, { target := 124, numerator := 27710846521479078113968128 }, { target := 125, numerator := 30317592820023122271928320 }, { target := 161, numerator := 7241975084775968319467421696 }, { target := 162, numerator := 151176229894698338668882427904 }, { target := 163, numerator := 7845473008507299012756373504 }, { target := 164, numerator := 162642690445593621841372512256 }, { target := 165, numerator := 243511412225591934742092054528 }, { target := 166, numerator := 7543724046641633666111897600 }, { target := 167, numerator := 243511412225591934742092054528 }, { target := 168, numerator := 253770876929024556528004235264 }, { target := 169, numerator := 151176229894698338668882427904 }, { target := 170, numerator := 7543724046641633666111897600 }, { target := 197, numerator := 415662697822186171709521920 }, { target := 198, numerator := 454763892300346834078924800 }, { target := 199, numerator := 415662697822186171709521920 }, { target := 200, numerator := 454763892300346834078924800 }, { target := 211, numerator := 729718958398949057001160704 }, { target := 212, numerator := 798363277593942219827445760 }, { target := 213, numerator := 729718958398949057001160704 }, { target := 214, numerator := 798363277593942219827445760 }, { target := 232, numerator := 7241972428444821705291988992 }, { target := 233, numerator := 151176174443785653097970270208 }, { target := 234, numerator := 7845470130815223514066321408 }, { target := 235, numerator := 162642630788823287464682586112 }, { target := 236, numerator := 243511322906457129840443129856 }, { target := 237, numerator := 7543721279630022609679155200 }, { target := 238, numerator := 243511322906457129840443129856 }, { target := 239, numerator := 253770783846753960589606780928 }, { target := 240, numerator := 151176174443785653097970270208 }, { target := 241, numerator := 7543721279630022609679155200 }, { target := 242, numerator := 27710846521479078113968128 }, { target := 243, numerator := 30317592820023122271928320 }, { target := 244, numerator := 27710846521479078113968128 }, { target := 245, numerator := 30317592820023122271928320 }, { target := 256, numerator := 461847442024651301899468800 }, { target := 257, numerator := 505293213667052037865472000 }, { target := 258, numerator := 461847442024651301899468800 }, { target := 259, numerator := 505293213667052037865472000 }, { target := 261, numerator := 27710846521479078113968128 }, { target := 262, numerator := 30317592820023122271928320 }, { target := 263, numerator := 27710846521479078113968128 }, { target := 264, numerator := 30317592820023122271928320 }, { target := 337, numerator := 729718958398949057001160704 }, { target := 338, numerator := 798363277593942219827445760 }, { target := 339, numerator := 729718958398949057001160704 }, { target := 340, numerator := 798363277593942219827445760 }, { target := 351, numerator := 725100483978702543982166016 }, { target := 352, numerator := 793310345457271699448791040 }, { target := 353, numerator := 725100483978702543982166016 }, { target := 354, numerator := 793310345457271699448791040 }, { target := 406, numerator := 185666921823744406044278784 }, { target := 407, numerator := 3875796993070664476174319616 }, { target := 408, numerator := 201139165309056439881302016 }, { target := 409, numerator := 4169769619291593119077761024 }, { target := 410, numerator := 6243050246323405653238874112 }, { target := 411, numerator := 193403043566400422962790400 }, { target := 412, numerator := 6243050246323405653238874112 }, { target := 413, numerator := 6506078385573710228468269056 }, { target := 414, numerator := 3875796993070664476174319616 }, { target := 415, numerator := 193403043566400422962790400 }]

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

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot27.Left8.expected,
    Slot27.Left9.expected,
    Slot27.Left10.expected,
    Slot27.Left11.expected,
    Slot27.Left12.expected,
    Slot27.Left13.expected,
    Slot27.Left14.expected,
    Slot27.Left15.expected,
    Slot27.Left16.expected,
    Slot27.Left17.expected,
    Slot27.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 382, numerator := 461847442024651301899468800 }, { target := 383, numerator := 505293213667052037865472000 }, { target := 384, numerator := 461847442024651301899468800 }, { target := 385, numerator := 505293213667052037865472000 }, { target := 396, numerator := 11190563520257301045024129024 }, { target := 397, numerator := 12243254567152670877480386560 }, { target := 398, numerator := 11190563520257301045024129024 }, { target := 399, numerator := 12243254567152670877480386560 }, { target := 401, numerator := 715863535138209517944176640 }, { target := 402, numerator := 783204481183930658691481600 }, { target := 403, numerator := 715863535138209517944176640 }, { target := 404, numerator := 783204481183930658691481600 }, { target := 416, numerator := 415662697822186171709521920 }, { target := 417, numerator := 454763892300346834078924800 }, { target := 418, numerator := 415662697822186171709521920 }, { target := 419, numerator := 454763892300346834078924800 }, { target := 421, numerator := 729718958398949057001160704 }, { target := 422, numerator := 798363277593942219827445760 }, { target := 423, numerator := 729718958398949057001160704 }, { target := 424, numerator := 798363277593942219827445760 }, { target := 453, numerator := 27710846521479078113968128 }, { target := 454, numerator := 30317592820023122271928320 }, { target := 455, numerator := 27710846521479078113968128 }, { target := 456, numerator := 30317592820023122271928320 }, { target := 467, numerator := 715863535138209517944176640 }, { target := 468, numerator := 783204481183930658691481600 }, { target := 469, numerator := 715863535138209517944176640 }, { target := 470, numerator := 783204481183930658691481600 }, { target := 472, numerator := 27710846521479078113968128 }, { target := 473, numerator := 30317592820023122271928320 }, { target := 474, numerator := 27710846521479078113968128 }, { target := 475, numerator := 30317592820023122271928320 }, { target := 487, numerator := 729718958398949057001160704 }, { target := 488, numerator := 798363277593942219827445760 }, { target := 489, numerator := 729718958398949057001160704 }, { target := 490, numerator := 798363277593942219827445760 }, { target := 492, numerator := 729718958398949057001160704 }, { target := 493, numerator := 798363277593942219827445760 }, { target := 494, numerator := 729718958398949057001160704 }, { target := 495, numerator := 798363277593942219827445760 }, { target := 498, numerator := 27710846521479078113968128 }, { target := 499, numerator := 30317592820023122271928320 }, { target := 500, numerator := 27710846521479078113968128 }, { target := 501, numerator := 30317592820023122271928320 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent1
