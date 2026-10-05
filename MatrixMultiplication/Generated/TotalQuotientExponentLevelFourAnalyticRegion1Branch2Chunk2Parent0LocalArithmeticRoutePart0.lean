import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 9; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent0

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
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 8737888412713598983423918080 }, { target := 89, numerator := 29875432499590440825605062656 }, { target := 91, numerator := 8737885590361755705862520832 }, { target := 112, numerator := 8555849070782065671269253120 }, { target := 115, numerator := 29253027655848973308404957184 }, { target := 117, numerator := 8555846307229219128657051648 }, { target := 122, numerator := 522374057046608719663595520 }, { target := 124, numerator := 522137851100430887282540544 }, { target := 161, numerator := 6735455651466732549722603520 }, { target := 164, numerator := 23028979218434298136403902464 }, { target := 166, numerator := 6735453475903853356602359808 }, { target := 197, numerator := 13929974854576232524362547200 }, { target := 199, numerator := 13923676029344823660867747840 }, { target := 211, numerator := 13320538454688522351421685760 }, { target := 213, numerator := 13314515203060987625704783872 }, { target := 215, numerator := 676998458984192337835458560 }, { target := 242, numerator := 435311714205507266386329600 }, { target := 244, numerator := 435114875917025739402117120 }, { target := 256, numerator := 13668787826052928164530749440 }, { target := 258, numerator := 13662607103794608217226477568 }, { target := 260, numerator := 696341272098026404630757376 }, { target := 261, numerator := 435311714205507266386329600 }, { target := 263, numerator := 435114875917025739402117120 }, { target := 265, numerator := 676998458984192337835458560 }, { target := 337, numerator := 13320538454688522351421685760 }, { target := 339, numerator := 13314515203060987625704783872 }, { target := 351, numerator := 7574423827175826435122135040 }, { target := 353, numerator := 7570998840956247865596837888 }, { target := 355, numerator := 599627206528856070654263296 }, { target := 382, numerator := 13668787826052928164530749440 }, { target := 384, numerator := 13662607103794608217226477568 }, { target := 396, numerator := 213389802303539661982578769920 }, { target := 398, numerator := 213293312174526017454917812224 }, { target := 400, numerator := 28066421828173230919978582016 }, { target := 401, numerator := 8357984912745739514617528320 }, { target := 403, numerator := 8354205617606894196520648704 }, { target := 405, numerator := 7640411179964456384143032320 }, { target := 416, numerator := 13929974854576232524362547200 }, { target := 418, numerator := 13923676029344823660867747840 }, { target := 420, numerator := 696341272098026404630757376 }, { target := 421, numerator := 13320538454688522351421685760 }, { target := 423, numerator := 13314515203060987625704783872 }, { target := 425, numerator := 28066421828173230919978582016 }, { target := 426, numerator := 676998458984192337835458560 }, { target := 453, numerator := 435311714205507266386329600 }, { target := 455, numerator := 435114875917025739402117120 }, { target := 467, numerator := 8357984912745739514617528320 }, { target := 469, numerator := 8354205617606894196520648704 }, { target := 471, numerator := 676998458984192337835458560 }, { target := 472, numerator := 435311714205507266386329600 }, { target := 474, numerator := 435114875917025739402117120 }, { target := 476, numerator := 580284393415022003858964480 }, { target := 487, numerator := 13407600797529623804698951680 }, { target := 489, numerator := 13401538178244392773585207296 }, { target := 491, numerator := 676998458984192337835458560 }, { target := 492, numerator := 7574423827175826435122135040 }, { target := 494, numerator := 7570998840956247865596837888 }, { target := 496, numerator := 7640411179964456384143032320 }, { target := 497, numerator := 580284393415022003858964480 }, { target := 498, numerator := 522374057046608719663595520 }, { target := 500, numerator := 522137851100430887282540544 }, { target := 502, numerator := 676998458984192337835458560 }, { target := 503, numerator := 599627206528856070654263296 }]

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
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 233204481061285118338924544 }, { target := 37, numerator := 8161575409606833872077586432 }, { target := 40, numerator := 8161579412550297867050287104 }, { target := 47, numerator := 233202479589553120852574208 }, { target := 70, numerator := 5717271148599248062502666240 }, { target := 72, numerator := 200090235848425604605773086720 }, { target := 75, numerator := 200090333985104076740587683840 }, { target := 82, numerator := 5717222080260011995095367680 }, { target := 96, numerator := 233204481061285118338924544 }, { target := 98, numerator := 8161575409606833872077586432 }, { target := 101, numerator := 8161579412550297867050287104 }, { target := 108, numerator := 233202479589553120852574208 }, { target := 145, numerator := 4791975949549632915544997888 }, { target := 147, numerator := 167707210836114618597207179264 }, { target := 150, numerator := 167707293090146443268097835008 }, { target := 157, numerator := 4791934822533720580099670016 }, { target := 171, numerator := 4709225972398854325166669824 }, { target := 173, numerator := 164811167948834774320018358272 }, { target := 176, numerator := 164811248782467305315273539584 }, { target := 183, numerator := 4709185555582588827539079168 }, { target := 187, numerator := 211711754666373242035875348480 }, { target := 190, numerator := 723856833271326722503722663936 }, { target := 192, numerator := 211711686283140039289960660992 }, { target := 201, numerator := 6735455651466732549722603520 }, { target := 204, numerator := 23028979218434298136403902464 }, { target := 206, numerator := 6735453475903853356602359808 }, { target := 216, numerator := 233204481061285118338924544 }, { target := 218, numerator := 8161575409606833872077586432 }, { target := 221, numerator := 8161579412550297867050287104 }, { target := 228, numerator := 233202479589553120852574208 }, { target := 232, numerator := 6735455651466732549722603520 }, { target := 235, numerator := 23028979218434298136403902464 }, { target := 237, numerator := 6735453475903853356602359808 }, { target := 246, numerator := 6917494993398265861877268480 }, { target := 249, numerator := 23651384062175765653604007936 }, { target := 251, numerator := 6917492759036389933807828992 }, { target := 301, numerator := 6917494993398265861877268480 }, { target := 304, numerator := 23651384062175765653604007936 }, { target := 306, numerator := 6917492759036389933807828992 }, { target := 327, numerator := 117051296861975919715449569280 }, { target := 330, numerator := 400206314525763613559667818496 }, { target := 332, numerator := 117051259054221019143116685312 }, { target := 341, numerator := 6371376967603665925413273600 }, { target := 344, numerator := 21784169530951363102003691520 }, { target := 346, numerator := 6371374909638780202191421440 }, { target := 372, numerator := 211711754666373242035875348480 }, { target := 375, numerator := 723856833271326722503722663936 }, { target := 377, numerator := 211711686283140039289960660992 }, { target := 386, numerator := 117051296861975919715449569280 }, { target := 389, numerator := 400206314525763613559667818496 }, { target := 391, numerator := 117051259054221019143116685312 }, { target := 406, numerator := 8737888412713598983423918080 }, { target := 409, numerator := 29875432499590440825605062656 }, { target := 411, numerator := 8737885590361755705862520832 }, { target := 443, numerator := 6735455651466732549722603520 }, { target := 446, numerator := 23028979218434298136403902464 }, { target := 448, numerator := 6735453475903853356602359808 }, { target := 457, numerator := 6371376967603665925413273600 }, { target := 460, numerator := 21784169530951363102003691520 }, { target := 462, numerator := 6371374909638780202191421440 }, { target := 477, numerator := 8555849070782065671269253120 }, { target := 480, numerator := 29253027655848973308404957184 }, { target := 482, numerator := 8555846307229219128657051648 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 467537893636509224381972480 }, { target := 1, numerator := 39146543363495659572390002688 }, { target := 6, numerator := 39146557530595108181325643776 }, { target := 14, numerator := 467523726537060615446331392 }, { target := 16, numerator := 73876760057009464672256000 }, { target := 17, numerator := 7745845050280306838339584000 }, { target := 19, numerator := 83492467679002248609792000000 }, { target := 27, numerator := 7745850959003017948430336000 }, { target := 34, numerator := 73876760057009464672256000 }, { target := 51, numerator := 73372235841985985401323520 }, { target := 52, numerator := 7692946596278392547736289280 }, { target := 54, numerator := 82922275216804184472944640000 }, { target := 62, numerator := 7692952464648850996587397120 }, { target := 69, numerator := 73372235841985985401323520 }, { target := 122, numerator := 73876760057009464672256000 }, { target := 123, numerator := 73372235841985985401323520 }, { target := 124, numerator := 73876760057009464672256000 }, { target := 125, numerator := 74092984720590955788369920 }, { target := 126, numerator := 73876760057009464672256000 }, { target := 127, numerator := 7745845050280306838339584000 }, { target := 129, numerator := 83492467679002248609792000000 }, { target := 137, numerator := 7745850959003017948430336000 }, { target := 144, numerator := 73876760057009464672256000 }, { target := 197, numerator := 7745845050280306838339584000 }, { target := 198, numerator := 7692946596278392547736289280 }, { target := 199, numerator := 7745845050280306838339584000 }, { target := 200, numerator := 7768515816281127248598138880 }, { target := 215, numerator := 467537893636509224381972480 }, { target := 242, numerator := 83492467679002248609792000000 }, { target := 243, numerator := 82922275216804184472944640000 }, { target := 244, numerator := 83492467679002248609792000000 }, { target := 245, numerator := 83736835877087133239869440000 }, { target := 260, numerator := 39146543363495659572390002688 }, { target := 266, numerator := 74092984720590955788369920 }, { target := 267, numerator := 7768515816281127248598138880 }, { target := 269, numerator := 83736835877087133239869440000 }, { target := 277, numerator := 7768521742297660927791595520 }, { target := 284, numerator := 74092984720590955788369920 }, { target := 285, numerator := 4716748697594379651564699648 }, { target := 287, numerator := 165074444574951123799762796544 }, { target := 290, numerator := 165074525537710863310984839168 }, { target := 297, numerator := 4716708216214509895953678336 }, { target := 311, numerator := 4227771559885233435692761088 }, { target := 313, numerator := 147961463877388407616374308864 }, { target := 316, numerator := 147961536446879593589750366208 }, { target := 323, numerator := 4227735275139640449004732416 }, { target := 356, numerator := 5717271148599248062502666240 }, { target := 358, numerator := 200090235848425604605773086720 }, { target := 361, numerator := 200090333985104076740587683840 }, { target := 368, numerator := 5717222080260011995095367680 }, { target := 416, numerator := 7745850959003017948430336000 }, { target := 417, numerator := 7692952464648850996587397120 }, { target := 418, numerator := 7745850959003017948430336000 }, { target := 419, numerator := 7768521742297660927791595520 }, { target := 420, numerator := 39146557530595108181325643776 }, { target := 427, numerator := 233204481061285118338924544 }, { target := 429, numerator := 8161575409606833872077586432 }, { target := 432, numerator := 8161579412550297867050287104 }, { target := 439, numerator := 233202479589553120852574208 }, { target := 498, numerator := 73876760057009464672256000 }, { target := 499, numerator := 73372235841985985401323520 }, { target := 500, numerator := 73876760057009464672256000 }, { target := 501, numerator := 74092984720590955788369920 }, { target := 502, numerator := 467523726537060615446331392 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 8223894976671622572634275840 }, { target := 36, numerator := 8052563831324297102371061760 }, { target := 37, numerator := 6339252377851042399738920960 }, { target := 38, numerator := 199258122038939521916117975040 }, { target := 39, numerator := 6339252377851042399738920960 }, { target := 40, numerator := 6339252377851042399738920960 }, { target := 41, numerator := 6510583523198367870002135040 }, { target := 42, numerator := 6510583523198367870002135040 }, { target := 43, numerator := 110165926458330277379246653440 }, { target := 44, numerator := 5996590087156391459212492800 }, { target := 45, numerator := 199258122038939521916117975040 }, { target := 46, numerator := 110165926458330277379246653440 }, { target := 47, numerator := 8223894976671622572634275840 }, { target := 48, numerator := 6339252377851042399738920960 }, { target := 49, numerator := 5996590087156391459212492800 }, { target := 50, numerator := 8052563831324297102371061760 }, { target := 86, numerator := 233204481061285118338924544 }, { target := 87, numerator := 5717271148599248062502666240 }, { target := 88, numerator := 233204481061285118338924544 }, { target := 89, numerator := 4791975949549632915544997888 }, { target := 90, numerator := 4709225972398854325166669824 }, { target := 91, numerator := 233204481061285118338924544 }, { target := 92, numerator := 4716748697594379651564699648 }, { target := 93, numerator := 4227771559885233435692761088 }, { target := 94, numerator := 5717271148599248062502666240 }, { target := 95, numerator := 233204481061285118338924544 }, { target := 161, numerator := 8161575409606833872077586432 }, { target := 162, numerator := 200090235848425604605773086720 }, { target := 163, numerator := 8161575409606833872077586432 }, { target := 164, numerator := 167707210836114618597207179264 }, { target := 165, numerator := 164811167948834774320018358272 }, { target := 166, numerator := 8161575409606833872077586432 }, { target := 167, numerator := 165074444574951123799762796544 }, { target := 168, numerator := 147961463877388407616374308864 }, { target := 169, numerator := 200090235848425604605773086720 }, { target := 170, numerator := 8161575409606833872077586432 }, { target := 232, numerator := 8161579412550297867050287104 }, { target := 233, numerator := 200090333985104076740587683840 }, { target := 234, numerator := 8161579412550297867050287104 }, { target := 235, numerator := 167707293090146443268097835008 }, { target := 236, numerator := 164811248782467305315273539584 }, { target := 237, numerator := 8161579412550297867050287104 }, { target := 238, numerator := 165074525537710863310984839168 }, { target := 239, numerator := 147961536446879593589750366208 }, { target := 240, numerator := 200090333985104076740587683840 }, { target := 241, numerator := 8161579412550297867050287104 }, { target := 406, numerator := 233202479589553120852574208 }, { target := 407, numerator := 5717222080260011995095367680 }, { target := 408, numerator := 233202479589553120852574208 }, { target := 409, numerator := 4791934822533720580099670016 }, { target := 410, numerator := 4709185555582588827539079168 }, { target := 411, numerator := 233202479589553120852574208 }, { target := 412, numerator := 4716708216214509895953678336 }, { target := 413, numerator := 4227735275139640449004732416 }, { target := 414, numerator := 5717222080260011995095367680 }, { target := 415, numerator := 233202479589553120852574208 }]

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
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 522374057046608719663595520 }, { target := 17, numerator := 13929974854576232524362547200 }, { target := 18, numerator := 13320538454688522351421685760 }, { target := 19, numerator := 435311714205507266386329600 }, { target := 20, numerator := 13668787826052928164530749440 }, { target := 21, numerator := 435311714205507266386329600 }, { target := 22, numerator := 13320538454688522351421685760 }, { target := 23, numerator := 7574423827175826435122135040 }, { target := 24, numerator := 13668787826052928164530749440 }, { target := 25, numerator := 213389802303539661982578769920 }, { target := 26, numerator := 8357984912745739514617528320 }, { target := 27, numerator := 13929974854576232524362547200 }, { target := 28, numerator := 13320538454688522351421685760 }, { target := 29, numerator := 435311714205507266386329600 }, { target := 30, numerator := 8357984912745739514617528320 }, { target := 31, numerator := 435311714205507266386329600 }, { target := 32, numerator := 13407600797529623804698951680 }, { target := 33, numerator := 7574423827175826435122135040 }, { target := 34, numerator := 522374057046608719663595520 }, { target := 145, numerator := 28118054117261591365275353088 }, { target := 146, numerator := 27532261323151974878498783232 }, { target := 147, numerator := 21674333382055810010733084672 }, { target := 148, numerator := 681277019549483974121150742528 }, { target := 149, numerator := 21674333382055810010733084672 }, { target := 150, numerator := 21674333382055810010733084672 }, { target := 151, numerator := 22260126176165426497509654528 }, { target := 152, numerator := 22260126176165426497509654528 }, { target := 153, numerator := 376664766612483400997334417408 }, { target := 154, numerator := 20502747793836577037179944960 }, { target := 155, numerator := 681277019549483974121150742528 }, { target := 156, numerator := 376664766612483400997334417408 }, { target := 157, numerator := 28118054117261591365275353088 }, { target := 158, numerator := 21674333382055810010733084672 }, { target := 159, numerator := 20502747793836577037179944960 }, { target := 160, numerator := 27532261323151974878498783232 }, { target := 216, numerator := 8223892320340475958458843136 }, { target := 217, numerator := 8052561230333382709324283904 }, { target := 218, numerator := 6339250330262450217978691584 }, { target := 219, numerator := 199258057678249448743492386816 }, { target := 220, numerator := 6339250330262450217978691584 }, { target := 221, numerator := 6339250330262450217978691584 }, { target := 222, numerator := 6510581420269543467113250816 }, { target := 223, numerator := 6510581420269543467113250816 }, { target := 224, numerator := 110165890874560959193521586176 }, { target := 225, numerator := 5996588150248263719709573120 }, { target := 226, numerator := 199258057678249448743492386816 }, { target := 227, numerator := 110165890874560959193521586176 }, { target := 228, numerator := 8223892320340475958458843136 }, { target := 229, numerator := 6339250330262450217978691584 }, { target := 230, numerator := 5996588150248263719709573120 }, { target := 231, numerator := 8052561230333382709324283904 }]

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
    Slot10.Left2.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 676998458984192337835458560 }, { target := 1, numerator := 696341272098026404630757376 }, { target := 2, numerator := 676998458984192337835458560 }, { target := 3, numerator := 599627206528856070654263296 }, { target := 4, numerator := 28066421828173230919978582016 }, { target := 5, numerator := 7640411179964456384143032320 }, { target := 6, numerator := 696341272098026404630757376 }, { target := 7, numerator := 28066421828173230919978582016 }, { target := 8, numerator := 676998458984192337835458560 }, { target := 9, numerator := 676998458984192337835458560 }, { target := 10, numerator := 580284393415022003858964480 }, { target := 11, numerator := 676998458984192337835458560 }, { target := 12, numerator := 7640411179964456384143032320 }, { target := 13, numerator := 580284393415022003858964480 }, { target := 14, numerator := 676998458984192337835458560 }, { target := 15, numerator := 599627206528856070654263296 }, { target := 126, numerator := 522137851100430887282540544 }, { target := 127, numerator := 13923676029344823660867747840 }, { target := 128, numerator := 13314515203060987625704783872 }, { target := 129, numerator := 435114875917025739402117120 }, { target := 130, numerator := 13662607103794608217226477568 }, { target := 131, numerator := 435114875917025739402117120 }, { target := 132, numerator := 13314515203060987625704783872 }, { target := 133, numerator := 7570998840956247865596837888 }, { target := 134, numerator := 13662607103794608217226477568 }, { target := 135, numerator := 213293312174526017454917812224 }, { target := 136, numerator := 8354205617606894196520648704 }, { target := 137, numerator := 13923676029344823660867747840 }, { target := 138, numerator := 13314515203060987625704783872 }, { target := 139, numerator := 435114875917025739402117120 }, { target := 140, numerator := 8354205617606894196520648704 }, { target := 141, numerator := 435114875917025739402117120 }, { target := 142, numerator := 13401538178244392773585207296 }, { target := 143, numerator := 7570998840956247865596837888 }, { target := 144, numerator := 522137851100430887282540544 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent0
