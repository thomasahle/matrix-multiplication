import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 48; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2

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
  [{ target := 142, numerator := 6148521160696278068232192 }, { target := 143, numerator := 92227817410444171023482880 }, { target := 144, numerator := 161911057231668655796781056 }, { target := 145, numerator := 6148521160696278068232192 }, { target := 146, numerator := 102475352678271301137203200 }, { target := 147, numerator := 6148521160696278068232192 }, { target := 148, numerator := 161911057231668655796781056 }, { target := 149, numerator := 160886303704885942785409024 }, { target := 150, numerator := 102475352678271301137203200 }, { target := 151, numerator := 2482977795394513626554433536 }, { target := 152, numerator := 158836796651320516762664960 }, { target := 153, numerator := 92227817410444171023482880 }, { target := 154, numerator := 161911057231668655796781056 }, { target := 155, numerator := 6148521160696278068232192 }, { target := 156, numerator := 158836796651320516762664960 }, { target := 157, numerator := 6148521160696278068232192 }, { target := 158, numerator := 161911057231668655796781056 }, { target := 159, numerator := 161911057231668655796781056 }, { target := 160, numerator := 6148521160696278068232192 }, { target := 282, numerator := 150737938133199075221176320 }, { target := 283, numerator := 2261069071997986128317644800 }, { target := 284, numerator := 3969432370840908980824309760 }, { target := 285, numerator := 150737938133199075221176320 }, { target := 286, numerator := 2512298968886651253686272000 }, { target := 287, numerator := 150737938133199075221176320 }, { target := 288, numerator := 3969432370840908980824309760 }, { target := 289, numerator := 3944309381152042468287447040 }, { target := 290, numerator := 2512298968886651253686272000 }, { target := 291, numerator := 60873004016123559876818370560 }, { target := 292, numerator := 3894063401774309443213721600 }, { target := 293, numerator := 2261069071997986128317644800 }, { target := 294, numerator := 3969432370840908980824309760 }, { target := 295, numerator := 150737938133199075221176320 }, { target := 296, numerator := 3894063401774309443213721600 }, { target := 297, numerator := 150737938133199075221176320 }, { target := 298, numerator := 3969432370840908980824309760 }, { target := 299, numerator := 3969432370840908980824309760 }, { target := 300, numerator := 150737938133199075221176320 }, { target := 357, numerator := 111466738461655105624080384 }, { target := 358, numerator := 1672001076924826584361205760 }, { target := 359, numerator := 2935290779490251114767450112 }, { target := 360, numerator := 111466738461655105624080384 }, { target := 361, numerator := 1857778974360918427068006400 }, { target := 362, numerator := 111466738461655105624080384 }, { target := 363, numerator := 2935290779490251114767450112 }, { target := 364, numerator := 2916712989746641930496770048 }, { target := 365, numerator := 1857778974360918427068006400 }, { target := 366, numerator := 45013984548765053487857795072 }, { target := 367, numerator := 2879557410259423561955409920 }, { target := 368, numerator := 1672001076924826584361205760 }, { target := 369, numerator := 2935290779490251114767450112 }, { target := 370, numerator := 111466738461655105624080384 }, { target := 371, numerator := 2879557410259423561955409920 }, { target := 372, numerator := 111466738461655105624080384 }, { target := 373, numerator := 2935290779490251114767450112 }, { target := 374, numerator := 2935290779490251114767450112 }, { target := 375, numerator := 111466738461655105624080384 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 392, numerator := 124358798959889237057470464 }, { target := 393, numerator := 1865381984398338555862056960 }, { target := 394, numerator := 3274781705943749909180055552 }, { target := 395, numerator := 124358798959889237057470464 }, { target := 396, numerator := 2072646649331487284291174400 }, { target := 397, numerator := 124358798959889237057470464 }, { target := 398, numerator := 3274781705943749909180055552 }, { target := 399, numerator := 3254055239450435036337143808 }, { target := 400, numerator := 2072646649331487284291174400 }, { target := 401, numerator := 50220228313301936898375155712 }, { target := 402, numerator := 3212602306463805290651320320 }, { target := 403, numerator := 1865381984398338555862056960 }, { target := 404, numerator := 3274781705943749909180055552 }, { target := 405, numerator := 124358798959889237057470464 }, { target := 406, numerator := 3212602306463805290651320320 }, { target := 407, numerator := 124358798959889237057470464 }, { target := 408, numerator := 3274781705943749909180055552 }, { target := 409, numerator := 3274781705943749909180055552 }, { target := 410, numerator := 124358798959889237057470464 }, { target := 498, numerator := 6148521160696278068232192 }, { target := 499, numerator := 92227817410444171023482880 }, { target := 500, numerator := 161911057231668655796781056 }, { target := 501, numerator := 6148521160696278068232192 }, { target := 502, numerator := 102475352678271301137203200 }, { target := 503, numerator := 6148521160696278068232192 }, { target := 504, numerator := 161911057231668655796781056 }, { target := 505, numerator := 160886303704885942785409024 }, { target := 506, numerator := 102475352678271301137203200 }, { target := 507, numerator := 2482977795394513626554433536 }, { target := 508, numerator := 158836796651320516762664960 }, { target := 509, numerator := 92227817410444171023482880 }, { target := 510, numerator := 161911057231668655796781056 }, { target := 511, numerator := 6148521160696278068232192 }, { target := 512, numerator := 158836796651320516762664960 }, { target := 513, numerator := 6148521160696278068232192 }, { target := 514, numerator := 161911057231668655796781056 }, { target := 515, numerator := 161911057231668655796781056 }, { target := 516, numerator := 6148521160696278068232192 }, { target := 573, numerator := 124160459567608711958495232 }, { target := 574, numerator := 1862406893514130679377428480 }, { target := 575, numerator := 3269558768613696081573707776 }, { target := 576, numerator := 124160459567608711958495232 }, { target := 577, numerator := 2069340992793478532641587200 }, { target := 578, numerator := 124160459567608711958495232 }, { target := 579, numerator := 3269558768613696081573707776 }, { target := 580, numerator := 3248865358685761296247291904 }, { target := 581, numerator := 2069340992793478532641587200 }, { target := 582, numerator := 50140132255385984845905657856 }, { target := 583, numerator := 3207478538829891725594460160 }, { target := 584, numerator := 1862406893514130679377428480 }, { target := 585, numerator := 3269558768613696081573707776 }, { target := 586, numerator := 124160459567608711958495232 }, { target := 587, numerator := 3207478538829891725594460160 }, { target := 588, numerator := 124160459567608711958495232 }, { target := 589, numerator := 3269558768613696081573707776 }, { target := 590, numerator := 3269558768613696081573707776 }, { target := 591, numerator := 124160459567608711958495232 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 608, numerator := 126342192882694488047222784 }, { target := 609, numerator := 1895132893240417320708341760 }, { target := 610, numerator := 3327011079244288185243533312 }, { target := 611, numerator := 126342192882694488047222784 }, { target := 612, numerator := 2105703214711574800787046400 }, { target := 613, numerator := 126342192882694488047222784 }, { target := 614, numerator := 3327011079244288185243533312 }, { target := 615, numerator := 3305954047097172437235662848 }, { target := 616, numerator := 2105703214711574800787046400 }, { target := 617, numerator := 51021188892461457423070134272 }, { target := 618, numerator := 3263839982802940941219921920 }, { target := 619, numerator := 1895132893240417320708341760 }, { target := 620, numerator := 3327011079244288185243533312 }, { target := 621, numerator := 126342192882694488047222784 }, { target := 622, numerator := 3263839982802940941219921920 }, { target := 623, numerator := 126342192882694488047222784 }, { target := 624, numerator := 3327011079244288185243533312 }, { target := 625, numerator := 3327011079244288185243533312 }, { target := 626, numerator := 126342192882694488047222784 }, { target := 669, numerator := 6148521160696278068232192 }, { target := 670, numerator := 92227817410444171023482880 }, { target := 671, numerator := 161911057231668655796781056 }, { target := 672, numerator := 6148521160696278068232192 }, { target := 673, numerator := 102475352678271301137203200 }, { target := 674, numerator := 6148521160696278068232192 }, { target := 675, numerator := 161911057231668655796781056 }, { target := 676, numerator := 160886303704885942785409024 }, { target := 677, numerator := 102475352678271301137203200 }, { target := 678, numerator := 2482977795394513626554433536 }, { target := 679, numerator := 158836796651320516762664960 }, { target := 680, numerator := 92227817410444171023482880 }, { target := 681, numerator := 161911057231668655796781056 }, { target := 682, numerator := 6148521160696278068232192 }, { target := 683, numerator := 158836796651320516762664960 }, { target := 684, numerator := 6148521160696278068232192 }, { target := 685, numerator := 161911057231668655796781056 }, { target := 686, numerator := 161911057231668655796781056 }, { target := 687, numerator := 6148521160696278068232192 }, { target := 704, numerator := 150737938133199075221176320 }, { target := 705, numerator := 2261069071997986128317644800 }, { target := 706, numerator := 3969432370840908980824309760 }, { target := 707, numerator := 150737938133199075221176320 }, { target := 708, numerator := 2512298968886651253686272000 }, { target := 709, numerator := 150737938133199075221176320 }, { target := 710, numerator := 3969432370840908980824309760 }, { target := 711, numerator := 3944309381152042468287447040 }, { target := 712, numerator := 2512298968886651253686272000 }, { target := 713, numerator := 60873004016123559876818370560 }, { target := 714, numerator := 3894063401774309443213721600 }, { target := 715, numerator := 2261069071997986128317644800 }, { target := 716, numerator := 3969432370840908980824309760 }, { target := 717, numerator := 150737938133199075221176320 }, { target := 718, numerator := 3894063401774309443213721600 }, { target := 719, numerator := 150737938133199075221176320 }, { target := 720, numerator := 3969432370840908980824309760 }, { target := 721, numerator := 3969432370840908980824309760 }, { target := 722, numerator := 150737938133199075221176320 }]

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
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 116444149628087859098419200 }, { target := 56, numerator := 87333112221065894323814400 }, { target := 57, numerator := 92184951788902888452915200 }, { target := 58, numerator := 118870069412006356162969600 }, { target := 59, numerator := 1591403378250534074345062400 }, { target := 60, numerator := 2782529992154516133039308800 }, { target := 61, numerator := 84907192437147397259264000 }, { target := 62, numerator := 1591403378250534074345062400 }, { target := 63, numerator := 89759032004984391388364800 }, { target := 64, numerator := 92184951788902888452915200 }, { target := 65, numerator := 92184951788902888452915200 }, { target := 66, numerator := 89759032004984391388364800 }, { target := 67, numerator := 2782529992154516133039308800 }, { target := 68, numerator := 89759032004984391388364800 }, { target := 69, numerator := 116444149628087859098419200 }, { target := 70, numerator := 118870069412006356162969600 }, { target := 411, numerator := 1242608628897589038342471680 }, { target := 413, numerator := 48468426999672496304768942080 }, { target := 416, numerator := 48468409221622895267188572160 }, { target := 423, numerator := 1242614554914122717535928320 }, { target := 627, numerator := 1238982339124541599514624000 }, { target := 629, numerator := 48326982173797965673529344000 }, { target := 632, numerator := 48326964447629832343257088000 }, { target := 639, numerator := 1238988247847252709605376000 }, { target := 723, numerator := 1230520996320764242249646080 }, { target := 725, numerator := 47996944246757394200636948480 }, { target := 728, numerator := 47996926641646018854083624960 }, { target := 735, numerator := 1230526864691222691100753920 }, { target := 739, numerator := 6148521160696278068232192 }, { target := 740, numerator := 92227817410444171023482880 }, { target := 741, numerator := 161911057231668655796781056 }, { target := 742, numerator := 6148521160696278068232192 }, { target := 743, numerator := 102475352678271301137203200 }, { target := 744, numerator := 6148521160696278068232192 }, { target := 745, numerator := 161911057231668655796781056 }, { target := 746, numerator := 160886303704885942785409024 }, { target := 747, numerator := 102475352678271301137203200 }, { target := 748, numerator := 2482977795394513626554433536 }, { target := 749, numerator := 158836796651320516762664960 }, { target := 750, numerator := 92227817410444171023482880 }, { target := 751, numerator := 161911057231668655796781056 }, { target := 752, numerator := 6148521160696278068232192 }, { target := 753, numerator := 158836796651320516762664960 }, { target := 754, numerator := 6148521160696278068232192 }, { target := 755, numerator := 161911057231668655796781056 }, { target := 756, numerator := 161911057231668655796781056 }, { target := 757, numerator := 6148521160696278068232192 }, { target := 758, numerator := 1238982339124541599514624000 }, { target := 760, numerator := 48326982173797965673529344000 }, { target := 763, numerator := 48326964447629832343257088000 }, { target := 770, numerator := 1238988247847252709605376000 }, { target := 774, numerator := 70777719089126768096250429440 }, { target := 777, numerator := 254585350781235737426992824320 }, { target := 779, numerator := 70777742700959182444476497920 }]

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
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 100, numerator := 23094931586972792295260160000 }, { target := 101, numerator := 17321198690229594221445120000 }, { target := 102, numerator := 18283487506353460567080960000 }, { target := 103, numerator := 23576075995034725468078080000 }, { target := 104, numerator := 315630731688628161368555520000 }, { target := 105, numerator := 551872636047037349222154240000 }, { target := 106, numerator := 16840054282167661048627200000 }, { target := 107, numerator := 315630731688628161368555520000 }, { target := 108, numerator := 17802343098291527394263040000 }, { target := 109, numerator := 18283487506353460567080960000 }, { target := 110, numerator := 18283487506353460567080960000 }, { target := 111, numerator := 17802343098291527394263040000 }, { target := 112, numerator := 551872636047037349222154240000 }, { target := 113, numerator := 17802343098291527394263040000 }, { target := 114, numerator := 23094931586972792295260160000 }, { target := 115, numerator := 23576075995034725468078080000 }, { target := 142, numerator := 44428554304801733867470848 }, { target := 143, numerator := 5251169877136502986477928448 }, { target := 145, numerator := 49832555383456092040124694528 }, { target := 153, numerator := 5251173478673006294011478016 }, { target := 160, numerator := 44428554304801733867470848 }, { target := 315, numerator := 23094931586972792295260160000 }, { target := 316, numerator := 17321198690229594221445120000 }, { target := 317, numerator := 18283487506353460567080960000 }, { target := 318, numerator := 23576075995034725468078080000 }, { target := 319, numerator := 315630731688628161368555520000 }, { target := 320, numerator := 551872636047037349222154240000 }, { target := 321, numerator := 16840054282167661048627200000 }, { target := 322, numerator := 315630731688628161368555520000 }, { target := 323, numerator := 17802343098291527394263040000 }, { target := 324, numerator := 18283487506353460567080960000 }, { target := 325, numerator := 18283487506353460567080960000 }, { target := 326, numerator := 17802343098291527394263040000 }, { target := 327, numerator := 551872636047037349222154240000 }, { target := 328, numerator := 17802343098291527394263040000 }, { target := 329, numerator := 23094931586972792295260160000 }, { target := 330, numerator := 23576075995034725468078080000 }, { target := 357, numerator := 2008089828341219403547803648 }, { target := 358, numerator := 237343325304419436954541621248 }, { target := 360, numerator := 2252340845917498409681135075328 }, { target := 368, numerator := 237343488087317324537178095616 }, { target := 375, numerator := 2008089828341219403547803648 }, { target := 653, numerator := 116444149628087859098419200 }, { target := 654, numerator := 87333112221065894323814400 }, { target := 655, numerator := 92184951788902888452915200 }, { target := 656, numerator := 118870069412006356162969600 }, { target := 657, numerator := 1591403378250534074345062400 }, { target := 658, numerator := 2782529992154516133039308800 }, { target := 659, numerator := 84907192437147397259264000 }, { target := 660, numerator := 1591403378250534074345062400 }, { target := 661, numerator := 89759032004984391388364800 }, { target := 662, numerator := 92184951788902888452915200 }, { target := 663, numerator := 92184951788902888452915200 }, { target := 664, numerator := 89759032004984391388364800 }, { target := 665, numerator := 2782529992154516133039308800 }, { target := 666, numerator := 89759032004984391388364800 }, { target := 667, numerator := 116444149628087859098419200 }, { target := 668, numerator := 118870069412006356162969600 }, { target := 669, numerator := 44665682930456823406264320 }, { target := 670, numerator := 5279196958267797095653048320 }, { target := 672, numerator := 50098526796567838344106475520 }, { target := 680, numerator := 5279200579026789512710717440 }, { target := 687, numerator := 44665682930456823406264320 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 6184547651872232822538240 }, { target := 12, numerator := 149825654405033769346007040 }, { target := 13, numerator := 113516374642429047613685760 }, { target := 14, numerator := 126483974557645019660943360 }, { target := 15, numerator := 6184547651872232822538240 }, { target := 16, numerator := 126483974557645019660943360 }, { target := 17, numerator := 126284473020487850860216320 }, { target := 18, numerator := 6184547651872232822538240 }, { target := 19, numerator := 149825654405033769346007040 }, { target := 20, numerator := 6184547651872232822538240 }, { target := 31, numerator := 1992174895802358026238689280 }, { target := 32, numerator := 48262043443470028313072762880 }, { target := 33, numerator := 36566048893920700546123038720 }, { target := 34, numerator := 40743189804474031891462225920 }, { target := 35, numerator := 1992174895802358026238689280 }, { target := 36, numerator := 40743189804474031891462225920 }, { target := 37, numerator := 40678926098157826793841623040 }, { target := 38, numerator := 1992174895802358026238689280 }, { target := 39, numerator := 48262043443470028313072762880 }, { target := 40, numerator := 1992174895802358026238689280 }, { target := 76, numerator := 21187617782888298456897552384 }, { target := 77, numerator := 513287127579003617455808446464 }, { target := 78, numerator := 388895307047207800708861526016 }, { target := 79, numerator := 433320957237134878118485426176 }, { target := 80, numerator := 21187617782888298456897552384 }, { target := 81, numerator := 433320957237134878118485426176 }, { target := 82, numerator := 432637485695751384619875827712 }, { target := 83, numerator := 21187617782888298456897552384 }, { target := 84, numerator := 513287127579003617455808446464 }, { target := 85, numerator := 21187617782888298456897552384 }, { target := 305, numerator := 1992180900217554018697740288 }, { target := 306, numerator := 48262188905270421549742030848 }, { target := 307, numerator := 36566159103993168923839168512 }, { target := 308, numerator := 40743312604449330575947333632 }, { target := 309, numerator := 1992180900217554018697740288 }, { target := 310, numerator := 40743312604449330575947333632 }, { target := 311, numerator := 40679048704442312704376438784 }, { target := 312, numerator := 1992180900217554018697740288 }, { target := 313, numerator := 48262188905270421549742030848 }, { target := 314, numerator := 1992180900217554018697740288 }, { target := 411, numerator := 3701331819692192047929753600 }, { target := 413, numerator := 144851472894553440939965153280 }, { target := 416, numerator := 144851472894553440939965153280 }, { target := 423, numerator := 3701331819692192047929753600 }, { target := 627, numerator := 3701331819692192047929753600 }, { target := 629, numerator := 144851472894553440939965153280 }, { target := 632, numerator := 144851472894553440939965153280 }, { target := 639, numerator := 3701331819692192047929753600 }, { target := 723, numerator := 3701331819692192047929753600 }, { target := 725, numerator := 144851472894553440939965153280 }, { target := 728, numerator := 144851472894553440939965153280 }, { target := 735, numerator := 3701331819692192047929753600 }, { target := 758, numerator := 3701331819692192047929753600 }, { target := 760, numerator := 144851472894553440939965153280 }, { target := 763, numerator := 144851472894553440939965153280 }, { target := 770, numerator := 3701331819692192047929753600 }]

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
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 68753125913166554597425152 }, { target := 56, numerator := 12058652346681746186500571136 }, { target := 61, numerator := 12058653792381136668796649472 }, { target := 69, numerator := 68751680213776072301346816 }, { target := 100, numerator := 12058652346681746186500571136 }, { target := 101, numerator := 2114974330065860456098088091648 }, { target := 106, numerator := 2114974583627951140576633552896 }, { target := 114, numerator := 12058398784591061707955109888 }, { target := 142, numerator := 6184547651872232822538240 }, { target := 143, numerator := 1992174895802358026238689280 }, { target := 145, numerator := 21187617782888298456897552384 }, { target := 153, numerator := 1992180900217554018697740288 }, { target := 160, numerator := 6184547651872232822538240 }, { target := 282, numerator := 149825654405033769346007040 }, { target := 283, numerator := 48262043443470028313072762880 }, { target := 285, numerator := 513287127579003617455808446464 }, { target := 293, numerator := 48262188905270421549742030848 }, { target := 300, numerator := 149825654405033769346007040 }, { target := 315, numerator := 12058653792381136668796649472 }, { target := 316, numerator := 2114974583627951140576633552896 }, { target := 321, numerator := 2114974837190072224352663764992 }, { target := 329, numerator := 12058400230260052892766437376 }, { target := 357, numerator := 113516374642429047613685760 }, { target := 358, numerator := 36566048893920700546123038720 }, { target := 360, numerator := 388895307047207800708861526016 }, { target := 368, numerator := 36566159103993168923839168512 }, { target := 375, numerator := 113516374642429047613685760 }, { target := 392, numerator := 126483974557645019660943360 }, { target := 393, numerator := 40743189804474031891462225920 }, { target := 395, numerator := 433320957237134878118485426176 }, { target := 403, numerator := 40743312604449330575947333632 }, { target := 410, numerator := 126483974557645019660943360 }, { target := 498, numerator := 6184547651872232822538240 }, { target := 499, numerator := 1992174895802358026238689280 }, { target := 501, numerator := 21187617782888298456897552384 }, { target := 509, numerator := 1992180900217554018697740288 }, { target := 516, numerator := 6184547651872232822538240 }, { target := 573, numerator := 126483974557645019660943360 }, { target := 574, numerator := 40743189804474031891462225920 }, { target := 576, numerator := 433320957237134878118485426176 }, { target := 584, numerator := 40743312604449330575947333632 }, { target := 591, numerator := 126483974557645019660943360 }, { target := 608, numerator := 126284473020487850860216320 }, { target := 609, numerator := 40678926098157826793841623040 }, { target := 611, numerator := 432637485695751384619875827712 }, { target := 619, numerator := 40679048704442312704376438784 }, { target := 626, numerator := 126284473020487850860216320 }, { target := 643, numerator := 6184547651872232822538240 }, { target := 644, numerator := 149825654405033769346007040 }, { target := 645, numerator := 113516374642429047613685760 }, { target := 646, numerator := 126483974557645019660943360 }, { target := 647, numerator := 6184547651872232822538240 }, { target := 648, numerator := 126483974557645019660943360 }, { target := 649, numerator := 126284473020487850860216320 }, { target := 650, numerator := 6184547651872232822538240 }, { target := 651, numerator := 149825654405033769346007040 }, { target := 652, numerator := 6184547651872232822538240 }, { target := 653, numerator := 68751680213776072301346816 }, { target := 654, numerator := 12058398784591061707955109888 }, { target := 659, numerator := 12058400230260052892766437376 }, { target := 667, numerator := 68750234544784887490019328 }]

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
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 3701331819692192047929753600 }, { target := 3, numerator := 3701331819692192047929753600 }, { target := 4, numerator := 3701331819692192047929753600 }, { target := 5, numerator := 3701331819692192047929753600 }, { target := 11, numerator := 44428554304801733867470848 }, { target := 13, numerator := 2008089828341219403547803648 }, { target := 18, numerator := 44665682930456823406264320 }, { target := 22, numerator := 144851472894553440939965153280 }, { target := 23, numerator := 144851472894553440939965153280 }, { target := 24, numerator := 144851472894553440939965153280 }, { target := 25, numerator := 144851472894553440939965153280 }, { target := 31, numerator := 5251169877136502986477928448 }, { target := 33, numerator := 237343325304419436954541621248 }, { target := 38, numerator := 5279196958267797095653048320 }, { target := 55, numerator := 116444149628087859098419200 }, { target := 56, numerator := 23094931586972792295260160000 }, { target := 61, numerator := 23094931586972792295260160000 }, { target := 69, numerator := 116444149628087859098419200 }, { target := 72, numerator := 144851472894553440939965153280 }, { target := 73, numerator := 144851472894553440939965153280 }, { target := 74, numerator := 144851472894553440939965153280 }, { target := 75, numerator := 144851472894553440939965153280 }, { target := 76, numerator := 49832555383456092040124694528 }, { target := 78, numerator := 2252340845917498409681135075328 }, { target := 83, numerator := 50098526796567838344106475520 }, { target := 100, numerator := 87333112221065894323814400 }, { target := 101, numerator := 17321198690229594221445120000 }, { target := 106, numerator := 17321198690229594221445120000 }, { target := 114, numerator := 87333112221065894323814400 }, { target := 126, numerator := 92184951788902888452915200 }, { target := 127, numerator := 18283487506353460567080960000 }, { target := 132, numerator := 18283487506353460567080960000 }, { target := 140, numerator := 92184951788902888452915200 }, { target := 195, numerator := 118870069412006356162969600 }, { target := 196, numerator := 23576075995034725468078080000 }, { target := 201, numerator := 23576075995034725468078080000 }, { target := 209, numerator := 118870069412006356162969600 }, { target := 301, numerator := 3701331819692192047929753600 }, { target := 302, numerator := 3701331819692192047929753600 }, { target := 303, numerator := 3701331819692192047929753600 }, { target := 304, numerator := 3701331819692192047929753600 }, { target := 305, numerator := 5251173478673006294011478016 }, { target := 307, numerator := 237343488087317324537178095616 }, { target := 312, numerator := 5279200579026789512710717440 }, { target := 643, numerator := 44428554304801733867470848 }, { target := 645, numerator := 2008089828341219403547803648 }, { target := 650, numerator := 44665682930456823406264320 }, { target := 669, numerator := 6184547651872232822538240 }, { target := 670, numerator := 1992174895802358026238689280 }, { target := 672, numerator := 21187617782888298456897552384 }, { target := 680, numerator := 1992180900217554018697740288 }, { target := 687, numerator := 6184547651872232822538240 }, { target := 704, numerator := 149825654405033769346007040 }, { target := 705, numerator := 48262043443470028313072762880 }, { target := 707, numerator := 513287127579003617455808446464 }, { target := 715, numerator := 48262188905270421549742030848 }, { target := 722, numerator := 149825654405033769346007040 }, { target := 739, numerator := 6184547651872232822538240 }, { target := 740, numerator := 1992174895802358026238689280 }, { target := 742, numerator := 21187617782888298456897552384 }, { target := 750, numerator := 1992180900217554018697740288 }, { target := 757, numerator := 6184547651872232822538240 }]

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
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 70777719089126768096250429440 }, { target := 2, numerator := 1242608628897589038342471680 }, { target := 3, numerator := 1238982339124541599514624000 }, { target := 4, numerator := 1230520996320764242249646080 }, { target := 5, numerator := 1238982339124541599514624000 }, { target := 21, numerator := 254585350781235737426992824320 }, { target := 22, numerator := 48468426999672496304768942080 }, { target := 23, numerator := 48326982173797965673529344000 }, { target := 24, numerator := 47996944246757394200636948480 }, { target := 25, numerator := 48326982173797965673529344000 }, { target := 71, numerator := 70777742700959182444476497920 }, { target := 72, numerator := 48468409221622895267188572160 }, { target := 73, numerator := 48326964447629832343257088000 }, { target := 74, numerator := 47996926641646018854083624960 }, { target := 75, numerator := 48326964447629832343257088000 }, { target := 240, numerator := 1591403378250534074345062400 }, { target := 241, numerator := 315630731688628161368555520000 }, { target := 246, numerator := 315630731688628161368555520000 }, { target := 254, numerator := 1591403378250534074345062400 }, { target := 266, numerator := 2782529992154516133039308800 }, { target := 267, numerator := 551872636047037349222154240000 }, { target := 272, numerator := 551872636047037349222154240000 }, { target := 280, numerator := 2782529992154516133039308800 }, { target := 315, numerator := 84907192437147397259264000 }, { target := 316, numerator := 16840054282167661048627200000 }, { target := 321, numerator := 16840054282167661048627200000 }, { target := 329, numerator := 84907192437147397259264000 }, { target := 341, numerator := 1591403378250534074345062400 }, { target := 342, numerator := 315630731688628161368555520000 }, { target := 347, numerator := 315630731688628161368555520000 }, { target := 355, numerator := 1591403378250534074345062400 }, { target := 376, numerator := 89759032004984391388364800 }, { target := 377, numerator := 17802343098291527394263040000 }, { target := 382, numerator := 17802343098291527394263040000 }, { target := 390, numerator := 89759032004984391388364800 }, { target := 456, numerator := 92184951788902888452915200 }, { target := 457, numerator := 18283487506353460567080960000 }, { target := 462, numerator := 18283487506353460567080960000 }, { target := 470, numerator := 92184951788902888452915200 }, { target := 482, numerator := 92184951788902888452915200 }, { target := 483, numerator := 18283487506353460567080960000 }, { target := 488, numerator := 18283487506353460567080960000 }, { target := 496, numerator := 92184951788902888452915200 }, { target := 531, numerator := 89759032004984391388364800 }, { target := 532, numerator := 17802343098291527394263040000 }, { target := 537, numerator := 17802343098291527394263040000 }, { target := 545, numerator := 89759032004984391388364800 }, { target := 557, numerator := 2782529992154516133039308800 }, { target := 558, numerator := 551872636047037349222154240000 }, { target := 563, numerator := 551872636047037349222154240000 }, { target := 571, numerator := 2782529992154516133039308800 }, { target := 592, numerator := 89759032004984391388364800 }, { target := 593, numerator := 17802343098291527394263040000 }, { target := 598, numerator := 17802343098291527394263040000 }, { target := 606, numerator := 89759032004984391388364800 }, { target := 653, numerator := 116444149628087859098419200 }, { target := 654, numerator := 23094931586972792295260160000 }, { target := 659, numerator := 23094931586972792295260160000 }, { target := 667, numerator := 116444149628087859098419200 }, { target := 688, numerator := 118870069412006356162969600 }, { target := 689, numerator := 23576075995034725468078080000 }, { target := 694, numerator := 23576075995034725468078080000 }, { target := 702, numerator := 118870069412006356162969600 }]

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
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 6148521160696278068232192 }, { target := 12, numerator := 150737938133199075221176320 }, { target := 13, numerator := 111466738461655105624080384 }, { target := 14, numerator := 124358798959889237057470464 }, { target := 15, numerator := 6148521160696278068232192 }, { target := 16, numerator := 124160459567608711958495232 }, { target := 17, numerator := 126342192882694488047222784 }, { target := 18, numerator := 6148521160696278068232192 }, { target := 19, numerator := 150737938133199075221176320 }, { target := 20, numerator := 6148521160696278068232192 }, { target := 31, numerator := 92227817410444171023482880 }, { target := 32, numerator := 2261069071997986128317644800 }, { target := 33, numerator := 1672001076924826584361205760 }, { target := 34, numerator := 1865381984398338555862056960 }, { target := 35, numerator := 92227817410444171023482880 }, { target := 36, numerator := 1862406893514130679377428480 }, { target := 37, numerator := 1895132893240417320708341760 }, { target := 38, numerator := 92227817410444171023482880 }, { target := 39, numerator := 2261069071997986128317644800 }, { target := 40, numerator := 92227817410444171023482880 }, { target := 45, numerator := 161911057231668655796781056 }, { target := 46, numerator := 3969432370840908980824309760 }, { target := 47, numerator := 2935290779490251114767450112 }, { target := 48, numerator := 3274781705943749909180055552 }, { target := 49, numerator := 161911057231668655796781056 }, { target := 50, numerator := 3269558768613696081573707776 }, { target := 51, numerator := 3327011079244288185243533312 }, { target := 52, numerator := 161911057231668655796781056 }, { target := 53, numerator := 3969432370840908980824309760 }, { target := 54, numerator := 161911057231668655796781056 }, { target := 76, numerator := 6148521160696278068232192 }, { target := 77, numerator := 150737938133199075221176320 }, { target := 78, numerator := 111466738461655105624080384 }, { target := 79, numerator := 124358798959889237057470464 }, { target := 80, numerator := 6148521160696278068232192 }, { target := 81, numerator := 124160459567608711958495232 }, { target := 82, numerator := 126342192882694488047222784 }, { target := 83, numerator := 6148521160696278068232192 }, { target := 84, numerator := 150737938133199075221176320 }, { target := 85, numerator := 6148521160696278068232192 }, { target := 90, numerator := 102475352678271301137203200 }, { target := 91, numerator := 2512298968886651253686272000 }, { target := 92, numerator := 1857778974360918427068006400 }, { target := 93, numerator := 2072646649331487284291174400 }, { target := 94, numerator := 102475352678271301137203200 }, { target := 95, numerator := 2069340992793478532641587200 }, { target := 96, numerator := 2105703214711574800787046400 }, { target := 97, numerator := 102475352678271301137203200 }, { target := 98, numerator := 2512298968886651253686272000 }, { target := 99, numerator := 102475352678271301137203200 }, { target := 116, numerator := 6148521160696278068232192 }, { target := 117, numerator := 150737938133199075221176320 }, { target := 118, numerator := 111466738461655105624080384 }, { target := 119, numerator := 124358798959889237057470464 }, { target := 120, numerator := 6148521160696278068232192 }, { target := 121, numerator := 124160459567608711958495232 }, { target := 122, numerator := 126342192882694488047222784 }, { target := 123, numerator := 6148521160696278068232192 }, { target := 124, numerator := 150737938133199075221176320 }, { target := 125, numerator := 6148521160696278068232192 }, { target := 301, numerator := 1242614554914122717535928320 }, { target := 302, numerator := 1238988247847252709605376000 }, { target := 303, numerator := 1230526864691222691100753920 }, { target := 304, numerator := 1238988247847252709605376000 }]

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

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 161911057231668655796781056 }, { target := 172, numerator := 3969432370840908980824309760 }, { target := 173, numerator := 2935290779490251114767450112 }, { target := 174, numerator := 3274781705943749909180055552 }, { target := 175, numerator := 161911057231668655796781056 }, { target := 176, numerator := 3269558768613696081573707776 }, { target := 177, numerator := 3327011079244288185243533312 }, { target := 178, numerator := 161911057231668655796781056 }, { target := 179, numerator := 3969432370840908980824309760 }, { target := 180, numerator := 161911057231668655796781056 }, { target := 185, numerator := 160886303704885942785409024 }, { target := 186, numerator := 3944309381152042468287447040 }, { target := 187, numerator := 2916712989746641930496770048 }, { target := 188, numerator := 3254055239450435036337143808 }, { target := 189, numerator := 160886303704885942785409024 }, { target := 190, numerator := 3248865358685761296247291904 }, { target := 191, numerator := 3305954047097172437235662848 }, { target := 192, numerator := 160886303704885942785409024 }, { target := 193, numerator := 3944309381152042468287447040 }, { target := 194, numerator := 160886303704885942785409024 }, { target := 216, numerator := 102475352678271301137203200 }, { target := 217, numerator := 2512298968886651253686272000 }, { target := 218, numerator := 1857778974360918427068006400 }, { target := 219, numerator := 2072646649331487284291174400 }, { target := 220, numerator := 102475352678271301137203200 }, { target := 221, numerator := 2069340992793478532641587200 }, { target := 222, numerator := 2105703214711574800787046400 }, { target := 223, numerator := 102475352678271301137203200 }, { target := 224, numerator := 2512298968886651253686272000 }, { target := 225, numerator := 102475352678271301137203200 }, { target := 230, numerator := 2482977795394513626554433536 }, { target := 231, numerator := 60873004016123559876818370560 }, { target := 232, numerator := 45013984548765053487857795072 }, { target := 233, numerator := 50220228313301936898375155712 }, { target := 234, numerator := 2482977795394513626554433536 }, { target := 235, numerator := 50140132255385984845905657856 }, { target := 236, numerator := 51021188892461457423070134272 }, { target := 237, numerator := 2482977795394513626554433536 }, { target := 238, numerator := 60873004016123559876818370560 }, { target := 239, numerator := 2482977795394513626554433536 }, { target := 256, numerator := 158836796651320516762664960 }, { target := 257, numerator := 3894063401774309443213721600 }, { target := 258, numerator := 2879557410259423561955409920 }, { target := 259, numerator := 3212602306463805290651320320 }, { target := 260, numerator := 158836796651320516762664960 }, { target := 261, numerator := 3207478538829891725594460160 }, { target := 262, numerator := 3263839982802940941219921920 }, { target := 263, numerator := 158836796651320516762664960 }, { target := 264, numerator := 3894063401774309443213721600 }, { target := 265, numerator := 158836796651320516762664960 }, { target := 305, numerator := 92227817410444171023482880 }, { target := 306, numerator := 2261069071997986128317644800 }, { target := 307, numerator := 1672001076924826584361205760 }, { target := 308, numerator := 1865381984398338555862056960 }, { target := 309, numerator := 92227817410444171023482880 }, { target := 310, numerator := 1862406893514130679377428480 }, { target := 311, numerator := 1895132893240417320708341760 }, { target := 312, numerator := 92227817410444171023482880 }, { target := 313, numerator := 2261069071997986128317644800 }, { target := 314, numerator := 92227817410444171023482880 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 331, numerator := 161911057231668655796781056 }, { target := 332, numerator := 3969432370840908980824309760 }, { target := 333, numerator := 2935290779490251114767450112 }, { target := 334, numerator := 3274781705943749909180055552 }, { target := 335, numerator := 161911057231668655796781056 }, { target := 336, numerator := 3269558768613696081573707776 }, { target := 337, numerator := 3327011079244288185243533312 }, { target := 338, numerator := 161911057231668655796781056 }, { target := 339, numerator := 3969432370840908980824309760 }, { target := 340, numerator := 161911057231668655796781056 }, { target := 432, numerator := 6148521160696278068232192 }, { target := 433, numerator := 150737938133199075221176320 }, { target := 434, numerator := 111466738461655105624080384 }, { target := 435, numerator := 124358798959889237057470464 }, { target := 436, numerator := 6148521160696278068232192 }, { target := 437, numerator := 124160459567608711958495232 }, { target := 438, numerator := 126342192882694488047222784 }, { target := 439, numerator := 6148521160696278068232192 }, { target := 440, numerator := 150737938133199075221176320 }, { target := 441, numerator := 6148521160696278068232192 }, { target := 446, numerator := 158836796651320516762664960 }, { target := 447, numerator := 3894063401774309443213721600 }, { target := 448, numerator := 2879557410259423561955409920 }, { target := 449, numerator := 3212602306463805290651320320 }, { target := 450, numerator := 158836796651320516762664960 }, { target := 451, numerator := 3207478538829891725594460160 }, { target := 452, numerator := 3263839982802940941219921920 }, { target := 453, numerator := 158836796651320516762664960 }, { target := 454, numerator := 3894063401774309443213721600 }, { target := 455, numerator := 158836796651320516762664960 }, { target := 472, numerator := 6148521160696278068232192 }, { target := 473, numerator := 150737938133199075221176320 }, { target := 474, numerator := 111466738461655105624080384 }, { target := 475, numerator := 124358798959889237057470464 }, { target := 476, numerator := 6148521160696278068232192 }, { target := 477, numerator := 124160459567608711958495232 }, { target := 478, numerator := 126342192882694488047222784 }, { target := 479, numerator := 6148521160696278068232192 }, { target := 480, numerator := 150737938133199075221176320 }, { target := 481, numerator := 6148521160696278068232192 }, { target := 521, numerator := 161911057231668655796781056 }, { target := 522, numerator := 3969432370840908980824309760 }, { target := 523, numerator := 2935290779490251114767450112 }, { target := 524, numerator := 3274781705943749909180055552 }, { target := 525, numerator := 161911057231668655796781056 }, { target := 526, numerator := 3269558768613696081573707776 }, { target := 527, numerator := 3327011079244288185243533312 }, { target := 528, numerator := 161911057231668655796781056 }, { target := 529, numerator := 3969432370840908980824309760 }, { target := 530, numerator := 161911057231668655796781056 }, { target := 547, numerator := 161911057231668655796781056 }, { target := 548, numerator := 3969432370840908980824309760 }, { target := 549, numerator := 2935290779490251114767450112 }, { target := 550, numerator := 3274781705943749909180055552 }, { target := 551, numerator := 161911057231668655796781056 }, { target := 552, numerator := 3269558768613696081573707776 }, { target := 553, numerator := 3327011079244288185243533312 }, { target := 554, numerator := 161911057231668655796781056 }, { target := 555, numerator := 3969432370840908980824309760 }, { target := 556, numerator := 161911057231668655796781056 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 643, numerator := 6148521160696278068232192 }, { target := 644, numerator := 150737938133199075221176320 }, { target := 645, numerator := 111466738461655105624080384 }, { target := 646, numerator := 124358798959889237057470464 }, { target := 647, numerator := 6148521160696278068232192 }, { target := 648, numerator := 124160459567608711958495232 }, { target := 649, numerator := 126342192882694488047222784 }, { target := 650, numerator := 6148521160696278068232192 }, { target := 651, numerator := 150737938133199075221176320 }, { target := 652, numerator := 6148521160696278068232192 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2
