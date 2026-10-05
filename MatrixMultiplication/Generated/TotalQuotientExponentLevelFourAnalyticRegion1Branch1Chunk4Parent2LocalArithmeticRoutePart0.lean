import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 9211353983090754035122176 }, { target := 15, numerator := 1615584947578970856769978368 }, { target := 20, numerator := 1615585141269783630720270336 }, { target := 28, numerator := 9211160292277980084830208 }, { target := 40, numerator := 192287014397019490483175424 }, { target := 41, numerator := 33725335780711016635073298432 }, { target := 46, numerator := 33725339824006733291285643264 }, { target := 54, numerator := 192282971101302834270830592 }, { target := 56, numerator := 67882773036026174552145920 }, { target := 57, numerator := 21866491118211596430857994240 }, { target := 59, numerator := 232559328521702514014994563072 }, { target := 67, numerator := 21866557023816485776658530304 }, { target := 74, numerator := 67882773036026174552145920 }, { target := 75, numerator := 9978966815014983538049024 }, { target := 76, numerator := 1750217026543885094834143232 }, { target := 81, numerator := 1750217236375598933280292864 }, { target := 89, numerator := 9978756983301145091899392 }, { target := 91, numerator := 76641840524545680945971200 }, { target := 92, numerator := 24687973843142125002581606400 }, { target := 94, numerator := 262566983814825419049187409920 }, { target := 102, numerator := 24688048252696032328485437440 }, { target := 109, numerator := 76641840524545680945971200 }, { target := 136, numerator := 206871658203579851038785536 }, { target := 137, numerator := 36283345281044387158292430848 }, { target := 142, numerator := 36283349631017224039926071296 }, { target := 150, numerator := 206867308230742969405145088 }, { target := 152, numerator := 65693006163896297953689600 }, { target := 153, numerator := 21161120436978964287927091200 }, { target := 155, numerator := 225057414698421787756446351360 }, { target := 163, numerator := 21161184216596599138701803520 }, { target := 170, numerator := 65693006163896297953689600 }, { target := 171, numerator := 309731777681426604430983168 }, { target := 172, numerator := 54324043862342895058890522624 }, { target := 177, numerator := 54324050375196474582969090048 }, { target := 185, numerator := 309725264827847080352415744 }, { target := 187, numerator := 864957914491301256390246400 }, { target := 188, numerator := 278621419086889696457706700800 }, { target := 190, numerator := 2963255960195886872126543626240 }, { target := 198, numerator := 278622258851855221992907079680 }, { target := 205, numerator := 864957914491301256390246400 }, { target := 267, numerator := 9595160399052868786585600 }, { target := 268, numerator := 1682900987061427975802060800 }, { target := 273, numerator := 1682901188822691282000281600 }, { target := 281, numerator := 9594958637789562588364800 }, { target := 403, numerator := 309731777681426604430983168 }, { target := 404, numerator := 54324043862342895058890522624 }, { target := 409, numerator := 54324050375196474582969090048 }, { target := 417, numerator := 309725264827847080352415744 }, { target := 438, numerator := 322781195824138505980739584 }, { target := 439, numerator := 56612789204746437105981325312 }, { target := 444, numerator := 56612795991995334726489473024 }, { target := 452, numerator := 322774408575240885472591872 }, { target := 534, numerator := 192287014397019490483175424 }, { target := 535, numerator := 33725335780711016635073298432 }, { target := 540, numerator := 33725339824006733291285643264 }, { target := 548, numerator := 192282971101302834270830592 }, { target := 750, numerator := 9595160399052868786585600 }, { target := 751, numerator := 1682900987061427975802060800 }, { target := 756, numerator := 1682901188822691282000281600 }, { target := 764, numerator := 9594958637789562588364800 }]

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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2564833654248353496538546176 }, { target := 112, numerator := 100377580922487064882204114944 }, { target := 115, numerator := 100377617737576549988041752576 }, { target := 122, numerator := 2564870469337838602376183808 }, { target := 222, numerator := 76641840524545680945971200 }, { target := 223, numerator := 24687973843142125002581606400 }, { target := 225, numerator := 262566983814825419049187409920 }, { target := 233, numerator := 24688048252696032328485437440 }, { target := 240, numerator := 76641840524545680945971200 }, { target := 283, numerator := 65693006163896297953689600 }, { target := 284, numerator := 21161120436978964287927091200 }, { target := 286, numerator := 225057414698421787756446351360 }, { target := 294, numerator := 21161184216596599138701803520 }, { target := 301, numerator := 65693006163896297953689600 }, { target := 318, numerator := 76641840524545680945971200 }, { target := 319, numerator := 24687973843142125002581606400 }, { target := 321, numerator := 262566983814825419049187409920 }, { target := 329, numerator := 24688048252696032328485437440 }, { target := 336, numerator := 76641840524545680945971200 }, { target := 419, numerator := 76641840524545680945971200 }, { target := 420, numerator := 24687973843142125002581606400 }, { target := 422, numerator := 262566983814825419049187409920 }, { target := 430, numerator := 24688048252696032328485437440 }, { target := 437, numerator := 76641840524545680945971200 }, { target := 454, numerator := 3177351731460450944360120320 }, { target := 455, numerator := 1023492858468549239392740311040 }, { target := 457, numerator := 10885276957580333801153455194112 }, { target := 465, numerator := 1023495943276055511675210563584 }, { target := 472, numerator := 3177351731460450944360120320 }, { target := 489, numerator := 78831607396675557544427520 }, { target := 490, numerator := 25393344524374757145512509440 }, { target := 492, numerator := 270068897638106145307735621632 }, { target := 500, numerator := 25393421059915918966442164224 }, { target := 507, numerator := 78831607396675557544427520 }, { target := 550, numerator := 864957914491301256390246400 }, { target := 551, numerator := 278621419086889696457706700800 }, { target := 553, numerator := 2963255960195886872126543626240 }, { target := 561, numerator := 278622258851855221992907079680 }, { target := 568, numerator := 864957914491301256390246400 }, { target := 585, numerator := 3177351731460450944360120320 }, { target := 586, numerator := 1023492858468549239392740311040 }, { target := 588, numerator := 10885276957580333801153455194112 }, { target := 596, numerator := 1023495943276055511675210563584 }, { target := 603, numerator := 3177351731460450944360120320 }, { target := 660, numerator := 67882773036026174552145920 }, { target := 661, numerator := 21866491118211596430857994240 }, { target := 663, numerator := 232559328521702514014994563072 }, { target := 671, numerator := 21866557023816485776658530304 }, { target := 678, numerator := 67882773036026174552145920 }, { target := 766, numerator := 76641840524545680945971200 }, { target := 767, numerator := 24687973843142125002581606400 }, { target := 769, numerator := 262566983814825419049187409920 }, { target := 777, numerator := 24688048252696032328485437440 }, { target := 784, numerator := 76641840524545680945971200 }, { target := 801, numerator := 78831607396675557544427520 }, { target := 802, numerator := 25393344524374757145512509440 }, { target := 804, numerator := 270068897638106145307735621632 }, { target := 812, numerator := 25393421059915918966442164224 }, { target := 819, numerator := 78831607396675557544427520 }, { target := 876, numerator := 76641840524545680945971200 }, { target := 877, numerator := 24687973843142125002581606400 }, { target := 879, numerator := 262566983814825419049187409920 }, { target := 887, numerator := 24688048252696032328485437440 }, { target := 894, numerator := 76641840524545680945971200 }]

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
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
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
    Slot3.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 37190087986601125699808919552 }, { target := 208, numerator := 1455474923376062440791959666688 }, { target := 211, numerator := 1455475457194859974826605412352 }, { target := 218, numerator := 37190621805398659734454665216 }, { target := 241, numerator := 65830730459041073077822685184 }, { target := 243, numerator := 2576357910343834665309905616896 }, { target := 246, numerator := 2576358855264464783026404982784 }, { target := 253, numerator := 65831675379671190794322051072 }, { target := 302, numerator := 2137361378540294580448788480 }, { target := 304, numerator := 83647984102072554068503429120 }, { target := 307, numerator := 83648014781313791656701460480 }, { target := 314, numerator := 2137392057781532168646819840 }, { target := 337, numerator := 41037338467973655944616738816 }, { target := 339, numerator := 1606041294759793038115265839104 }, { target := 342, numerator := 1606041883801224799808668041216 }, { target := 349, numerator := 41037927509405417638018940928 }, { target := 363, numerator := 2137361378540294580448788480 }, { target := 365, numerator := 83647984102072554068503429120 }, { target := 368, numerator := 83648014781313791656701460480 }, { target := 375, numerator := 2137392057781532168646819840 }, { target := 473, numerator := 65403258183333014161732927488 }, { target := 475, numerator := 2559628313523420154496204931072 }, { target := 478, numerator := 2559629252308202024695064690688 }, { target := 485, numerator := 65404196968114884360592687104 }, { target := 508, numerator := 68395564113289426574361231360 }, { target := 510, numerator := 2676735491266321730192109731840 }, { target := 513, numerator := 2676736473002041333014446735360 }, { target := 520, numerator := 68396545849009029396698234880 }, { target := 569, numerator := 41037338467973655944616738816 }, { target := 571, numerator := 1606041294759793038115265839104 }, { target := 574, numerator := 1606041883801224799808668041216 }, { target := 581, numerator := 41037927509405417638018940928 }, { target := 604, numerator := 1047734547760452403335996112896 }, { target := 606, numerator := 41004241806835966004380380954624 }, { target := 609, numerator := 41004256845800020670115055927296 }, { target := 616, numerator := 1047749586724507069070671085568 }, { target := 630, numerator := 67113147286165249826091958272 }, { target := 632, numerator := 2626546700805078197751007674368 }, { target := 635, numerator := 2626547664133253058020425859072 }, { target := 642, numerator := 67114110614340110095510142976 }, { target := 679, numerator := 37190087986601125699808919552 }, { target := 681, numerator := 1455474923376062440791959666688 }, { target := 684, numerator := 1455475457194859974826605412352 }, { target := 691, numerator := 37190621805398659734454665216 }, { target := 705, numerator := 65403258183333014161732927488 }, { target := 707, numerator := 2559628313523420154496204931072 }, { target := 710, numerator := 2559629252308202024695064690688 }, { target := 717, numerator := 65404196968114884360592687104 }, { target := 785, numerator := 2137361378540294580448788480 }, { target := 787, numerator := 83647984102072554068503429120 }, { target := 790, numerator := 83648014781313791656701460480 }, { target := 797, numerator := 2137392057781532168646819840 }, { target := 820, numerator := 67113147286165249826091958272 }, { target := 822, numerator := 2626546700805078197751007674368 }, { target := 825, numerator := 2626547664133253058020425859072 }, { target := 832, numerator := 67114110614340110095510142976 }, { target := 846, numerator := 2137361378540294580448788480 }, { target := 848, numerator := 83647984102072554068503429120 }, { target := 851, numerator := 83648014781313791656701460480 }, { target := 858, numerator := 2137392057781532168646819840 }, { target := 895, numerator := 65403258183333014161732927488 }, { target := 897, numerator := 2559628313523420154496204931072 }, { target := 900, numerator := 2559629252308202024695064690688 }, { target := 907, numerator := 65404196968114884360592687104 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 52905660251309722854804684800 }, { target := 260, numerator := 189634775516462879438641561600 }, { target := 262, numerator := 52921034546042768004743168000 }, { target := 353, numerator := 39397832102039155317407744000 }, { target := 356, numerator := 141217386022897888943669248000 }, { target := 358, numerator := 39409281044925465535447040000 }, { target := 379, numerator := 41649136793584249906973900800 }, { target := 382, numerator := 149286950938492054026164633600 }, { target := 384, numerator := 41661239961778349280329728000 }, { target := 389, numerator := 1798880976256368641342177280 }, { target := 391, numerator := 1798882262916767782583402496 }, { target := 524, numerator := 54031312597082270149587763200 }, { target := 527, numerator := 193669557974259961979889254400 }, { target := 529, numerator := 54047014004469209877184512000 }, { target := 620, numerator := 723794458331747910545519411200 }, { target := 623, numerator := 2594365120363524074022266470400 }, { target := 625, numerator := 724004791768202123979784192000 }, { target := 646, numerator := 1309133678133472503832720179200 }, { target := 649, numerator := 4692451998418006995471066726400 }, { target := 651, numerator := 1309514110149951897649283072000 }, { target := 656, numerator := 44101598127575489271614668800 }, { target := 658, numerator := 44101629671507855314947932160 }, { target := 695, numerator := 39397832102039155317407744000 }, { target := 698, numerator := 141217386022897888943669248000 }, { target := 700, numerator := 39409281044925465535447040000 }, { target := 721, numerator := 723794458331747910545519411200 }, { target := 724, numerator := 2594365120363524074022266470400 }, { target := 726, numerator := 724004791768202123979784192000 }, { target := 731, numerator := 32611971246970296014009794560 }, { target := 733, numerator := 32611994572878177219737812992 }, { target := 735, numerator := 42774789139356797201756979200 }, { target := 738, numerator := 153321733396289136567412326400 }, { target := 740, numerator := 42787219420204791152771072000 }, { target := 745, numerator := 36383818455249778649082101760 }, { target := 747, numerator := 36383844478993980634832044032 }, { target := 836, numerator := 42774789139356797201756979200 }, { target := 839, numerator := 153321733396289136567412326400 }, { target := 841, numerator := 42787219420204791152771072000 }, { target := 862, numerator := 41649136793584249906973900800 }, { target := 865, numerator := 149286950938492054026164633600 }, { target := 867, numerator := 41661239961778349280329728000 }, { target := 911, numerator := 41649136793584249906973900800 }, { target := 914, numerator := 149286950938492054026164633600 }, { target := 916, numerator := 41661239961778349280329728000 }, { target := 921, numerator := 68395564113289426574361231360 }, { target := 923, numerator := 2676735491266321730192109731840 }, { target := 926, numerator := 2676736473002041333014446735360 }, { target := 933, numerator := 68396545849009029396698234880 }, { target := 937, numerator := 1309133678133472503832720179200 }, { target := 940, numerator := 4692451998418006995471066726400 }, { target := 942, numerator := 1309514110149951897649283072000 }, { target := 951, numerator := 41649136793584249906973900800 }, { target := 954, numerator := 149286950938492054026164633600 }, { target := 956, numerator := 41661239961778349280329728000 }, { target := 966, numerator := 2564833654248353496538546176 }, { target := 968, numerator := 100377580922487064882204114944 }, { target := 971, numerator := 100377617737576549988041752576 }, { target := 978, numerator := 2564870469337838602376183808 }, { target := 982, numerator := 52905660251309722854804684800 }, { target := 985, numerator := 189634775516462879438641561600 }, { target := 987, numerator := 52921034546042768004743168000 }, { target := 996, numerator := 54031312597082270149587763200 }, { target := 999, numerator := 193669557974259961979889254400 }, { target := 1001, numerator := 54047014004469209877184512000 }]

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
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 839218831220488955393736704 }, { target := 6, numerator := 37931164430082189027499311104 }, { target := 11, numerator := 843697995829490813878927360 }, { target := 14, numerator := 3768412847271218239040913408 }, { target := 15, numerator := 747407552695159679980299878400 }, { target := 20, numerator := 747407552695159679980299878400 }, { target := 28, numerator := 3768412847271218239040913408 }, { target := 56, numerator := 1099920666314250749592207360 }, { target := 57, numerator := 180255813355726623204389683200 }, { target := 59, numerator := 1855803391491637019111797555200 }, { target := 67, numerator := 180255813355726623204389683200 }, { target := 74, numerator := 1099920666314250749592207360 }, { target := 110, numerator := 1095127983672358589463265280 }, { target := 112, numerator := 43783013598370720412587786240 }, { target := 115, numerator := 43783002898589247216476487680 }, { target := 122, numerator := 1095127983672358589463265280 }, { target := 126, numerator := 839218831220488955393736704 }, { target := 128, numerator := 37931164430082189027499311104 }, { target := 133, numerator := 843697995829490813878927360 }, { target := 136, numerator := 13727426081311465219700031488 }, { target := 137, numerator := 2722626832053755132544181862400 }, { target := 142, numerator := 2722626832053755132544181862400 }, { target := 150, numerator := 13727426081311465219700031488 }, { target := 152, numerator := 43974624161164465359688826880 }, { target := 153, numerator := 7206593973495185453199497625600 }, { target := 155, numerator := 74194675268100986970289314201600 }, { target := 163, numerator := 7206593973495185453199497625600 }, { target := 170, numerator := 43974624161164465359688826880 }, { target := 206, numerator := 179470384975091648811342233600 }, { target := 208, numerator := 7175192692564923207216057548800 }, { target := 211, numerator := 7175190939076811521472960921600 }, { target := 218, numerator := 179470384975091648811342233600 }, { target := 267, numerator := 3768415382167867450751713280 }, { target := 268, numerator := 747408055453476697820626944000 }, { target := 273, numerator := 747408055453476697820626944000 }, { target := 281, numerator := 3768415382167867450751713280 }, { target := 283, numerator := 43974613414556815037992796160 }, { target := 284, numerator := 7206592212333165182398444339200 }, { target := 286, numerator := 74194657136256086440863281971200 }, { target := 294, numerator := 7206592212333165182398444339200 }, { target := 301, numerator := 43974613414556815037992796160 }, { target := 302, numerator := 1847717102204091759769262489600 }, { target := 304, numerator := 73871386922706211427935112396800 }, { target := 307, numerator := 73871368869867171031534901657600 }, { target := 314, numerator := 1847717102204091759769262489600 }, { target := 660, numerator := 1099920666314250749592207360 }, { target := 661, numerator := 180255813355726623204389683200 }, { target := 663, numerator := 1855803391491637019111797555200 }, { target := 671, numerator := 180255813355726623204389683200 }, { target := 678, numerator := 1099920666314250749592207360 }, { target := 872, numerator := 1798880976256368641342177280 }, { target := 874, numerator := 1798882262916767782583402496 }, { target := 947, numerator := 36325790036660863531619450880 }, { target := 949, numerator := 36325816018899891351522902016 }, { target := 961, numerator := 36964102641138929823708610560 }, { target := 963, numerator := 36964129079934873467923464192 }, { target := 992, numerator := 1798880976256368641342177280 }, { target := 994, numerator := 1798882262916767782583402496 }, { target := 1006, numerator := 44101598127575489271614668800 }, { target := 1008, numerator := 44101629671507855314947932160 }, { target := 1011, numerator := 1798880976256368641342177280 }, { target := 1013, numerator := 1798882262916767782583402496 }]

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
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left7.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1798880976256368641342177280 }, { target := 5, numerator := 44101598127575489271614668800 }, { target := 6, numerator := 32611971246970296014009794560 }, { target := 7, numerator := 36383818455249778649082101760 }, { target := 8, numerator := 1798880976256368641342177280 }, { target := 9, numerator := 36325790036660863531619450880 }, { target := 10, numerator := 36964102641138929823708610560 }, { target := 11, numerator := 1798880976256368641342177280 }, { target := 12, numerator := 44101598127575489271614668800 }, { target := 13, numerator := 1798880976256368641342177280 }, { target := 14, numerator := 53719593485945257052570910720 }, { target := 15, numerator := 40003952595916680783829401600 }, { target := 16, numerator := 42289892744254776828619653120 }, { target := 17, numerator := 54862563560114305074966036480 }, { target := 18, numerator := 734929757690697878400065863680 }, { target := 19, numerator := 1329274196258602850045531258880 }, { target := 20, numerator := 40003952595916680783829401600 }, { target := 21, numerator := 734929757690697878400065863680 }, { target := 22, numerator := 43432862818423824851014778880 }, { target := 23, numerator := 43432862818423824851014778880 }, { target := 24, numerator := 42289892744254776828619653120 }, { target := 25, numerator := 42289892744254776828619653120 }, { target := 26, numerator := 1329274196258602850045531258880 }, { target := 27, numerator := 42289892744254776828619653120 }, { target := 28, numerator := 53719593485945257052570910720 }, { target := 29, numerator := 54862563560114305074966036480 }, { target := 126, numerator := 1798882262916767782583402496 }, { target := 127, numerator := 44101629671507855314947932160 }, { target := 128, numerator := 32611994572878177219737812992 }, { target := 129, numerator := 36383844478993980634832044032 }, { target := 130, numerator := 1798882262916767782583402496 }, { target := 131, numerator := 36325816018899891351522902016 }, { target := 132, numerator := 36964129079934873467923464192 }, { target := 133, numerator := 1798882262916767782583402496 }, { target := 134, numerator := 44101629671507855314947932160 }, { target := 135, numerator := 1798882262916767782583402496 }, { target := 257, numerator := 3874069282241439311163555840 }, { target := 260, numerator := 14112307186394964244551434240 }, { target := 262, numerator := 3874071888209957192361574400 }, { target := 353, numerator := 768362904639883783157317632000 }, { target := 356, numerator := 2798962163793580042802429952000 }, { target := 358, numerator := 768363421494228380937093120000 }, { target := 389, numerator := 839218831220488955393736704 }, { target := 391, numerator := 839218831220488955393736704 }, { target := 679, numerator := 179470384975091648811342233600 }, { target := 681, numerator := 7175192692564923207216057548800 }, { target := 684, numerator := 7175190939076811521472960921600 }, { target := 691, numerator := 179470384975091648811342233600 }, { target := 695, numerator := 768362904639883783157317632000 }, { target := 698, numerator := 2798962163793580042802429952000 }, { target := 700, numerator := 768363421494228380937093120000 }, { target := 731, numerator := 37931164430082189027499311104 }, { target := 733, numerator := 37931164430082189027499311104 }, { target := 966, numerator := 1095127983672358589463265280 }, { target := 968, numerator := 43783013598370720412587786240 }, { target := 971, numerator := 43783002898589247216476487680 }, { target := 978, numerator := 1095127983672358589463265280 }, { target := 982, numerator := 3874069282241439311163555840 }, { target := 985, numerator := 14112307186394964244551434240 }, { target := 987, numerator := 3874071888209957192361574400 }, { target := 992, numerator := 843697995829490813878927360 }, { target := 994, numerator := 843697995829490813878927360 }]

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
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2561942071774567303194083328 }, { target := 57, numerator := 37148160040731225896314208256 }, { target := 58, numerator := 65756513175547227448648138752 }, { target := 59, numerator := 2134951726478806085995069440 }, { target := 60, numerator := 40991073148393076851105333248 }, { target := 61, numerator := 2134951726478806085995069440 }, { target := 62, numerator := 65329522830251466231449124864 }, { target := 63, numerator := 68318455247321794751842222080 }, { target := 64, numerator := 40991073148393076851105333248 }, { target := 65, numerator := 1046553336319910743354783039488 }, { target := 66, numerator := 67037484211434511100245180416 }, { target := 67, numerator := 37148160040731225896314208256 }, { target := 68, numerator := 65329522830251466231449124864 }, { target := 69, numerator := 2134951726478806085995069440 }, { target := 70, numerator := 67037484211434511100245180416 }, { target := 71, numerator := 2134951726478806085995069440 }, { target := 72, numerator := 65329522830251466231449124864 }, { target := 73, numerator := 68318455247321794751842222080 }, { target := 74, numerator := 2561942071774567303194083328 }, { target := 136, numerator := 192552233601331539122312970240 }, { target := 137, numerator := 143389961192480933388956467200 }, { target := 138, numerator := 151583673260622701011182551040 }, { target := 139, numerator := 196649089635402422933426012160 }, { target := 140, numerator := 2634278429907578290545685954560 }, { target := 141, numerator := 4764643567624437872324467752960 }, { target := 142, numerator := 143389961192480933388956467200 }, { target := 143, numerator := 2634278429907578290545685954560 }, { target := 144, numerator := 155680529294693584822295592960 }, { target := 145, numerator := 155680529294693584822295592960 }, { target := 146, numerator := 151583673260622701011182551040 }, { target := 147, numerator := 151583673260622701011182551040 }, { target := 148, numerator := 4764643567624437872324467752960 }, { target := 149, numerator := 151583673260622701011182551040 }, { target := 150, numerator := 192552233601331539122312970240 }, { target := 151, numerator := 196649089635402422933426012160 }, { target := 267, numerator := 53735204308289579820200755200 }, { target := 268, numerator := 40015577676385857312915456000 }, { target := 269, numerator := 42302182115036477730796339200 }, { target := 270, numerator := 54878506527614890029141196800 }, { target := 271, numerator := 735143327026174464348703948800 }, { target := 272, numerator := 1329660481075335772997733580800 }, { target := 273, numerator := 40015577676385857312915456000 }, { target := 274, numerator := 735143327026174464348703948800 }, { target := 275, numerator := 43445484334361787939736780800 }, { target := 276, numerator := 43445484334361787939736780800 }, { target := 277, numerator := 42302182115036477730796339200 }, { target := 278, numerator := 42302182115036477730796339200 }, { target := 279, numerator := 1329660481075335772997733580800 }, { target := 280, numerator := 42302182115036477730796339200 }, { target := 281, numerator := 53735204308289579820200755200 }, { target := 282, numerator := 54878506527614890029141196800 }]

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
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 100264415667783020840623276032 }, { target := 153, numerator := 1453834027182853802189037502464 }, { target := 154, numerator := 2573453335473097534909330751488 }, { target := 155, numerator := 83553679723152517367186063360 }, { target := 156, numerator := 1604230650684528333449972416512 }, { target := 157, numerator := 83553679723152517367186063360 }, { target := 158, numerator := 2556742599528467031435893538816 }, { target := 159, numerator := 2673717751140880555749954027520 }, { target := 160, numerator := 1604230650684528333449972416512 }, { target := 161, numerator := 40958013800289364013394608259072 }, { target := 162, numerator := 2623585543306989045329642389504 }, { target := 163, numerator := 1453834027182853802189037502464 }, { target := 164, numerator := 2556742599528467031435893538816 }, { target := 165, numerator := 83553679723152517367186063360 }, { target := 166, numerator := 2623585543306989045329642389504 }, { target := 167, numerator := 83553679723152517367186063360 }, { target := 168, numerator := 2556742599528467031435893538816 }, { target := 169, numerator := 2673717751140880555749954027520 }, { target := 170, numerator := 100264415667783020840623276032 }, { target := 283, numerator := 100264452441367331780614422528 }, { target := 284, numerator := 1453834560399826310818909126656 }, { target := 285, numerator := 2573454279328428182369103511552 }, { target := 286, numerator := 83553710367806109817178685440 }, { target := 287, numerator := 1604231239061877308489830760448 }, { target := 288, numerator := 83553710367806109817178685440 }, { target := 289, numerator := 2556743537254866960405667774464 }, { target := 290, numerator := 2673718731769795514149717934080 }, { target := 291, numerator := 1604231239061877308489830760448 }, { target := 292, numerator := 40958028822298555032380991602688 }, { target := 293, numerator := 2623586505549111848259410722816 }, { target := 294, numerator := 1453834560399826310818909126656 }, { target := 295, numerator := 2556743537254866960405667774464 }, { target := 296, numerator := 83553710367806109817178685440 }, { target := 297, numerator := 2623586505549111848259410722816 }, { target := 298, numerator := 83553710367806109817178685440 }, { target := 299, numerator := 2556743537254866960405667774464 }, { target := 300, numerator := 2673718731769795514149717934080 }, { target := 301, numerator := 100264452441367331780614422528 }, { target := 660, numerator := 2561978845358878243185229824 }, { target := 661, numerator := 37148693257703734526185832448 }, { target := 662, numerator := 65757457030877874908420898816 }, { target := 663, numerator := 2134982371132398535987691520 }, { target := 664, numerator := 40991661525742051890963677184 }, { target := 665, numerator := 2134982371132398535987691520 }, { target := 666, numerator := 65330460556651395201223360512 }, { target := 667, numerator := 68319435876236753151606128640 }, { target := 668, numerator := 40991661525742051890963677184 }, { target := 669, numerator := 1046568358329101762341166383104 }, { target := 670, numerator := 67038446453557314030013513728 }, { target := 671, numerator := 37148693257703734526185832448 }, { target := 672, numerator := 65330460556651395201223360512 }, { target := 673, numerator := 2134982371132398535987691520 }, { target := 674, numerator := 67038446453557314030013513728 }, { target := 675, numerator := 2134982371132398535987691520 }, { target := 676, numerator := 65330460556651395201223360512 }, { target := 677, numerator := 68319435876236753151606128640 }, { target := 678, numerator := 2561978845358878243185229824 }]

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
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 66557512824910696090173440 }, { target := 111, numerator := 75145578995866914940518400 }, { target := 112, numerator := 64410496282171641377587200 }, { target := 113, numerator := 848071534381926611471564800 }, { target := 114, numerator := 75145578995866914940518400 }, { target := 115, numerator := 64410496282171641377587200 }, { target := 116, numerator := 75145578995866914940518400 }, { target := 117, numerator := 75145578995866914940518400 }, { target := 118, numerator := 3115321003514368387962634240 }, { target := 119, numerator := 77292595538605969653104640 }, { target := 120, numerator := 848071534381926611471564800 }, { target := 121, numerator := 3115321003514368387962634240 }, { target := 122, numerator := 66557512824910696090173440 }, { target := 123, numerator := 75145578995866914940518400 }, { target := 124, numerator := 77292595538605969653104640 }, { target := 125, numerator := 75145578995866914940518400 }, { target := 206, numerator := 21439596497682519710949703680 }, { target := 207, numerator := 24205996045770586770427084800 }, { target := 208, numerator := 20747996610660502946080358400 }, { target := 209, numerator := 273181955373696622123391385600 }, { target := 210, numerator := 24205996045770586770427084800 }, { target := 211, numerator := 20747996610660502946080358400 }, { target := 212, numerator := 24205996045770586770427084800 }, { target := 213, numerator := 24205996045770586770427084800 }, { target := 214, numerator := 1003511436068946325825420001280 }, { target := 215, numerator := 24897595932792603535296430080 }, { target := 216, numerator := 273181955373696622123391385600 }, { target := 217, numerator := 1003511436068946325825420001280 }, { target := 218, numerator := 21439596497682519710949703680 }, { target := 219, numerator := 24205996045770586770427084800 }, { target := 220, numerator := 24897595932792603535296430080 }, { target := 221, numerator := 24205996045770586770427084800 }, { target := 302, numerator := 228019124711083592917087944704 }, { target := 303, numerator := 257440947254449217809615421440 }, { target := 304, numerator := 220663669075242186693956075520 }, { target := 305, numerator := 2905404976157355458137088327680 }, { target := 306, numerator := 257440947254449217809615421440 }, { target := 307, numerator := 220663669075242186693956075520 }, { target := 308, numerator := 257440947254449217809615421440 }, { target := 309, numerator := 257440947254449217809615421440 }, { target := 310, numerator := 10672766127605880429764342185984 }, { target := 311, numerator := 264796402890290624032747290624 }, { target := 312, numerator := 2905404976157355458137088327680 }, { target := 313, numerator := 10672766127605880429764342185984 }, { target := 314, numerator := 228019124711083592917087944704 }, { target := 315, numerator := 257440947254449217809615421440 }, { target := 316, numerator := 264796402890290624032747290624 }, { target := 317, numerator := 257440947254449217809615421440 }, { target := 679, numerator := 21439661116627009915509014528 }, { target := 680, numerator := 24206069002643398291703726080 }, { target := 681, numerator := 20748059145122912821460336640 }, { target := 682, numerator := 273182778744118352149227765760 }, { target := 683, numerator := 24206069002643398291703726080 }, { target := 684, numerator := 20748059145122912821460336640 }, { target := 685, numerator := 24206069002643398291703726080 }, { target := 686, numerator := 24206069002643398291703726080 }, { target := 687, numerator := 1003514460652444883464631615488 }, { target := 688, numerator := 24897670974147495385752403968 }, { target := 689, numerator := 273182778744118352149227765760 }, { target := 690, numerator := 1003514460652444883464631615488 }, { target := 691, numerator := 21439661116627009915509014528 }, { target := 692, numerator := 24206069002643398291703726080 }, { target := 693, numerator := 24897670974147495385752403968 }, { target := 694, numerator := 24206069002643398291703726080 }]

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
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left6.expected,
    Slot20.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 9211353983090754035122176 }, { target := 258, numerator := 192287014397019490483175424 }, { target := 259, numerator := 9978966815014983538049024 }, { target := 260, numerator := 206871658203579851038785536 }, { target := 261, numerator := 309731777681426604430983168 }, { target := 262, numerator := 9595160399052868786585600 }, { target := 263, numerator := 309731777681426604430983168 }, { target := 264, numerator := 322781195824138505980739584 }, { target := 265, numerator := 192287014397019490483175424 }, { target := 266, numerator := 9595160399052868786585600 }, { target := 353, numerator := 1615584947578970856769978368 }, { target := 354, numerator := 33725335780711016635073298432 }, { target := 355, numerator := 1750217026543885094834143232 }, { target := 356, numerator := 36283345281044387158292430848 }, { target := 357, numerator := 54324043862342895058890522624 }, { target := 358, numerator := 1682900987061427975802060800 }, { target := 359, numerator := 54324043862342895058890522624 }, { target := 360, numerator := 56612789204746437105981325312 }, { target := 361, numerator := 33725335780711016635073298432 }, { target := 362, numerator := 1682900987061427975802060800 }, { target := 695, numerator := 1615585141269783630720270336 }, { target := 696, numerator := 33725339824006733291285643264 }, { target := 697, numerator := 1750217236375598933280292864 }, { target := 698, numerator := 36283349631017224039926071296 }, { target := 699, numerator := 54324050375196474582969090048 }, { target := 700, numerator := 1682901188822691282000281600 }, { target := 701, numerator := 54324050375196474582969090048 }, { target := 702, numerator := 56612795991995334726489473024 }, { target := 703, numerator := 33725339824006733291285643264 }, { target := 704, numerator := 1682901188822691282000281600 }, { target := 966, numerator := 66557512824910696090173440 }, { target := 967, numerator := 75145578995866914940518400 }, { target := 968, numerator := 64410496282171641377587200 }, { target := 969, numerator := 848071534381926611471564800 }, { target := 970, numerator := 75145578995866914940518400 }, { target := 971, numerator := 64410496282171641377587200 }, { target := 972, numerator := 75145578995866914940518400 }, { target := 973, numerator := 75145578995866914940518400 }, { target := 974, numerator := 3115321003514368387962634240 }, { target := 975, numerator := 77292595538605969653104640 }, { target := 976, numerator := 848071534381926611471564800 }, { target := 977, numerator := 3115321003514368387962634240 }, { target := 978, numerator := 66557512824910696090173440 }, { target := 979, numerator := 75145578995866914940518400 }, { target := 980, numerator := 77292595538605969653104640 }, { target := 981, numerator := 75145578995866914940518400 }, { target := 982, numerator := 9211160292277980084830208 }, { target := 983, numerator := 192282971101302834270830592 }, { target := 984, numerator := 9978756983301145091899392 }, { target := 985, numerator := 206867308230742969405145088 }, { target := 986, numerator := 309725264827847080352415744 }, { target := 987, numerator := 9594958637789562588364800 }, { target := 988, numerator := 309725264827847080352415744 }, { target := 989, numerator := 322774408575240885472591872 }, { target := 990, numerator := 192282971101302834270830592 }, { target := 991, numerator := 9594958637789562588364800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2
