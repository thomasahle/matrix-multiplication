import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 191765858136370552837767168 }, { target := 201, numerator := 218400005099755351843012608 }, { target := 202, numerator := 170458540565662713633570816 }, { target := 203, numerator := 2285209809458415754650058752 }, { target := 204, numerator := 202419516921724472439865344 }, { target := 205, numerator := 170458540565662713633570816 }, { target := 206, numerator := 202419516921724472439865344 }, { target := 207, numerator := 197092687529047512638816256 }, { target := 208, numerator := 7446907490962389801866625024 }, { target := 209, numerator := 197092687529047512638816256 }, { target := 210, numerator := 2285209809458415754650058752 }, { target := 211, numerator := 7446907490962389801866625024 }, { target := 212, numerator := 191765858136370552837767168 }, { target := 213, numerator := 197092687529047512638816256 }, { target := 214, numerator := 197092687529047512638816256 }, { target := 215, numerator := 218400005099755351843012608 }, { target := 296, numerator := 142804362441978071262167040 }, { target := 297, numerator := 162638301670030581159690240 }, { target := 298, numerator := 126937211059536063344148480 }, { target := 299, numerator := 1701751985766905349207490560 }, { target := 300, numerator := 150737938133199075221176320 }, { target := 301, numerator := 126937211059536063344148480 }, { target := 302, numerator := 150737938133199075221176320 }, { target := 303, numerator := 146771150287588573241671680 }, { target := 304, numerator := 5545569408163481767347486720 }, { target := 305, numerator := 146771150287588573241671680 }, { target := 306, numerator := 1701751985766905349207490560 }, { target := 307, numerator := 5545569408163481767347486720 }, { target := 308, numerator := 142804362441978071262167040 }, { target := 309, numerator := 146771150287588573241671680 }, { target := 310, numerator := 146771150287588573241671680 }, { target := 311, numerator := 162638301670030581159690240 }, { target := 331, numerator := 150964611724376818191433728 }, { target := 332, numerator := 171931918908318042940243968 }, { target := 333, numerator := 134190765977223838392385536 }, { target := 334, numerator := 1798994956382157083447918592 }, { target := 335, numerator := 159351534597953308090957824 }, { target := 336, numerator := 134190765977223838392385536 }, { target := 337, numerator := 159351534597953308090957824 }, { target := 338, numerator := 155158073161165063141195776 }, { target := 339, numerator := 5862459088629966439767343104 }, { target := 340, numerator := 155158073161165063141195776 }, { target := 341, numerator := 1798994956382157083447918592 }, { target := 342, numerator := 5862459088629966439767343104 }, { target := 343, numerator := 150964611724376818191433728 }, { target := 344, numerator := 155158073161165063141195776 }, { target := 345, numerator := 155158073161165063141195776 }, { target := 346, numerator := 171931918908318042940243968 }, { target := 467, numerator := 195845982777569926302400512 }, { target := 468, numerator := 223046813718899082733289472 }, { target := 469, numerator := 174085318024506601157689344 }, { target := 470, numerator := 2333831294766041621770272768 }, { target := 471, numerator := 206726315154101588874756096 }, { target := 472, numerator := 174085318024506601157689344 }, { target := 473, numerator := 206726315154101588874756096 }, { target := 474, numerator := 201286148965835757588578304 }, { target := 475, numerator := 7605352331195632138076553216 }, { target := 476, numerator := 201286148965835757588578304 }, { target := 477, numerator := 2333831294766041621770272768 }, { target := 478, numerator := 7605352331195632138076553216 }, { target := 479, numerator := 195845982777569926302400512 }, { target := 480, numerator := 201286148965835757588578304 }, { target := 481, numerator := 201286148965835757588578304 }, { target := 482, numerator := 223046813718899082733289472 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 563, numerator := 2623520144291197137759240192 }, { target := 564, numerator := 2987897942109418962448023552 }, { target := 565, numerator := 2332017906036619678008213504 }, { target := 566, numerator := 31263615052803432558297612288 }, { target := 567, numerator := 2769271263418485867634753536 }, { target := 568, numerator := 2332017906036619678008213504 }, { target := 569, numerator := 2769271263418485867634753536 }, { target := 570, numerator := 2696395703854841502696996864 }, { target := 571, numerator := 101880032269974822182983827456 }, { target := 572, numerator := 2696395703854841502696996864 }, { target := 573, numerator := 31263615052803432558297612288 }, { target := 574, numerator := 101880032269974822182983827456 }, { target := 575, numerator := 2623520144291197137759240192 }, { target := 576, numerator := 2696395703854841502696996864 }, { target := 577, numerator := 2696395703854841502696996864 }, { target := 578, numerator := 2987897942109418962448023552 }, { target := 598, numerator := 4745184957714871339368579072 }, { target := 599, numerator := 5404238424064159025391992832 }, { target := 600, numerator := 4217942184635441190549848064 }, { target := 601, numerator := 56546787412768883460808900608 }, { target := 602, numerator := 5008806344254586413777944576 }, { target := 603, numerator := 4217942184635441190549848064 }, { target := 604, numerator := 5008806344254586413777944576 }, { target := 605, numerator := 4876995650984728876573261824 }, { target := 606, numerator := 184271349191260837012146487296 }, { target := 607, numerator := 4876995650984728876573261824 }, { target := 608, numerator := 56546787412768883460808900608 }, { target := 609, numerator := 184271349191260837012146487296 }, { target := 610, numerator := 4745184957714871339368579072 }, { target := 611, numerator := 4876995650984728876573261824 }, { target := 612, numerator := 4876995650984728876573261824 }, { target := 613, numerator := 5404238424064159025391992832 }, { target := 659, numerator := 142804362441978071262167040 }, { target := 660, numerator := 162638301670030581159690240 }, { target := 661, numerator := 126937211059536063344148480 }, { target := 662, numerator := 1701751985766905349207490560 }, { target := 663, numerator := 150737938133199075221176320 }, { target := 664, numerator := 126937211059536063344148480 }, { target := 665, numerator := 150737938133199075221176320 }, { target := 666, numerator := 146771150287588573241671680 }, { target := 667, numerator := 5545569408163481767347486720 }, { target := 668, numerator := 146771150287588573241671680 }, { target := 669, numerator := 1701751985766905349207490560 }, { target := 670, numerator := 5545569408163481767347486720 }, { target := 671, numerator := 142804362441978071262167040 }, { target := 672, numerator := 146771150287588573241671680 }, { target := 673, numerator := 146771150287588573241671680 }, { target := 674, numerator := 162638301670030581159690240 }, { target := 694, numerator := 2623520144291197137759240192 }, { target := 695, numerator := 2987897942109418962448023552 }, { target := 696, numerator := 2332017906036619678008213504 }, { target := 697, numerator := 31263615052803432558297612288 }, { target := 698, numerator := 2769271263418485867634753536 }, { target := 699, numerator := 2332017906036619678008213504 }, { target := 700, numerator := 2769271263418485867634753536 }, { target := 701, numerator := 2696395703854841502696996864 }, { target := 702, numerator := 101880032269974822182983827456 }, { target := 703, numerator := 2696395703854841502696996864 }, { target := 704, numerator := 31263615052803432558297612288 }, { target := 705, numerator := 101880032269974822182983827456 }, { target := 706, numerator := 2623520144291197137759240192 }, { target := 707, numerator := 2696395703854841502696996864 }, { target := 708, numerator := 2696395703854841502696996864 }, { target := 709, numerator := 2987897942109418962448023552 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 720, numerator := 155044736365576191656067072 }, { target := 721, numerator := 176578727527461773830520832 }, { target := 722, numerator := 137817543436067725916504064 }, { target := 723, numerator := 1847616441689782950568132608 }, { target := 724, numerator := 163658332830330424525848576 }, { target := 725, numerator := 137817543436067725916504064 }, { target := 726, numerator := 163658332830330424525848576 }, { target := 727, numerator := 159351534597953308090957824 }, { target := 728, numerator := 6020903928863208775977271296 }, { target := 729, numerator := 159351534597953308090957824 }, { target := 730, numerator := 1847616441689782950568132608 }, { target := 731, numerator := 6020903928863208775977271296 }, { target := 732, numerator := 155044736365576191656067072 }, { target := 733, numerator := 159351534597953308090957824 }, { target := 734, numerator := 159351534597953308090957824 }, { target := 735, numerator := 176578727527461773830520832 }, { target := 830, numerator := 155044736365576191656067072 }, { target := 831, numerator := 176578727527461773830520832 }, { target := 832, numerator := 137817543436067725916504064 }, { target := 833, numerator := 1847616441689782950568132608 }, { target := 834, numerator := 163658332830330424525848576 }, { target := 835, numerator := 137817543436067725916504064 }, { target := 836, numerator := 163658332830330424525848576 }, { target := 837, numerator := 159351534597953308090957824 }, { target := 838, numerator := 6020903928863208775977271296 }, { target := 839, numerator := 159351534597953308090957824 }, { target := 840, numerator := 1847616441689782950568132608 }, { target := 841, numerator := 6020903928863208775977271296 }, { target := 842, numerator := 155044736365576191656067072 }, { target := 843, numerator := 159351534597953308090957824 }, { target := 844, numerator := 159351534597953308090957824 }, { target := 845, numerator := 176578727527461773830520832 }, { target := 865, numerator := 150964611724376818191433728 }, { target := 866, numerator := 171931918908318042940243968 }, { target := 867, numerator := 134190765977223838392385536 }, { target := 868, numerator := 1798994956382157083447918592 }, { target := 869, numerator := 159351534597953308090957824 }, { target := 870, numerator := 134190765977223838392385536 }, { target := 871, numerator := 159351534597953308090957824 }, { target := 872, numerator := 155158073161165063141195776 }, { target := 873, numerator := 5862459088629966439767343104 }, { target := 874, numerator := 155158073161165063141195776 }, { target := 875, numerator := 1798994956382157083447918592 }, { target := 876, numerator := 5862459088629966439767343104 }, { target := 877, numerator := 150964611724376818191433728 }, { target := 878, numerator := 155158073161165063141195776 }, { target := 879, numerator := 155158073161165063141195776 }, { target := 880, numerator := 171931918908318042940243968 }, { target := 926, numerator := 150964611724376818191433728 }, { target := 927, numerator := 171931918908318042940243968 }, { target := 928, numerator := 134190765977223838392385536 }, { target := 929, numerator := 1798994956382157083447918592 }, { target := 930, numerator := 159351534597953308090957824 }, { target := 931, numerator := 134190765977223838392385536 }, { target := 932, numerator := 159351534597953308090957824 }, { target := 933, numerator := 155158073161165063141195776 }, { target := 934, numerator := 5862459088629966439767343104 }, { target := 935, numerator := 155158073161165063141195776 }, { target := 936, numerator := 1798994956382157083447918592 }, { target := 937, numerator := 5862459088629966439767343104 }, { target := 938, numerator := 150964611724376818191433728 }, { target := 939, numerator := 155158073161165063141195776 }, { target := 940, numerator := 155158073161165063141195776 }, { target := 941, numerator := 171931918908318042940243968 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 961, numerator := 4745184957714871339368579072 }, { target := 962, numerator := 5404238424064159025391992832 }, { target := 963, numerator := 4217942184635441190549848064 }, { target := 964, numerator := 56546787412768883460808900608 }, { target := 965, numerator := 5008806344254586413777944576 }, { target := 966, numerator := 4217942184635441190549848064 }, { target := 967, numerator := 5008806344254586413777944576 }, { target := 968, numerator := 4876995650984728876573261824 }, { target := 969, numerator := 184271349191260837012146487296 }, { target := 970, numerator := 4876995650984728876573261824 }, { target := 971, numerator := 56546787412768883460808900608 }, { target := 972, numerator := 184271349191260837012146487296 }, { target := 973, numerator := 4745184957714871339368579072 }, { target := 974, numerator := 4876995650984728876573261824 }, { target := 975, numerator := 4876995650984728876573261824 }, { target := 976, numerator := 5404238424064159025391992832 }, { target := 987, numerator := 150964611724376818191433728 }, { target := 988, numerator := 171931918908318042940243968 }, { target := 989, numerator := 134190765977223838392385536 }, { target := 990, numerator := 1798994956382157083447918592 }, { target := 991, numerator := 159351534597953308090957824 }, { target := 992, numerator := 134190765977223838392385536 }, { target := 993, numerator := 159351534597953308090957824 }, { target := 994, numerator := 155158073161165063141195776 }, { target := 995, numerator := 5862459088629966439767343104 }, { target := 996, numerator := 155158073161165063141195776 }, { target := 997, numerator := 1798994956382157083447918592 }, { target := 998, numerator := 5862459088629966439767343104 }, { target := 999, numerator := 150964611724376818191433728 }, { target := 1000, numerator := 155158073161165063141195776 }, { target := 1001, numerator := 155158073161165063141195776 }, { target := 1002, numerator := 171931918908318042940243968 }, { target := 1036, numerator := 191765858136370552837767168 }, { target := 1037, numerator := 218400005099755351843012608 }, { target := 1038, numerator := 170458540565662713633570816 }, { target := 1039, numerator := 2285209809458415754650058752 }, { target := 1040, numerator := 202419516921724472439865344 }, { target := 1041, numerator := 170458540565662713633570816 }, { target := 1042, numerator := 202419516921724472439865344 }, { target := 1043, numerator := 197092687529047512638816256 }, { target := 1044, numerator := 7446907490962389801866625024 }, { target := 1045, numerator := 197092687529047512638816256 }, { target := 1046, numerator := 2285209809458415754650058752 }, { target := 1047, numerator := 7446907490962389801866625024 }, { target := 1048, numerator := 191765858136370552837767168 }, { target := 1049, numerator := 197092687529047512638816256 }, { target := 1050, numerator := 197092687529047512638816256 }, { target := 1051, numerator := 218400005099755351843012608 }, { target := 1062, numerator := 195845982777569926302400512 }, { target := 1063, numerator := 223046813718899082733289472 }, { target := 1064, numerator := 174085318024506601157689344 }, { target := 1065, numerator := 2333831294766041621770272768 }, { target := 1066, numerator := 206726315154101588874756096 }, { target := 1067, numerator := 174085318024506601157689344 }, { target := 1068, numerator := 206726315154101588874756096 }, { target := 1069, numerator := 201286148965835757588578304 }, { target := 1070, numerator := 7605352331195632138076553216 }, { target := 1071, numerator := 201286148965835757588578304 }, { target := 1072, numerator := 2333831294766041621770272768 }, { target := 1073, numerator := 7605352331195632138076553216 }, { target := 1074, numerator := 195845982777569926302400512 }, { target := 1075, numerator := 201286148965835757588578304 }, { target := 1076, numerator := 201286148965835757588578304 }, { target := 1077, numerator := 223046813718899082733289472 }]

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
    Slot2.Left3.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 45686765122823303989297152 }, { target := 72, numerator := 685301476842349559839457280 }, { target := 73, numerator := 1203084814901013671718158336 }, { target := 74, numerator := 45686765122823303989297152 }, { target := 75, numerator := 761446085380388399821619200 }, { target := 76, numerator := 45686765122823303989297152 }, { target := 77, numerator := 1203084814901013671718158336 }, { target := 78, numerator := 1195470354047209787719942144 }, { target := 79, numerator := 761446085380388399821619200 }, { target := 80, numerator := 18449838648766810927677833216 }, { target := 81, numerator := 1180241432339602019723509760 }, { target := 82, numerator := 685301476842349559839457280 }, { target := 83, numerator := 1203084814901013671718158336 }, { target := 84, numerator := 45686765122823303989297152 }, { target := 85, numerator := 1180241432339602019723509760 }, { target := 86, numerator := 45686765122823303989297152 }, { target := 87, numerator := 1203084814901013671718158336 }, { target := 88, numerator := 1203084814901013671718158336 }, { target := 89, numerator := 45686765122823303989297152 }, { target := 347, numerator := 742570030231851405810860032 }, { target := 350, numerator := 2712250635422256182643916800 }, { target := 352, numerator := 742569780047884906125066240 }, { target := 614, numerator := 18204942676651840916653342720 }, { target := 617, numerator := 66493886545835958026108928000 }, { target := 619, numerator := 18204936543109436408227430400 }, { target := 710, numerator := 13462076031945177098893656064 }, { target := 713, numerator := 49170479261526063698254233600 }, { target := 715, numerator := 13462071496351977975557652480 }, { target := 736, numerator := 15019077708237768756239007744 }, { target := 739, numerator := 54857456400314665371539865600 }, { target := 741, numerator := 15019072648065285036787630080 }, { target := 746, numerator := 9942204755307403596944900096 }, { target := 748, numerator := 9942207125714017068622282752 }, { target := 881, numerator := 742570030231851405810860032 }, { target := 884, numerator := 2712250635422256182643916800 }, { target := 886, numerator := 742569780047884906125066240 }, { target := 977, numerator := 14995123836294805807664463872 }, { target := 980, numerator := 54769964444333302268873932800 }, { target := 982, numerator := 14995118784192772620461015040 }, { target := 1003, numerator := 15258616427667398241984446464 }, { target := 1006, numerator := 55732375960128296398199193600 }, { target := 1008, numerator := 15258611286790409200053780480 }, { target := 1013, numerator := 9913190539095417010572492800 }, { target := 1015, numerator := 9913192902584501454608793600 }, { target := 1052, numerator := 742570030231851405810860032 }, { target := 1055, numerator := 2712250635422256182643916800 }, { target := 1057, numerator := 742569780047884906125066240 }, { target := 1078, numerator := 18204942676651840916653342720 }, { target := 1081, numerator := 66493886545835958026108928000 }, { target := 1083, numerator := 18204936543109436408227430400 }, { target := 1088, numerator := 9845490701267448309036875776 }, { target := 1090, numerator := 9845493048615631688577318912 }, { target := 1092, numerator := 742570030231851405810860032 }, { target := 1095, numerator := 2712250635422256182643916800 }, { target := 1097, numerator := 742569780047884906125066240 }, { target := 1102, numerator := 9913190539095417010572492800 }, { target := 1104, numerator := 9913192902584501454608793600 }]

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
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 7487180902239458411403018240 }, { target := 147, numerator := 112307713533591876171045273600 }, { target := 148, numerator := 197162430425639071500279480320 }, { target := 149, numerator := 7487180902239458411403018240 }, { target := 150, numerator := 124786348370657640190050304000 }, { target := 151, numerator := 7487180902239458411403018240 }, { target := 152, numerator := 197162430425639071500279480320 }, { target := 153, numerator := 195914566941932495098378977280 }, { target := 154, numerator := 124786348370657640190050304000 }, { target := 155, numerator := 3023573221021034621804918865920 }, { target := 156, numerator := 193418839974519342294577971200 }, { target := 157, numerator := 112307713533591876171045273600 }, { target := 158, numerator := 197162430425639071500279480320 }, { target := 159, numerator := 7487180902239458411403018240 }, { target := 160, numerator := 193418839974519342294577971200 }, { target := 161, numerator := 7487180902239458411403018240 }, { target := 162, numerator := 197162430425639071500279480320 }, { target := 163, numerator := 197162430425639071500279480320 }, { target := 164, numerator := 7487180902239458411403018240 }, { target := 242, numerator := 77083426339580930782018928640 }, { target := 243, numerator := 1156251395093713961730283929600 }, { target := 244, numerator := 2029863560275631177259831787520 }, { target := 245, numerator := 77083426339580930782018928640 }, { target := 246, numerator := 1284723772326348846366982144000 }, { target := 247, numerator := 77083426339580930782018928640 }, { target := 248, numerator := 2029863560275631177259831787520 }, { target := 249, numerator := 2017016322552367688796161966080 }, { target := 250, numerator := 1284723772326348846366982144000 }, { target := 251, numerator := 31128857003467432547471977349120 }, { target := 252, numerator := 1991321847105840711868822323200 }, { target := 253, numerator := 1156251395093713961730283929600 }, { target := 254, numerator := 2029863560275631177259831787520 }, { target := 255, numerator := 77083426339580930782018928640 }, { target := 256, numerator := 1991321847105840711868822323200 }, { target := 257, numerator := 77083426339580930782018928640 }, { target := 258, numerator := 2029863560275631177259831787520 }, { target := 259, numerator := 2029863560275631177259831787520 }, { target := 260, numerator := 77083426339580930782018928640 }, { target := 640, numerator := 7487180902239458411403018240 }, { target := 641, numerator := 112307713533591876171045273600 }, { target := 642, numerator := 197162430425639071500279480320 }, { target := 643, numerator := 7487180902239458411403018240 }, { target := 644, numerator := 124786348370657640190050304000 }, { target := 645, numerator := 7487180902239458411403018240 }, { target := 646, numerator := 197162430425639071500279480320 }, { target := 647, numerator := 195914566941932495098378977280 }, { target := 648, numerator := 124786348370657640190050304000 }, { target := 649, numerator := 3023573221021034621804918865920 }, { target := 650, numerator := 193418839974519342294577971200 }, { target := 651, numerator := 112307713533591876171045273600 }, { target := 652, numerator := 197162430425639071500279480320 }, { target := 653, numerator := 7487180902239458411403018240 }, { target := 654, numerator := 193418839974519342294577971200 }, { target := 655, numerator := 7487180902239458411403018240 }, { target := 656, numerator := 197162430425639071500279480320 }, { target := 657, numerator := 197162430425639071500279480320 }, { target := 658, numerator := 7487180902239458411403018240 }]

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
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 1356159070238587744677789696 }, { target := 202, numerator := 52897505592020156489794584576 }, { target := 205, numerator := 52897486189400009719783882752 }, { target := 212, numerator := 1356165537778636668014690304 }, { target := 296, numerator := 268973589899083444042648780800 }, { target := 298, numerator := 10491418217841789716654771404800 }, { target := 301, numerator := 10491414369626260393185352089600 }, { target := 308, numerator := 268974872637593218532455219200 }, { target := 347, numerator := 15893811587645760473548193792 }, { target := 350, numerator := 57169567631818234010770866176 }, { target := 352, numerator := 15893816889907834787417030656 }, { target := 659, numerator := 268973589899083444042648780800 }, { target := 661, numerator := 10491418217841789716654771404800 }, { target := 664, numerator := 10491414369626260393185352089600 }, { target := 671, numerator := 268974872637593218532455219200 }, { target := 710, numerator := 718371369092102797769930964992 }, { target := 713, numerator := 2583960451751906773545072459776 }, { target := 715, numerator := 718371608744702465599923552256 }, { target := 746, numerator := 49517607474373314583021486080 }, { target := 748, numerator := 49517595668457107408908451840 }, { target := 1013, numerator := 49517607474373314583021486080 }, { target := 1015, numerator := 49517595668457107408908451840 }, { target := 1017, numerator := 45686765122823303989297152 }, { target := 1018, numerator := 685301476842349559839457280 }, { target := 1019, numerator := 1203084814901013671718158336 }, { target := 1020, numerator := 45686765122823303989297152 }, { target := 1021, numerator := 761446085380388399821619200 }, { target := 1022, numerator := 45686765122823303989297152 }, { target := 1023, numerator := 1203084814901013671718158336 }, { target := 1024, numerator := 1195470354047209787719942144 }, { target := 1025, numerator := 761446085380388399821619200 }, { target := 1026, numerator := 18449838648766810927677833216 }, { target := 1027, numerator := 1180241432339602019723509760 }, { target := 1028, numerator := 685301476842349559839457280 }, { target := 1029, numerator := 1203084814901013671718158336 }, { target := 1030, numerator := 45686765122823303989297152 }, { target := 1031, numerator := 1180241432339602019723509760 }, { target := 1032, numerator := 45686765122823303989297152 }, { target := 1033, numerator := 1203084814901013671718158336 }, { target := 1034, numerator := 1203084814901013671718158336 }, { target := 1035, numerator := 45686765122823303989297152 }, { target := 1036, numerator := 1356159070238587744677789696 }, { target := 1038, numerator := 52897505592020156489794584576 }, { target := 1041, numerator := 52897486189400009719783882752 }, { target := 1048, numerator := 1356165537778636668014690304 }, { target := 1052, numerator := 15978641664995183576775393280 }, { target := 1055, numerator := 57474698897373809170280611840 }, { target := 1057, numerator := 15978646995557033524110295040 }, { target := 1088, numerator := 49517607474373314583021486080 }, { target := 1090, numerator := 49517595668457107408908451840 }, { target := 1102, numerator := 49517607474373314583021486080 }, { target := 1104, numerator := 49517595668457107408908451840 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 6708471339183968559153807360 }, { target := 30, numerator := 5031353504387976419365355520 }, { target := 31, numerator := 5310873143520641775996764160 }, { target := 32, numerator := 6848231158750301237469511680 }, { target := 33, numerator := 91682441635514236975102033920 }, { target := 34, numerator := 160304513042583582028112855040 }, { target := 35, numerator := 4891593684821643741049651200 }, { target := 36, numerator := 91682441635514236975102033920 }, { target := 37, numerator := 5171113323954309097681059840 }, { target := 38, numerator := 5310873143520641775996764160 }, { target := 39, numerator := 5310873143520641775996764160 }, { target := 40, numerator := 5171113323954309097681059840 }, { target := 41, numerator := 160304513042583582028112855040 }, { target := 42, numerator := 5171113323954309097681059840 }, { target := 43, numerator := 6708471339183968559153807360 }, { target := 44, numerator := 6848231158750301237469511680 }, { target := 104, numerator := 262543390913382176467546275840 }, { target := 105, numerator := 196907543185036632350659706880 }, { target := 106, numerator := 207846851139760889703474135040 }, { target := 107, numerator := 268013044890744305143953489920 }, { target := 108, numerator := 3588093009149556411723132436480 }, { target := 109, numerator := 6273693112034361591839074549760 }, { target := 110, numerator := 191437889207674503674252492800 }, { target := 111, numerator := 3588093009149556411723132436480 }, { target := 112, numerator := 202377197162398761027066920960 }, { target := 113, numerator := 207846851139760889703474135040 }, { target := 114, numerator := 207846851139760889703474135040 }, { target := 115, numerator := 202377197162398761027066920960 }, { target := 116, numerator := 6273693112034361591839074549760 }, { target := 117, numerator := 202377197162398761027066920960 }, { target := 118, numerator := 262543390913382176467546275840 }, { target := 119, numerator := 268013044890744305143953489920 }, { target := 226, numerator := 262543487205386241231405711360 }, { target := 227, numerator := 196907615404039680923554283520 }, { target := 228, numerator := 207846927370930774308196188160 }, { target := 229, numerator := 268013143188831787923726663680 }, { target := 230, numerator := 3588094325140278630162544721920 }, { target := 231, numerator := 6273695413012042056092132311040 }, { target := 232, numerator := 191437959420594134231233331200 }, { target := 233, numerator := 3588094325140278630162544721920 }, { target := 234, numerator := 202377271387485227615875235840 }, { target := 235, numerator := 207846927370930774308196188160 }, { target := 236, numerator := 207846927370930774308196188160 }, { target := 237, numerator := 202377271387485227615875235840 }, { target := 238, numerator := 6273695413012042056092132311040 }, { target := 239, numerator := 202377271387485227615875235840 }, { target := 240, numerator := 262543487205386241231405711360 }, { target := 241, numerator := 268013143188831787923726663680 }, { target := 624, numerator := 6708567631188033323013242880 }, { target := 625, numerator := 5031425723391024992259932160 }, { target := 626, numerator := 5310949374690526380718817280 }, { target := 627, numerator := 6848329456837784017242685440 }, { target := 628, numerator := 91683757626236455414514319360 }, { target := 629, numerator := 160306814020264046281170616320 }, { target := 630, numerator := 4891663897741274298030489600 }, { target := 631, numerator := 91683757626236455414514319360 }, { target := 632, numerator := 5171187549040775686489374720 }, { target := 633, numerator := 5310949374690526380718817280 }, { target := 634, numerator := 5310949374690526380718817280 }, { target := 635, numerator := 5171187549040775686489374720 }, { target := 636, numerator := 160306814020264046281170616320 }, { target := 637, numerator := 5171187549040775686489374720 }, { target := 638, numerator := 6708567631188033323013242880 }, { target := 639, numerator := 6848329456837784017242685440 }]

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
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 53188868804029262132674560 }, { target := 72, numerator := 6286582807680902175978946560 }, { target := 74, numerator := 59658417698585892400303964160 }, { target := 82, numerator := 6286587119359631426081259520 }, { target := 89, numerator := 53188868804029262132674560 }, { target := 146, numerator := 17133270714703736637562552320 }, { target := 147, numerator := 2025042598880007891705994936320 }, { target := 149, numerator := 19217250598179922631101796843520 }, { target := 157, numerator := 2025043987763820691944049213440 }, { target := 164, numerator := 17133270714703736637562552320 }, { target := 200, numerator := 3181132600560641182311383040 }, { target := 202, numerator := 124493497235924690175359188992 }, { target := 205, numerator := 124493497235924690175359188992 }, { target := 212, numerator := 3181132600560641182311383040 }, { target := 242, numerator := 182219539077010047084942852096 }, { target := 243, numerator := 21537179626920186528172968247296 }, { target := 245, numerator := 204383541510409880285298825363456 }, { target := 253, numerator := 21537194398283600682683918712832 }, { target := 260, numerator := 182219539077010047084942852096 }, { target := 296, numerator := 557940771264775673283839262720 }, { target := 298, numerator := 21834989793578376956323358048256 }, { target := 301, numerator := 21834989793578376956323358048256 }, { target := 308, numerator := 557940771264775673283839262720 }, { target := 347, numerator := 7135245866797439411453689856 }, { target := 350, numerator := 26505660271939931523839426560 }, { target := 352, numerator := 7133743905224841869196787712 }, { target := 614, numerator := 172857085353705709612958744576 }, { target := 617, numerator := 642120995620222212077529333760 }, { target := 619, numerator := 172820699123350201411831857152 }, { target := 640, numerator := 17133322354382187151409283072 }, { target := 641, numerator := 2025048702358461950834321129472 }, { target := 643, numerator := 19217308518973804753327428206592 }, { target := 651, numerator := 2025050091246460846926016282624 }, { target := 658, numerator := 17133322354382187151409283072 }, { target := 659, numerator := 557940838155719184452356669440 }, { target := 661, numerator := 21834992411352778956548144627712 }, { target := 664, numerator := 21834992411352778956548144627712 }, { target := 671, numerator := 557940838155719184452356669440 }, { target := 710, numerator := 130966287038959452423133855744 }, { target := 713, numerator := 486507119184961968937568829440 }, { target := 715, numerator := 130938718776546291082999103488 }, { target := 736, numerator := 145927286437083115705214173184 }, { target := 739, numerator := 542083503626126341487554723840 }, { target := 741, numerator := 145896568900404830486153658368 }, { target := 881, numerator := 7135245866797439411453689856 }, { target := 884, numerator := 26505660271939931523839426560 }, { target := 886, numerator := 7133743905224841869196787712 }, { target := 977, numerator := 145927286437083115705214173184 }, { target := 980, numerator := 542083503626126341487554723840 }, { target := 982, numerator := 145896568900404830486153658368 }, { target := 1003, numerator := 145697117215573520885489860608 }, { target := 1006, numerator := 541228482327031504986785710080 }, { target := 1008, numerator := 145666448129268545264566665216 }, { target := 1017, numerator := 53188868804029262132674560 }, { target := 1018, numerator := 6286582807680902175978946560 }, { target := 1020, numerator := 59658417698585892400303964160 }, { target := 1028, numerator := 6286587119359631426081259520 }, { target := 1035, numerator := 53188868804029262132674560 }, { target := 1036, numerator := 3181065709617130013793976320 }, { target := 1038, numerator := 124490879461522689950572609536 }, { target := 1041, numerator := 124490879461522689950572609536 }, { target := 1048, numerator := 3181065709617130013793976320 }]

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
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 7135245866797439411453689856 }, { target := 6, numerator := 172857085353705709612958744576 }, { target := 7, numerator := 130966287038959452423133855744 }, { target := 8, numerator := 145927286437083115705214173184 }, { target := 9, numerator := 7135245866797439411453689856 }, { target := 10, numerator := 145927286437083115705214173184 }, { target := 11, numerator := 145697117215573520885489860608 }, { target := 12, numerator := 7135245866797439411453689856 }, { target := 13, numerator := 172857085353705709612958744576 }, { target := 14, numerator := 7135245866797439411453689856 }, { target := 29, numerator := 3175536940753146650768179200 }, { target := 30, numerator := 556959345105998583269267865600 }, { target := 35, numerator := 556959411879279924673196851200 }, { target := 43, numerator := 3175470167471805246839193600 }, { target := 71, numerator := 53117339932587587492904960 }, { target := 72, numerator := 17110229737411235646925701120 }, { target := 74, numerator := 181974488594120038952768372736 }, { target := 82, numerator := 17110281307644179906719383552 }, { target := 89, numerator := 53117339932587587492904960 }, { target := 94, numerator := 26505660271939931523839426560 }, { target := 95, numerator := 642120995620222212077529333760 }, { target := 96, numerator := 486507119184961968937568829440 }, { target := 97, numerator := 542083503626126341487554723840 }, { target := 98, numerator := 26505660271939931523839426560 }, { target := 99, numerator := 542083503626126341487554723840 }, { target := 100, numerator := 541228482327031504986785710080 }, { target := 101, numerator := 26505660271939931523839426560 }, { target := 102, numerator := 642120995620222212077529333760 }, { target := 103, numerator := 26505660271939931523839426560 }, { target := 104, numerator := 124274511312906352989474652160 }, { target := 105, numerator := 21796581720062847709258585210880 }, { target := 110, numerator := 21796584333232545396378314997760 }, { target := 118, numerator := 124271898143208665869744865280 }, { target := 216, numerator := 7133743905224841869196787712 }, { target := 217, numerator := 172820699123350201411831857152 }, { target := 218, numerator := 130938718776546291082999103488 }, { target := 219, numerator := 145896568900404830486153658368 }, { target := 220, numerator := 7133743905224841869196787712 }, { target := 221, numerator := 145896568900404830486153658368 }, { target := 222, numerator := 145666448129268545264566665216 }, { target := 223, numerator := 7133743905224841869196787712 }, { target := 224, numerator := 172820699123350201411831857152 }, { target := 225, numerator := 7133743905224841869196787712 }, { target := 226, numerator := 124274511312906352989474652160 }, { target := 227, numerator := 21796581720062847709258585210880 }, { target := 232, numerator := 21796584333232545396378314997760 }, { target := 240, numerator := 124271898143208665869744865280 }, { target := 624, numerator := 3175536940753146650768179200 }, { target := 625, numerator := 556959345105998583269267865600 }, { target := 630, numerator := 556959411879279924673196851200 }, { target := 638, numerator := 3175470167471805246839193600 }, { target := 1052, numerator := 7135245866797439411453689856 }, { target := 1055, numerator := 26505660271939931523839426560 }, { target := 1057, numerator := 7133743905224841869196787712 }, { target := 1078, numerator := 172857085353705709612958744576 }, { target := 1081, numerator := 642120995620222212077529333760 }, { target := 1083, numerator := 172820699123350201411831857152 }, { target := 1092, numerator := 7135245866797439411453689856 }, { target := 1095, numerator := 26505660271939931523839426560 }, { target := 1097, numerator := 7133743905224841869196787712 }]

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
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 6278128554308550236527656960 }, { target := 147, numerator := 2022319303292487708957600645120 }, { target := 149, numerator := 21508216233123897950270637735936 }, { target := 157, numerator := 2022325398562928785219966205952 }, { target := 164, numerator := 6278128554308550236527656960 }, { target := 200, numerator := 6627507029917955145508847616 }, { target := 202, numerator := 259374763781668943303282786304 }, { target := 205, numerator := 259374858911528131423440470016 }, { target := 212, numerator := 6627602159777143265666531328 }, { target := 242, numerator := 59578188519324749457323458560 }, { target := 243, numerator := 19191407065906953396794236600320 }, { target := 245, numerator := 204108684676748758875555282026496 }, { target := 253, numerator := 19191464908808428469366525263872 }, { target := 260, numerator := 59578188519324749457323458560 }, { target := 296, numerator := 4970630272438466359131635712 }, { target := 298, numerator := 194531072836251707477462089728 }, { target := 301, numerator := 194531144183646098567580352512 }, { target := 308, numerator := 4970701619832857449249898496 }, { target := 331, numerator := 5246776398685047823527837696 }, { target := 333, numerator := 205338354660487913448432205824 }, { target := 336, numerator := 205338429971626437376890372096 }, { target := 343, numerator := 5246851709823571751986003968 }, { target := 467, numerator := 6765580093041245877706948608 }, { target := 469, numerator := 264778404693787046288767844352 }, { target := 472, numerator := 264778501805518300828095479808 }, { target := 479, numerator := 6765677204772500417034584064 }, { target := 563, numerator := 90575929408878720321954250752 }, { target := 565, numerator := 3544788438349475558478198079488 }, { target := 568, numerator := 3544789738457551129453686423552 }, { target := 575, numerator := 90577229516954291297442594816 }, { target := 598, numerator := 158369803402414469831221837824 }, { target := 600, numerator := 6197976126199464124351361581056 }, { target := 603, numerator := 6197978399406724307139296231424 }, { target := 610, numerator := 158372076609674652619156488192 }, { target := 640, numerator := 6278132860188894966390456320 }, { target := 641, numerator := 2022320690308517006236754903040 }, { target := 643, numerator := 21508230984622649094891175411712 }, { target := 651, numerator := 2022326785583138548853227126784 }, { target := 658, numerator := 6278132860188894966390456320 }, { target := 659, numerator := 4832557209315175626933534720 }, { target := 661, numerator := 189127431924133604491977031680 }, { target := 664, numerator := 189127501289655929162925342720 }, { target := 671, numerator := 4832626574837500297881845760 }, { target := 694, numerator := 90575929408878720321954250752 }, { target := 696, numerator := 3544788438349475558478198079488 }, { target := 699, numerator := 3544789738457551129453686423552 }, { target := 706, numerator := 90577229516954291297442594816 }, { target := 720, numerator := 5108703335561757091329736704 }, { target := 722, numerator := 199934713748369810462947147776 }, { target := 725, numerator := 199934787077636267972235362304 }, { target := 732, numerator := 5108776664828214600617951232 }, { target := 830, numerator := 5246776398685047823527837696 }, { target := 832, numerator := 205338354660487913448432205824 }, { target := 835, numerator := 205338429971626437376890372096 }, { target := 842, numerator := 5246851709823571751986003968 }, { target := 865, numerator := 5246776398685047823527837696 }, { target := 867, numerator := 205338354660487913448432205824 }, { target := 870, numerator := 205338429971626437376890372096 }, { target := 877, numerator := 5246851709823571751986003968 }, { target := 1017, numerator := 53117339932587587492904960 }, { target := 1018, numerator := 17110229737411235646925701120 }, { target := 1020, numerator := 181974488594120038952768372736 }, { target := 1028, numerator := 17110281307644179906719383552 }, { target := 1035, numerator := 53117339932587587492904960 }]

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
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 49517607474373314583021486080 }, { target := 2, numerator := 49517607474373314583021486080 }, { target := 3, numerator := 49517607474373314583021486080 }, { target := 4, numerator := 49517607474373314583021486080 }, { target := 5, numerator := 16793461300154011066390544384 }, { target := 7, numerator := 759033899418070880662568566784 }, { target := 12, numerator := 16883093079994910949045698560 }, { target := 29, numerator := 1361126685880487333486133248 }, { target := 30, numerator := 269958841144135031749764710400 }, { target := 35, numerator := 269958841144135031749764710400 }, { target := 43, numerator := 1361126685880487333486133248 }, { target := 71, numerator := 45916925148630978064809984 }, { target := 72, numerator := 7524899697716735279974318080 }, { target := 74, numerator := 77471755943306779299812474880 }, { target := 82, numerator := 7524899697716735279974318080 }, { target := 89, numerator := 45916925148630978064809984 }, { target := 90, numerator := 49517595668457107408908451840 }, { target := 91, numerator := 49517595668457107408908451840 }, { target := 92, numerator := 49517595668457107408908451840 }, { target := 93, numerator := 49517595668457107408908451840 }, { target := 94, numerator := 60405580893996624615154122752 }, { target := 96, numerator := 2730222364115222251292906749952 }, { target := 101, numerator := 60727983740621383274258759680 }, { target := 104, numerator := 53091269348767483070343282688 }, { target := 105, numerator := 10529848321203847554444715622400 }, { target := 110, numerator := 10529848321203847554444715622400 }, { target := 118, numerator := 53091269348767483070343282688 }, { target := 146, numerator := 688753877229464670972149760 }, { target := 147, numerator := 112873495465751029199614771200 }, { target := 149, numerator := 1162076339149601689497187123200 }, { target := 157, numerator := 112873495465751029199614771200 }, { target := 164, numerator := 688753877229464670972149760 }, { target := 216, numerator := 16793466902544127322553843712 }, { target := 218, numerator := 759034152635912039124447526912 }, { target := 223, numerator := 16883098712286676931135406080 }, { target := 226, numerator := 53091249875075467630845362176 }, { target := 227, numerator := 10529844458892290651035847884800 }, { target := 232, numerator := 10529844458892290651035847884800 }, { target := 240, numerator := 53091249875075467630845362176 }, { target := 624, numerator := 1361133177111159146652106752 }, { target := 625, numerator := 269960128581320666219387289600 }, { target := 630, numerator := 269960128581320666219387289600 }, { target := 638, numerator := 1361133177111159146652106752 }, { target := 926, numerator := 5108703335561757091329736704 }, { target := 928, numerator := 199934713748369810462947147776 }, { target := 931, numerator := 199934787077636267972235362304 }, { target := 938, numerator := 5108776664828214600617951232 }, { target := 961, numerator := 158369803402414469831221837824 }, { target := 963, numerator := 6197976126199464124351361581056 }, { target := 966, numerator := 6197978399406724307139296231424 }, { target := 973, numerator := 158372076609674652619156488192 }, { target := 987, numerator := 5108703335561757091329736704 }, { target := 989, numerator := 199934713748369810462947147776 }, { target := 992, numerator := 199934787077636267972235362304 }, { target := 999, numerator := 5108776664828214600617951232 }, { target := 1036, numerator := 6627507029917955145508847616 }, { target := 1038, numerator := 259374763781668943303282786304 }, { target := 1041, numerator := 259374858911528131423440470016 }, { target := 1048, numerator := 6627602159777143265666531328 }, { target := 1062, numerator := 6765580093041245877706948608 }, { target := 1064, numerator := 264778404693787046288767844352 }, { target := 1067, numerator := 264778501805518300828095479808 }, { target := 1074, numerator := 6765677204772500417034584064 }]

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
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 181, numerator := 1209145695580615755706662912 }, { target := 182, numerator := 198155692039874029039323709440 }, { target := 184, numerator := 2040089573173745188228395171840 }, { target := 192, numerator := 198155692039874029039323709440 }, { target := 199, numerator := 1209145695580615755706662912 }, { target := 242, numerator := 45916925148630978064809984 }, { target := 243, numerator := 7524899697716735279974318080 }, { target := 245, numerator := 77471755943306779299812474880 }, { target := 253, numerator := 7524899697716735279974318080 }, { target := 260, numerator := 45916925148630978064809984 }, { target := 277, numerator := 765282085810516301080166400 }, { target := 278, numerator := 125414994961945587999571968000 }, { target := 280, numerator := 1291195932388446321663541248000 }, { target := 288, numerator := 125414994961945587999571968000 }, { target := 295, numerator := 765282085810516301080166400 }, { target := 312, numerator := 45916925148630978064809984 }, { target := 313, numerator := 7524899697716735279974318080 }, { target := 315, numerator := 77471755943306779299812474880 }, { target := 323, numerator := 7524899697716735279974318080 }, { target := 330, numerator := 45916925148630978064809984 }, { target := 413, numerator := 1209145695580615755706662912 }, { target := 414, numerator := 198155692039874029039323709440 }, { target := 416, numerator := 2040089573173745188228395171840 }, { target := 424, numerator := 198155692039874029039323709440 }, { target := 431, numerator := 1209145695580615755706662912 }, { target := 448, numerator := 1201492874722510592695861248 }, { target := 449, numerator := 196901542090254573159327989760 }, { target := 451, numerator := 2027177613849860725011759759360 }, { target := 459, numerator := 196901542090254573159327989760 }, { target := 466, numerator := 1201492874722510592695861248 }, { target := 509, numerator := 765282085810516301080166400 }, { target := 510, numerator := 125414994961945587999571968000 }, { target := 512, numerator := 1291195932388446321663541248000 }, { target := 520, numerator := 125414994961945587999571968000 }, { target := 527, numerator := 765282085810516301080166400 }, { target := 544, numerator := 18542784939188809975172431872 }, { target := 545, numerator := 3038805327927941597229628784640 }, { target := 547, numerator := 31285677441772054373907604439040 }, { target := 555, numerator := 3038805327927941597229628784640 }, { target := 562, numerator := 18542784939188809975172431872 }, { target := 579, numerator := 1186187233006300266674257920 }, { target := 580, numerator := 194393242191015661399336550400 }, { target := 582, numerator := 2001353695202091798578488934400 }, { target := 590, numerator := 194393242191015661399336550400 }, { target := 597, numerator := 1186187233006300266674257920 }, { target := 640, numerator := 688753877229464670972149760 }, { target := 641, numerator := 112873495465751029199614771200 }, { target := 643, numerator := 1162076339149601689497187123200 }, { target := 651, numerator := 112873495465751029199614771200 }, { target := 658, numerator := 688753877229464670972149760 }, { target := 675, numerator := 1209145695580615755706662912 }, { target := 676, numerator := 198155692039874029039323709440 }, { target := 678, numerator := 2040089573173745188228395171840 }, { target := 686, numerator := 198155692039874029039323709440 }, { target := 693, numerator := 1209145695580615755706662912 }, { target := 776, numerator := 45916925148630978064809984 }, { target := 777, numerator := 7524899697716735279974318080 }, { target := 779, numerator := 77471755943306779299812474880 }, { target := 787, numerator := 7524899697716735279974318080 }, { target := 794, numerator := 45916925148630978064809984 }]

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

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left14.expected,
    Slot19.Left15.expected,
    Slot19.Left16.expected,
    Slot19.Left17.expected,
    Slot19.Left18.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9942204755307403596944900096 }, { target := 2, numerator := 9913190539095417010572492800 }, { target := 3, numerator := 9845490701267448309036875776 }, { target := 4, numerator := 9913190539095417010572492800 }, { target := 5, numerator := 742570030231851405810860032 }, { target := 6, numerator := 18204942676651840916653342720 }, { target := 7, numerator := 13462076031945177098893656064 }, { target := 8, numerator := 15019077708237768756239007744 }, { target := 9, numerator := 742570030231851405810860032 }, { target := 10, numerator := 14995123836294805807664463872 }, { target := 11, numerator := 15258616427667398241984446464 }, { target := 12, numerator := 742570030231851405810860032 }, { target := 13, numerator := 18204942676651840916653342720 }, { target := 14, numerator := 742570030231851405810860032 }, { target := 90, numerator := 9942207125714017068622282752 }, { target := 91, numerator := 9913192902584501454608793600 }, { target := 92, numerator := 9845493048615631688577318912 }, { target := 93, numerator := 9913192902584501454608793600 }, { target := 94, numerator := 2712250635422256182643916800 }, { target := 95, numerator := 66493886545835958026108928000 }, { target := 96, numerator := 49170479261526063698254233600 }, { target := 97, numerator := 54857456400314665371539865600 }, { target := 98, numerator := 2712250635422256182643916800 }, { target := 99, numerator := 54769964444333302268873932800 }, { target := 100, numerator := 55732375960128296398199193600 }, { target := 101, numerator := 2712250635422256182643916800 }, { target := 102, numerator := 66493886545835958026108928000 }, { target := 103, numerator := 2712250635422256182643916800 }, { target := 216, numerator := 742569780047884906125066240 }, { target := 217, numerator := 18204936543109436408227430400 }, { target := 218, numerator := 13462071496351977975557652480 }, { target := 219, numerator := 15019072648065285036787630080 }, { target := 220, numerator := 742569780047884906125066240 }, { target := 221, numerator := 14995118784192772620461015040 }, { target := 222, numerator := 15258611286790409200053780480 }, { target := 223, numerator := 742569780047884906125066240 }, { target := 224, numerator := 18204936543109436408227430400 }, { target := 225, numerator := 742569780047884906125066240 }, { target := 811, numerator := 1186187233006300266674257920 }, { target := 812, numerator := 194393242191015661399336550400 }, { target := 814, numerator := 2001353695202091798578488934400 }, { target := 822, numerator := 194393242191015661399336550400 }, { target := 829, numerator := 1186187233006300266674257920 }, { target := 846, numerator := 45916925148630978064809984 }, { target := 847, numerator := 7524899697716735279974318080 }, { target := 849, numerator := 77471755943306779299812474880 }, { target := 857, numerator := 7524899697716735279974318080 }, { target := 864, numerator := 45916925148630978064809984 }, { target := 907, numerator := 1209145695580615755706662912 }, { target := 908, numerator := 198155692039874029039323709440 }, { target := 910, numerator := 2040089573173745188228395171840 }, { target := 918, numerator := 198155692039874029039323709440 }, { target := 925, numerator := 1209145695580615755706662912 }, { target := 942, numerator := 1209145695580615755706662912 }, { target := 943, numerator := 198155692039874029039323709440 }, { target := 945, numerator := 2040089573173745188228395171840 }, { target := 953, numerator := 198155692039874029039323709440 }, { target := 960, numerator := 1209145695580615755706662912 }, { target := 1017, numerator := 45916925148630978064809984 }, { target := 1018, numerator := 7524899697716735279974318080 }, { target := 1020, numerator := 77471755943306779299812474880 }, { target := 1028, numerator := 7524899697716735279974318080 }, { target := 1035, numerator := 45916925148630978064809984 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 199756102225385992539340800 }, { target := 30, numerator := 148754544210393824231424000 }, { target := 31, numerator := 157254803879559185616076800 }, { target := 32, numerator := 204006232059968673231667200 }, { target := 33, numerator := 2732833483636663685165875200 }, { target := 34, numerator := 4942900997619657645175603200 }, { target := 35, numerator := 148754544210393824231424000 }, { target := 36, numerator := 2732833483636663685165875200 }, { target := 37, numerator := 161504933714141866308403200 }, { target := 38, numerator := 161504933714141866308403200 }, { target := 39, numerator := 157254803879559185616076800 }, { target := 40, numerator := 157254803879559185616076800 }, { target := 41, numerator := 4942900997619657645175603200 }, { target := 42, numerator := 157254803879559185616076800 }, { target := 43, numerator := 199756102225385992539340800 }, { target := 44, numerator := 204006232059968673231667200 }, { target := 55, numerator := 227500005312245158169804800 }, { target := 56, numerator := 169414897572948522041344000 }, { target := 57, numerator := 179095748862831294729420800 }, { target := 58, numerator := 232340430957186544513843200 }, { target := 59, numerator := 3112393689697311419216691200 }, { target := 60, numerator := 5629415025066832318116659200 }, { target := 61, numerator := 169414897572948522041344000 }, { target := 62, numerator := 3112393689697311419216691200 }, { target := 63, numerator := 183936174507772681073459200 }, { target := 64, numerator := 183936174507772681073459200 }, { target := 65, numerator := 179095748862831294729420800 }, { target := 66, numerator := 179095748862831294729420800 }, { target := 67, numerator := 5629415025066832318116659200 }, { target := 68, numerator := 179095748862831294729420800 }, { target := 69, numerator := 227500005312245158169804800 }, { target := 70, numerator := 232340430957186544513843200 }, { target := 104, numerator := 177560979755898660034969600 }, { target := 105, numerator := 132226261520350065983488000 }, { target := 106, numerator := 139782047892941498325401600 }, { target := 107, numerator := 181338872942194376205926400 }, { target := 108, numerator := 2429185318788145497925222400 }, { target := 109, numerator := 4393689775661917906822758400 }, { target := 110, numerator := 132226261520350065983488000 }, { target := 111, numerator := 2429185318788145497925222400 }, { target := 112, numerator := 143559941079237214496358400 }, { target := 113, numerator := 143559941079237214496358400 }, { target := 114, numerator := 139782047892941498325401600 }, { target := 115, numerator := 139782047892941498325401600 }, { target := 116, numerator := 4393689775661917906822758400 }, { target := 117, numerator := 139782047892941498325401600 }, { target := 118, numerator := 177560979755898660034969600 }, { target := 119, numerator := 181338872942194376205926400 }, { target := 130, numerator := 2380426884852516411093811200 }, { target := 131, numerator := 1772658318507193072091136000 }, { target := 132, numerator := 1873953079564746961924915200 }, { target := 133, numerator := 2431074265381293356010700800 }, { target := 134, numerator := 32566265680003575581560012800 }, { target := 135, numerator := 58902903554967586938342604800 }, { target := 136, numerator := 1772658318507193072091136000 }, { target := 137, numerator := 32566265680003575581560012800 }, { target := 138, numerator := 1924600460093523906841804800 }, { target := 139, numerator := 1924600460093523906841804800 }, { target := 140, numerator := 1873953079564746961924915200 }, { target := 141, numerator := 1873953079564746961924915200 }, { target := 142, numerator := 58902903554967586938342604800 }, { target := 143, numerator := 1873953079564746961924915200 }, { target := 144, numerator := 2380426884852516411093811200 }, { target := 145, numerator := 2431074265381293356010700800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 165, numerator := 210853663460129658791526400 }, { target := 166, numerator := 157018685555415703355392000 }, { target := 167, numerator := 165991181872868029261414400 }, { target := 168, numerator := 215339911618855821744537600 }, { target := 169, numerator := 2884657566060922778786201600 }, { target := 170, numerator := 5217506608598527514352025600 }, { target := 171, numerator := 157018685555415703355392000 }, { target := 172, numerator := 2884657566060922778786201600 }, { target := 173, numerator := 170477430031594192214425600 }, { target := 174, numerator := 170477430031594192214425600 }, { target := 175, numerator := 165991181872868029261414400 }, { target := 176, numerator := 165991181872868029261414400 }, { target := 177, numerator := 5217506608598527514352025600 }, { target := 178, numerator := 165991181872868029261414400 }, { target := 179, numerator := 210853663460129658791526400 }, { target := 180, numerator := 215339911618855821744537600 }, { target := 226, numerator := 177560979755898660034969600 }, { target := 227, numerator := 132226261520350065983488000 }, { target := 228, numerator := 139782047892941498325401600 }, { target := 229, numerator := 181338872942194376205926400 }, { target := 230, numerator := 2429185318788145497925222400 }, { target := 231, numerator := 4393689775661917906822758400 }, { target := 232, numerator := 132226261520350065983488000 }, { target := 233, numerator := 2429185318788145497925222400 }, { target := 234, numerator := 143559941079237214496358400 }, { target := 235, numerator := 143559941079237214496358400 }, { target := 236, numerator := 139782047892941498325401600 }, { target := 237, numerator := 139782047892941498325401600 }, { target := 238, numerator := 4393689775661917906822758400 }, { target := 239, numerator := 139782047892941498325401600 }, { target := 240, numerator := 177560979755898660034969600 }, { target := 241, numerator := 181338872942194376205926400 }, { target := 261, numerator := 210853663460129658791526400 }, { target := 262, numerator := 157018685555415703355392000 }, { target := 263, numerator := 165991181872868029261414400 }, { target := 264, numerator := 215339911618855821744537600 }, { target := 265, numerator := 2884657566060922778786201600 }, { target := 266, numerator := 5217506608598527514352025600 }, { target := 267, numerator := 157018685555415703355392000 }, { target := 268, numerator := 2884657566060922778786201600 }, { target := 269, numerator := 170477430031594192214425600 }, { target := 270, numerator := 170477430031594192214425600 }, { target := 271, numerator := 165991181872868029261414400 }, { target := 272, numerator := 165991181872868029261414400 }, { target := 273, numerator := 5217506608598527514352025600 }, { target := 274, numerator := 165991181872868029261414400 }, { target := 275, numerator := 210853663460129658791526400 }, { target := 276, numerator := 215339911618855821744537600 }, { target := 371, numerator := 205304882842757825665433600 }, { target := 372, numerator := 152886614882904763793408000 }, { target := 373, numerator := 161622992876213607438745600 }, { target := 374, numerator := 209673071839412247488102400 }, { target := 375, numerator := 2808745524848793231976038400 }, { target := 376, numerator := 5080203803109092579763814400 }, { target := 377, numerator := 152886614882904763793408000 }, { target := 378, numerator := 2808745524848793231976038400 }, { target := 379, numerator := 165991181872868029261414400 }, { target := 380, numerator := 165991181872868029261414400 }, { target := 381, numerator := 161622992876213607438745600 }, { target := 382, numerator := 161622992876213607438745600 }, { target := 383, numerator := 5080203803109092579763814400 }, { target := 384, numerator := 161622992876213607438745600 }, { target := 385, numerator := 205304882842757825665433600 }, { target := 386, numerator := 209673071839412247488102400 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 397, numerator := 7757195303085822710277734400 }, { target := 398, numerator := 5776634800170293507653632000 }, { target := 399, numerator := 6106728217322881708090982400 }, { target := 400, numerator := 7922242011662116810496409600 }, { target := 401, numerator := 106125033614557106440608153600 }, { target := 402, numerator := 191949322074230038554319257600 }, { target := 403, numerator := 5776634800170293507653632000 }, { target := 404, numerator := 106125033614557106440608153600 }, { target := 405, numerator := 6271774925899175808309657600 }, { target := 406, numerator := 6271774925899175808309657600 }, { target := 407, numerator := 6106728217322881708090982400 }, { target := 408, numerator := 6106728217322881708090982400 }, { target := 409, numerator := 191949322074230038554319257600 }, { target := 410, numerator := 6106728217322881708090982400 }, { target := 411, numerator := 7757195303085822710277734400 }, { target := 412, numerator := 7922242011662116810496409600 }, { target := 432, numerator := 205304882842757825665433600 }, { target := 433, numerator := 152886614882904763793408000 }, { target := 434, numerator := 161622992876213607438745600 }, { target := 435, numerator := 209673071839412247488102400 }, { target := 436, numerator := 2808745524848793231976038400 }, { target := 437, numerator := 5080203803109092579763814400 }, { target := 438, numerator := 152886614882904763793408000 }, { target := 439, numerator := 2808745524848793231976038400 }, { target := 440, numerator := 165991181872868029261414400 }, { target := 441, numerator := 165991181872868029261414400 }, { target := 442, numerator := 161622992876213607438745600 }, { target := 443, numerator := 161622992876213607438745600 }, { target := 444, numerator := 5080203803109092579763814400 }, { target := 445, numerator := 161622992876213607438745600 }, { target := 446, numerator := 205304882842757825665433600 }, { target := 447, numerator := 209673071839412247488102400 }, { target := 493, numerator := 2380426884852516411093811200 }, { target := 494, numerator := 1772658318507193072091136000 }, { target := 495, numerator := 1873953079564746961924915200 }, { target := 496, numerator := 2431074265381293356010700800 }, { target := 497, numerator := 32566265680003575581560012800 }, { target := 498, numerator := 58902903554967586938342604800 }, { target := 499, numerator := 1772658318507193072091136000 }, { target := 500, numerator := 32566265680003575581560012800 }, { target := 501, numerator := 1924600460093523906841804800 }, { target := 502, numerator := 1924600460093523906841804800 }, { target := 503, numerator := 1873953079564746961924915200 }, { target := 504, numerator := 1873953079564746961924915200 }, { target := 505, numerator := 58902903554967586938342604800 }, { target := 506, numerator := 1873953079564746961924915200 }, { target := 507, numerator := 2380426884852516411093811200 }, { target := 508, numerator := 2431074265381293356010700800 }, { target := 528, numerator := 7757195303085822710277734400 }, { target := 529, numerator := 5776634800170293507653632000 }, { target := 530, numerator := 6106728217322881708090982400 }, { target := 531, numerator := 7922242011662116810496409600 }, { target := 532, numerator := 106125033614557106440608153600 }, { target := 533, numerator := 191949322074230038554319257600 }, { target := 534, numerator := 5776634800170293507653632000 }, { target := 535, numerator := 106125033614557106440608153600 }, { target := 536, numerator := 6271774925899175808309657600 }, { target := 537, numerator := 6271774925899175808309657600 }, { target := 538, numerator := 6106728217322881708090982400 }, { target := 539, numerator := 6106728217322881708090982400 }, { target := 540, numerator := 191949322074230038554319257600 }, { target := 541, numerator := 6106728217322881708090982400 }, { target := 542, numerator := 7757195303085822710277734400 }, { target := 543, numerator := 7922242011662116810496409600 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 624, numerator := 199756102225385992539340800 }, { target := 625, numerator := 148754544210393824231424000 }, { target := 626, numerator := 157254803879559185616076800 }, { target := 627, numerator := 204006232059968673231667200 }, { target := 628, numerator := 2732833483636663685165875200 }, { target := 629, numerator := 4942900997619657645175603200 }, { target := 630, numerator := 148754544210393824231424000 }, { target := 631, numerator := 2732833483636663685165875200 }, { target := 632, numerator := 161504933714141866308403200 }, { target := 633, numerator := 161504933714141866308403200 }, { target := 634, numerator := 157254803879559185616076800 }, { target := 635, numerator := 157254803879559185616076800 }, { target := 636, numerator := 4942900997619657645175603200 }, { target := 637, numerator := 157254803879559185616076800 }, { target := 638, numerator := 199756102225385992539340800 }, { target := 639, numerator := 204006232059968673231667200 }, { target := 760, numerator := 205304882842757825665433600 }, { target := 761, numerator := 152886614882904763793408000 }, { target := 762, numerator := 161622992876213607438745600 }, { target := 763, numerator := 209673071839412247488102400 }, { target := 764, numerator := 2808745524848793231976038400 }, { target := 765, numerator := 5080203803109092579763814400 }, { target := 766, numerator := 152886614882904763793408000 }, { target := 767, numerator := 2808745524848793231976038400 }, { target := 768, numerator := 165991181872868029261414400 }, { target := 769, numerator := 165991181872868029261414400 }, { target := 770, numerator := 161622992876213607438745600 }, { target := 771, numerator := 161622992876213607438745600 }, { target := 772, numerator := 5080203803109092579763814400 }, { target := 773, numerator := 161622992876213607438745600 }, { target := 774, numerator := 205304882842757825665433600 }, { target := 775, numerator := 209673071839412247488102400 }, { target := 795, numerator := 205304882842757825665433600 }, { target := 796, numerator := 152886614882904763793408000 }, { target := 797, numerator := 161622992876213607438745600 }, { target := 798, numerator := 209673071839412247488102400 }, { target := 799, numerator := 2808745524848793231976038400 }, { target := 800, numerator := 5080203803109092579763814400 }, { target := 801, numerator := 152886614882904763793408000 }, { target := 802, numerator := 2808745524848793231976038400 }, { target := 803, numerator := 165991181872868029261414400 }, { target := 804, numerator := 165991181872868029261414400 }, { target := 805, numerator := 161622992876213607438745600 }, { target := 806, numerator := 161622992876213607438745600 }, { target := 807, numerator := 5080203803109092579763814400 }, { target := 808, numerator := 161622992876213607438745600 }, { target := 809, numerator := 205304882842757825665433600 }, { target := 810, numerator := 209673071839412247488102400 }, { target := 891, numerator := 227500005312245158169804800 }, { target := 892, numerator := 169414897572948522041344000 }, { target := 893, numerator := 179095748862831294729420800 }, { target := 894, numerator := 232340430957186544513843200 }, { target := 895, numerator := 3112393689697311419216691200 }, { target := 896, numerator := 5629415025066832318116659200 }, { target := 897, numerator := 169414897572948522041344000 }, { target := 898, numerator := 3112393689697311419216691200 }, { target := 899, numerator := 183936174507772681073459200 }, { target := 900, numerator := 183936174507772681073459200 }, { target := 901, numerator := 179095748862831294729420800 }, { target := 902, numerator := 179095748862831294729420800 }, { target := 903, numerator := 5629415025066832318116659200 }, { target := 904, numerator := 179095748862831294729420800 }, { target := 905, numerator := 227500005312245158169804800 }, { target := 906, numerator := 232340430957186544513843200 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3
