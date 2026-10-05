import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1

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
  [{ target := 121, numerator := 77239026193815917115211776 }, { target := 122, numerator := 1158585392907238756728176640 }, { target := 123, numerator := 2033961023103819150700576768 }, { target := 124, numerator := 77239026193815917115211776 }, { target := 125, numerator := 1287317103230265285253529600 }, { target := 126, numerator := 77239026193815917115211776 }, { target := 127, numerator := 2033961023103819150700576768 }, { target := 128, numerator := 2021087852071516497848041472 }, { target := 129, numerator := 1287317103230265285253529600 }, { target := 130, numerator := 31191693411269327861693022208 }, { target := 131, numerator := 1995341510006911192142970880 }, { target := 132, numerator := 1158585392907238756728176640 }, { target := 133, numerator := 2033961023103819150700576768 }, { target := 134, numerator := 77239026193815917115211776 }, { target := 135, numerator := 1995341510006911192142970880 }, { target := 136, numerator := 77239026193815917115211776 }, { target := 137, numerator := 2033961023103819150700576768 }, { target := 138, numerator := 2033961023103819150700576768 }, { target := 139, numerator := 77239026193815917115211776 }, { target := 196, numerator := 57518423761352278702817280 }, { target := 197, numerator := 862776356420284180542259200 }, { target := 198, numerator := 1514651825715610005840855040 }, { target := 199, numerator := 57518423761352278702817280 }, { target := 200, numerator := 958640396022537978380288000 }, { target := 201, numerator := 57518423761352278702817280 }, { target := 202, numerator := 1514651825715610005840855040 }, { target := 203, numerator := 1505065421755384626057052160 }, { target := 204, numerator := 958640396022537978380288000 }, { target := 205, numerator := 23227856795626095216154378240 }, { target := 206, numerator := 1485892613834933866489446400 }, { target := 207, numerator := 862776356420284180542259200 }, { target := 208, numerator := 1514651825715610005840855040 }, { target := 209, numerator := 57518423761352278702817280 }, { target := 210, numerator := 1485892613834933866489446400 }, { target := 211, numerator := 57518423761352278702817280 }, { target := 212, numerator := 1514651825715610005840855040 }, { target := 213, numerator := 1514651825715610005840855040 }, { target := 214, numerator := 57518423761352278702817280 }, { target := 231, numerator := 60805190833429551771549696 }, { target := 232, numerator := 912077862501443276573245440 }, { target := 233, numerator := 1601203358613644863317475328 }, { target := 234, numerator := 60805190833429551771549696 }, { target := 235, numerator := 1013419847223825862859161600 }, { target := 236, numerator := 60805190833429551771549696 }, { target := 237, numerator := 1601203358613644863317475328 }, { target := 238, numerator := 1591069160141406604688883712 }, { target := 239, numerator := 1013419847223825862859161600 }, { target := 240, numerator := 24555162898233300657077485568 }, { target := 241, numerator := 1570800763196930087431700480 }, { target := 242, numerator := 912077862501443276573245440 }, { target := 243, numerator := 1601203358613644863317475328 }, { target := 244, numerator := 60805190833429551771549696 }, { target := 245, numerator := 1570800763196930087431700480 }, { target := 246, numerator := 60805190833429551771549696 }, { target := 247, numerator := 1601203358613644863317475328 }, { target := 248, numerator := 1601203358613644863317475328 }, { target := 249, numerator := 60805190833429551771549696 }]

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
  [{ target := 337, numerator := 78882409729854553649577984 }, { target := 338, numerator := 1183236145947818304743669760 }, { target := 339, numerator := 2077236789552836579438886912 }, { target := 340, numerator := 78882409729854553649577984 }, { target := 341, numerator := 1314706828830909227492966400 }, { target := 342, numerator := 78882409729854553649577984 }, { target := 343, numerator := 2077236789552836579438886912 }, { target := 344, numerator := 2064089721264527487163957248 }, { target := 345, numerator := 1314706828830909227492966400 }, { target := 346, numerator := 31855346462572930582154575872 }, { target := 347, numerator := 2037795584687909302614097920 }, { target := 348, numerator := 1183236145947818304743669760 }, { target := 349, numerator := 2077236789552836579438886912 }, { target := 350, numerator := 78882409729854553649577984 }, { target := 351, numerator := 2037795584687909302614097920 }, { target := 352, numerator := 78882409729854553649577984 }, { target := 353, numerator := 2077236789552836579438886912 }, { target := 354, numerator := 2077236789552836579438886912 }, { target := 355, numerator := 78882409729854553649577984 }, { target := 412, numerator := 1056695613672843291597471744 }, { target := 413, numerator := 15850434205092649373962076160 }, { target := 414, numerator := 27826317826718206678733422592 }, { target := 415, numerator := 1056695613672843291597471744 }, { target := 416, numerator := 17611593561214054859957862400 }, { target := 417, numerator := 1056695613672843291597471744 }, { target := 418, numerator := 27826317826718206678733422592 }, { target := 419, numerator := 27650201891106066130133843968 }, { target := 420, numerator := 17611593561214054859957862400 }, { target := 421, numerator := 426728911988216549256779005952 }, { target := 422, numerator := 27297970019881785032934686720 }, { target := 423, numerator := 15850434205092649373962076160 }, { target := 424, numerator := 27826317826718206678733422592 }, { target := 425, numerator := 1056695613672843291597471744 }, { target := 426, numerator := 27297970019881785032934686720 }, { target := 427, numerator := 1056695613672843291597471744 }, { target := 428, numerator := 27826317826718206678733422592 }, { target := 429, numerator := 27826317826718206678733422592 }, { target := 430, numerator := 1056695613672843291597471744 }, { target := 447, numerator := 1911255052412934289467899904 }, { target := 448, numerator := 28668825786194014342018498560 }, { target := 449, numerator := 50329716380207269622654697472 }, { target := 450, numerator := 1911255052412934289467899904 }, { target := 451, numerator := 31854250873548904824464998400 }, { target := 452, numerator := 1911255052412934289467899904 }, { target := 453, numerator := 50329716380207269622654697472 }, { target := 454, numerator := 50011173871471780574410047488 }, { target := 455, numerator := 31854250873548904824464998400 }, { target := 456, numerator := 771828498666089963896786911232 }, { target := 457, numerator := 49374088854000802477920747520 }, { target := 458, numerator := 28668825786194014342018498560 }, { target := 459, numerator := 50329716380207269622654697472 }, { target := 460, numerator := 1911255052412934289467899904 }, { target := 461, numerator := 49374088854000802477920747520 }, { target := 462, numerator := 1911255052412934289467899904 }, { target := 463, numerator := 50329716380207269622654697472 }, { target := 464, numerator := 50329716380207269622654697472 }, { target := 465, numerator := 1911255052412934289467899904 }]

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
  [{ target := 508, numerator := 57518423761352278702817280 }, { target := 509, numerator := 862776356420284180542259200 }, { target := 510, numerator := 1514651825715610005840855040 }, { target := 511, numerator := 57518423761352278702817280 }, { target := 512, numerator := 958640396022537978380288000 }, { target := 513, numerator := 57518423761352278702817280 }, { target := 514, numerator := 1514651825715610005840855040 }, { target := 515, numerator := 1505065421755384626057052160 }, { target := 516, numerator := 958640396022537978380288000 }, { target := 517, numerator := 23227856795626095216154378240 }, { target := 518, numerator := 1485892613834933866489446400 }, { target := 519, numerator := 862776356420284180542259200 }, { target := 520, numerator := 1514651825715610005840855040 }, { target := 521, numerator := 57518423761352278702817280 }, { target := 522, numerator := 1485892613834933866489446400 }, { target := 523, numerator := 57518423761352278702817280 }, { target := 524, numerator := 1514651825715610005840855040 }, { target := 525, numerator := 1514651825715610005840855040 }, { target := 526, numerator := 57518423761352278702817280 }, { target := 543, numerator := 1056695613672843291597471744 }, { target := 544, numerator := 15850434205092649373962076160 }, { target := 545, numerator := 27826317826718206678733422592 }, { target := 546, numerator := 1056695613672843291597471744 }, { target := 547, numerator := 17611593561214054859957862400 }, { target := 548, numerator := 1056695613672843291597471744 }, { target := 549, numerator := 27826317826718206678733422592 }, { target := 550, numerator := 27650201891106066130133843968 }, { target := 551, numerator := 17611593561214054859957862400 }, { target := 552, numerator := 426728911988216549256779005952 }, { target := 553, numerator := 27297970019881785032934686720 }, { target := 554, numerator := 15850434205092649373962076160 }, { target := 555, numerator := 27826317826718206678733422592 }, { target := 556, numerator := 1056695613672843291597471744 }, { target := 557, numerator := 27297970019881785032934686720 }, { target := 558, numerator := 1056695613672843291597471744 }, { target := 559, numerator := 27826317826718206678733422592 }, { target := 560, numerator := 27826317826718206678733422592 }, { target := 561, numerator := 1056695613672843291597471744 }, { target := 578, numerator := 62448574369468188305915904 }, { target := 579, numerator := 936728615542022824588738560 }, { target := 580, numerator := 1644479125062662292055785472 }, { target := 581, numerator := 62448574369468188305915904 }, { target := 582, numerator := 1040809572824469805098598400 }, { target := 583, numerator := 62448574369468188305915904 }, { target := 584, numerator := 1644479125062662292055785472 }, { target := 585, numerator := 1634071029334417594004799488 }, { target := 586, numerator := 1040809572824469805098598400 }, { target := 587, numerator := 25218815949536903377539039232 }, { target := 588, numerator := 1613254837877928197902827520 }, { target := 589, numerator := 936728615542022824588738560 }, { target := 590, numerator := 1644479125062662292055785472 }, { target := 591, numerator := 62448574369468188305915904 }, { target := 592, numerator := 1613254837877928197902827520 }, { target := 593, numerator := 62448574369468188305915904 }, { target := 594, numerator := 1644479125062662292055785472 }, { target := 595, numerator := 1644479125062662292055785472 }, { target := 596, numerator := 62448574369468188305915904 }]

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
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 679, numerator := 62448574369468188305915904 }, { target := 680, numerator := 936728615542022824588738560 }, { target := 681, numerator := 1644479125062662292055785472 }, { target := 682, numerator := 62448574369468188305915904 }, { target := 683, numerator := 1040809572824469805098598400 }, { target := 684, numerator := 62448574369468188305915904 }, { target := 685, numerator := 1644479125062662292055785472 }, { target := 686, numerator := 1634071029334417594004799488 }, { target := 687, numerator := 1040809572824469805098598400 }, { target := 688, numerator := 25218815949536903377539039232 }, { target := 689, numerator := 1613254837877928197902827520 }, { target := 690, numerator := 936728615542022824588738560 }, { target := 691, numerator := 1644479125062662292055785472 }, { target := 692, numerator := 62448574369468188305915904 }, { target := 693, numerator := 1613254837877928197902827520 }, { target := 694, numerator := 62448574369468188305915904 }, { target := 695, numerator := 1644479125062662292055785472 }, { target := 696, numerator := 1644479125062662292055785472 }, { target := 697, numerator := 62448574369468188305915904 }, { target := 714, numerator := 60805190833429551771549696 }, { target := 715, numerator := 912077862501443276573245440 }, { target := 716, numerator := 1601203358613644863317475328 }, { target := 717, numerator := 60805190833429551771549696 }, { target := 718, numerator := 1013419847223825862859161600 }, { target := 719, numerator := 60805190833429551771549696 }, { target := 720, numerator := 1601203358613644863317475328 }, { target := 721, numerator := 1591069160141406604688883712 }, { target := 722, numerator := 1013419847223825862859161600 }, { target := 723, numerator := 24555162898233300657077485568 }, { target := 724, numerator := 1570800763196930087431700480 }, { target := 725, numerator := 912077862501443276573245440 }, { target := 726, numerator := 1601203358613644863317475328 }, { target := 727, numerator := 60805190833429551771549696 }, { target := 728, numerator := 1570800763196930087431700480 }, { target := 729, numerator := 60805190833429551771549696 }, { target := 730, numerator := 1601203358613644863317475328 }, { target := 731, numerator := 1601203358613644863317475328 }, { target := 732, numerator := 60805190833429551771549696 }, { target := 775, numerator := 60805190833429551771549696 }, { target := 776, numerator := 912077862501443276573245440 }, { target := 777, numerator := 1601203358613644863317475328 }, { target := 778, numerator := 60805190833429551771549696 }, { target := 779, numerator := 1013419847223825862859161600 }, { target := 780, numerator := 60805190833429551771549696 }, { target := 781, numerator := 1601203358613644863317475328 }, { target := 782, numerator := 1591069160141406604688883712 }, { target := 783, numerator := 1013419847223825862859161600 }, { target := 784, numerator := 24555162898233300657077485568 }, { target := 785, numerator := 1570800763196930087431700480 }, { target := 786, numerator := 912077862501443276573245440 }, { target := 787, numerator := 1601203358613644863317475328 }, { target := 788, numerator := 60805190833429551771549696 }, { target := 789, numerator := 1570800763196930087431700480 }, { target := 790, numerator := 60805190833429551771549696 }, { target := 791, numerator := 1601203358613644863317475328 }, { target := 792, numerator := 1601203358613644863317475328 }, { target := 793, numerator := 60805190833429551771549696 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 810, numerator := 1911255052412934289467899904 }, { target := 811, numerator := 28668825786194014342018498560 }, { target := 812, numerator := 50329716380207269622654697472 }, { target := 813, numerator := 1911255052412934289467899904 }, { target := 814, numerator := 31854250873548904824464998400 }, { target := 815, numerator := 1911255052412934289467899904 }, { target := 816, numerator := 50329716380207269622654697472 }, { target := 817, numerator := 50011173871471780574410047488 }, { target := 818, numerator := 31854250873548904824464998400 }, { target := 819, numerator := 771828498666089963896786911232 }, { target := 820, numerator := 49374088854000802477920747520 }, { target := 821, numerator := 28668825786194014342018498560 }, { target := 822, numerator := 50329716380207269622654697472 }, { target := 823, numerator := 1911255052412934289467899904 }, { target := 824, numerator := 49374088854000802477920747520 }, { target := 825, numerator := 1911255052412934289467899904 }, { target := 826, numerator := 50329716380207269622654697472 }, { target := 827, numerator := 50329716380207269622654697472 }, { target := 828, numerator := 1911255052412934289467899904 }, { target := 845, numerator := 60805190833429551771549696 }, { target := 846, numerator := 912077862501443276573245440 }, { target := 847, numerator := 1601203358613644863317475328 }, { target := 848, numerator := 60805190833429551771549696 }, { target := 849, numerator := 1013419847223825862859161600 }, { target := 850, numerator := 60805190833429551771549696 }, { target := 851, numerator := 1601203358613644863317475328 }, { target := 852, numerator := 1591069160141406604688883712 }, { target := 853, numerator := 1013419847223825862859161600 }, { target := 854, numerator := 24555162898233300657077485568 }, { target := 855, numerator := 1570800763196930087431700480 }, { target := 856, numerator := 912077862501443276573245440 }, { target := 857, numerator := 1601203358613644863317475328 }, { target := 858, numerator := 60805190833429551771549696 }, { target := 859, numerator := 1570800763196930087431700480 }, { target := 860, numerator := 60805190833429551771549696 }, { target := 861, numerator := 1601203358613644863317475328 }, { target := 862, numerator := 1601203358613644863317475328 }, { target := 863, numerator := 60805190833429551771549696 }, { target := 906, numerator := 77239026193815917115211776 }, { target := 907, numerator := 1158585392907238756728176640 }, { target := 908, numerator := 2033961023103819150700576768 }, { target := 909, numerator := 77239026193815917115211776 }, { target := 910, numerator := 1287317103230265285253529600 }, { target := 911, numerator := 77239026193815917115211776 }, { target := 912, numerator := 2033961023103819150700576768 }, { target := 913, numerator := 2021087852071516497848041472 }, { target := 914, numerator := 1287317103230265285253529600 }, { target := 915, numerator := 31191693411269327861693022208 }, { target := 916, numerator := 1995341510006911192142970880 }, { target := 917, numerator := 1158585392907238756728176640 }, { target := 918, numerator := 2033961023103819150700576768 }, { target := 919, numerator := 77239026193815917115211776 }, { target := 920, numerator := 1995341510006911192142970880 }, { target := 921, numerator := 77239026193815917115211776 }, { target := 922, numerator := 2033961023103819150700576768 }, { target := 923, numerator := 2033961023103819150700576768 }, { target := 924, numerator := 77239026193815917115211776 }]

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
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 217335633731309833749004288 }, { target := 252, numerator := 8477259897413535832293244928 }, { target := 255, numerator := 8477256787984237907626950656 }, { target := 262, numerator := 217336670207742475304435712 }, { target := 466, numerator := 5328228439864370117717524480 }, { target := 468, numerator := 207829597484977007501382778880 }, { target := 471, numerator := 207829521253807122896660725760 }, { target := 478, numerator := 5328253850254331652624875520 }, { target := 562, numerator := 3940084714741810534417432576 }, { target := 564, numerator := 153684518140206681862864633856 }, { target := 567, numerator := 153684461769262635615688589312 }, { target := 574, numerator := 3940103505056492616809447424 }, { target := 597, numerator := 4395788462888105347116957696 }, { target := 599, numerator := 171459417925106031188640792576 }, { target := 602, numerator := 171459355034390876389745098752 }, { target := 609, numerator := 4395809426459823613415522304 }, { target := 613, numerator := 28421677821727467813650563072 }, { target := 616, numerator := 102231929923089975810526806016 }, { target := 618, numerator := 28421687303353921700360093696 }, { target := 733, numerator := 217335633731309833749004288 }, { target := 735, numerator := 8477259897413535832293244928 }, { target := 738, numerator := 8477256787984237907626950656 }, { target := 745, numerator := 217336670207742475304435712 }, { target := 829, numerator := 4388777635993546965383118848 }, { target := 831, numerator := 171185957928415271968244236288 }, { target := 834, numerator := 171185895138004288070144229376 }, { target := 841, numerator := 4388798566130541598083121152 }, { target := 864, numerator := 4465896731833689164455346176 }, { target := 866, numerator := 174194017892013623392606355456 }, { target := 869, numerator := 174193953998256759585753792512 }, { target := 876, numerator := 4465918029752643766739533824 }, { target := 925, numerator := 217335633731309833749004288 }, { target := 927, numerator := 8477259897413535832293244928 }, { target := 930, numerator := 8477256787984237907626950656 }, { target := 937, numerator := 217336670207742475304435712 }, { target := 941, numerator := 78882409729854553649577984 }, { target := 942, numerator := 1183236145947818304743669760 }, { target := 943, numerator := 2077236789552836579438886912 }, { target := 944, numerator := 78882409729854553649577984 }, { target := 945, numerator := 1314706828830909227492966400 }, { target := 946, numerator := 78882409729854553649577984 }, { target := 947, numerator := 2077236789552836579438886912 }, { target := 948, numerator := 2064089721264527487163957248 }, { target := 949, numerator := 1314706828830909227492966400 }, { target := 950, numerator := 31855346462572930582154575872 }, { target := 951, numerator := 2037795584687909302614097920 }, { target := 952, numerator := 1183236145947818304743669760 }, { target := 953, numerator := 2077236789552836579438886912 }, { target := 954, numerator := 78882409729854553649577984 }, { target := 955, numerator := 2037795584687909302614097920 }, { target := 956, numerator := 78882409729854553649577984 }, { target := 957, numerator := 2077236789552836579438886912 }, { target := 958, numerator := 2077236789552836579438886912 }, { target := 959, numerator := 78882409729854553649577984 }, { target := 960, numerator := 5328228439864370117717524480 }, { target := 962, numerator := 207829597484977007501382778880 }, { target := 965, numerator := 207829521253807122896660725760 }, { target := 972, numerator := 5328253850254331652624875520 }, { target := 986, numerator := 217335633731309833749004288 }, { target := 988, numerator := 8477259897413535832293244928 }, { target := 991, numerator := 8477256787984237907626950656 }, { target := 998, numerator := 217336670207742475304435712 }]

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
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 111857772542529600699236352 }, { target := 35, numerator := 83893329406897200524427264 }, { target := 36, numerator := 88554069929502600553562112 }, { target := 37, numerator := 114188142803832300713803776 }, { target := 38, numerator := 1528722891414571209556230144 }, { target := 39, numerator := 2672934689714196916708835328 }, { target := 40, numerator := 81562959145594500509859840 }, { target := 41, numerator := 1528722891414571209556230144 }, { target := 42, numerator := 86223699668199900538994688 }, { target := 43, numerator := 88554069929502600553562112 }, { target := 44, numerator := 88554069929502600553562112 }, { target := 45, numerator := 86223699668199900538994688 }, { target := 46, numerator := 2672934689714196916708835328 }, { target := 47, numerator := 86223699668199900538994688 }, { target := 48, numerator := 111857772542529600699236352 }, { target := 49, numerator := 114188142803832300713803776 }, { target := 79, numerator := 18331334601956558125651722240 }, { target := 80, numerator := 13748500951467418594238791680 }, { target := 81, numerator := 14512306559882275182807613440 }, { target := 82, numerator := 18713237406163986419936133120 }, { target := 83, numerator := 250528239560072961050573537280 }, { target := 84, numerator := 438042516425920253544219279360 }, { target := 85, numerator := 13366598147259990299954380800 }, { target := 86, numerator := 250528239560072961050573537280 }, { target := 87, numerator := 14130403755674846888523202560 }, { target := 88, numerator := 14512306559882275182807613440 }, { target := 89, numerator := 14512306559882275182807613440 }, { target := 90, numerator := 14130403755674846888523202560 }, { target := 91, numerator := 438042516425920253544219279360 }, { target := 92, numerator := 14130403755674846888523202560 }, { target := 93, numerator := 18331334601956558125651722240 }, { target := 94, numerator := 18713237406163986419936133120 }, { target := 154, numerator := 188728187410762379647663472640 }, { target := 155, numerator := 141546140558071784735747604480 }, { target := 156, numerator := 149409815033520217221066915840 }, { target := 157, numerator := 192660024648486595890323128320 }, { target := 158, numerator := 2579285227947085855184734126080 }, { target := 159, numerator := 4509817311669676030330625064960 }, { target := 160, numerator := 137614303320347568493087948800 }, { target := 161, numerator := 2579285227947085855184734126080 }, { target := 162, numerator := 145477977795796000978407260160 }, { target := 163, numerator := 149409815033520217221066915840 }, { target := 164, numerator := 149409815033520217221066915840 }, { target := 165, numerator := 145477977795796000978407260160 }, { target := 166, numerator := 4509817311669676030330625064960 }, { target := 167, numerator := 145477977795796000978407260160 }, { target := 168, numerator := 188728187410762379647663472640 }, { target := 169, numerator := 192660024648486595890323128320 }, { target := 880, numerator := 28338735182169897382287769600 }, { target := 883, numerator := 101933587715143215180729548800 }, { target := 885, numerator := 28338744636126235158432972800 }, { target := 976, numerator := 28145202356535566375774584832 }, { target := 979, numerator := 101237455896600773711202615296 }, { target := 981, numerator := 28145211745928299893936357376 }, { target := 1002, numerator := 28338735182169897382287769600 }, { target := 1005, numerator := 101933587715143215180729548800 }, { target := 1007, numerator := 28338744636126235158432972800 }, { target := 1012, numerator := 118842257938495954999251566592 }, { target := 1014, numerator := 118842229604297057781380284416 }]

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
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 76130479993906640965337088 }, { target := 122, numerator := 8998133959824551164602482688 }, { target := 124, numerator := 85390497620928130222462599168 }, { target := 132, numerator := 8998140131231813965075972096 }, { target := 139, numerator := 76130479993906640965337088 }, { target := 196, numerator := 15099326438969218603312742400 }, { target := 197, numerator := 1784643443885288879336875622400 }, { target := 199, numerator := 16935910537640309913861645926400 }, { target := 207, numerator := 1784644667890350404078980300800 }, { target := 214, numerator := 15099326438969218603312742400 }, { target := 250, numerator := 1881892861390768967988019200 }, { target := 252, numerator := 73647801948453237017448284160 }, { target := 255, numerator := 73647801948453237017448284160 }, { target := 262, numerator := 1881892861390768967988019200 }, { target := 492, numerator := 18331334601956558125651722240 }, { target := 493, numerator := 13748500951467418594238791680 }, { target := 494, numerator := 14512306559882275182807613440 }, { target := 495, numerator := 18713237406163986419936133120 }, { target := 496, numerator := 250528239560072961050573537280 }, { target := 497, numerator := 438042516425920253544219279360 }, { target := 498, numerator := 13366598147259990299954380800 }, { target := 499, numerator := 250528239560072961050573537280 }, { target := 500, numerator := 14130403755674846888523202560 }, { target := 501, numerator := 14512306559882275182807613440 }, { target := 502, numerator := 14512306559882275182807613440 }, { target := 503, numerator := 14130403755674846888523202560 }, { target := 504, numerator := 438042516425920253544219279360 }, { target := 505, numerator := 14130403755674846888523202560 }, { target := 506, numerator := 18331334601956558125651722240 }, { target := 507, numerator := 18713237406163986419936133120 }, { target := 508, numerator := 15099326438969218603312742400 }, { target := 509, numerator := 1784643443885288879336875622400 }, { target := 511, numerator := 16935910537640309913861645926400 }, { target := 519, numerator := 1784644667890350404078980300800 }, { target := 526, numerator := 15099326438969218603312742400 }, { target := 562, numerator := 85058133718709117123769139200 }, { target := 564, numerator := 3328746664988687895351168860160 }, { target := 567, numerator := 3328746664988687895351168860160 }, { target := 574, numerator := 85058133718709117123769139200 }, { target := 890, numerator := 111857772542529600699236352 }, { target := 891, numerator := 83893329406897200524427264 }, { target := 892, numerator := 88554069929502600553562112 }, { target := 893, numerator := 114188142803832300713803776 }, { target := 894, numerator := 1528722891414571209556230144 }, { target := 895, numerator := 2672934689714196916708835328 }, { target := 896, numerator := 81562959145594500509859840 }, { target := 897, numerator := 1528722891414571209556230144 }, { target := 898, numerator := 86223699668199900538994688 }, { target := 899, numerator := 88554069929502600553562112 }, { target := 900, numerator := 88554069929502600553562112 }, { target := 901, numerator := 86223699668199900538994688 }, { target := 902, numerator := 2672934689714196916708835328 }, { target := 903, numerator := 86223699668199900538994688 }, { target := 904, numerator := 111857772542529600699236352 }, { target := 905, numerator := 114188142803832300713803776 }, { target := 906, numerator := 76130479993906640965337088 }, { target := 907, numerator := 8998133959824551164602482688 }, { target := 909, numerator := 85390497620928130222462599168 }, { target := 917, numerator := 8998140131231813965075972096 }, { target := 924, numerator := 76130479993906640965337088 }, { target := 925, numerator := 1891937092512723058556928000 }, { target := 927, numerator := 74040882532141450190546534400 }, { target := 930, numerator := 74040882532141450190546534400 }, { target := 937, numerator := 1891937092512723058556928000 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 537834340124231962070089728 }, { target := 11, numerator := 13029470626880587210149593088 }, { target := 12, numerator := 9871862565506064077996163072 }, { target := 13, numerator := 10999579730282679482336673792 }, { target := 14, numerator := 537834340124231962070089728 }, { target := 15, numerator := 10999579730282679482336673792 }, { target := 16, numerator := 10982230235439962322269896704 }, { target := 17, numerator := 537834340124231962070089728 }, { target := 18, numerator := 13029470626880587210149593088 }, { target := 19, numerator := 537834340124231962070089728 }, { target := 34, numerator := 42080025703190061666795520 }, { target := 35, numerator := 7380441164741660892316303360 }, { target := 40, numerator := 7380442049575138680866078720 }, { target := 48, numerator := 42079140869712273117020160 }, { target := 55, numerator := 21048737374952191734036037632 }, { target := 56, numerator := 509922637696422451363260137472 }, { target := 57, numerator := 386346179559606357956984045568 }, { target := 58, numerator := 430480628894183534173511221248 }, { target := 59, numerator := 21048737374952191734036037632 }, { target := 60, numerator := 430480628894183534173511221248 }, { target := 61, numerator := 429801637365959269924026187776 }, { target := 62, numerator := 21048737374952191734036037632 }, { target := 63, numerator := 509922637696422451363260137472 }, { target := 64, numerator := 21048737374952191734036037632 }, { target := 79, numerator := 13554875075663023893318205440 }, { target := 80, numerator := 2377397739654186368113752145920 }, { target := 85, numerator := 2377398024677948919641895075840 }, { target := 93, numerator := 13554590051900472365175275520 }, { target := 144, numerator := 21048745094914586581483388928 }, { target := 145, numerator := 509922824718737242667549196288 }, { target := 146, numerator := 386346321258270960156904783872 }, { target := 147, numerator := 430480786779866061053563502592 }, { target := 148, numerator := 21048745094914586581483388928 }, { target := 149, numerator := 430480786779866061053563502592 }, { target := 150, numerator := 429801795002610751808999522304 }, { target := 151, numerator := 21048745094914586581483388928 }, { target := 152, numerator := 509922824718737242667549196288 }, { target := 153, numerator := 21048745094914586581483388928 }, { target := 154, numerator := 144161796638983285895103250432 }, { target := 155, numerator := 25284624724381020161041210802176 }, { target := 160, numerator := 25284627755728595470318202519552 }, { target := 168, numerator := 144158765291407976618111533056 }, { target := 482, numerator := 537842060086626809517441024 }, { target := 483, numerator := 13029657649195378514438651904 }, { target := 484, numerator := 9872004264170666277916901376 }, { target := 485, numerator := 10999737615965206362388955136 }, { target := 486, numerator := 537842060086626809517441024 }, { target := 487, numerator := 10999737615965206362388955136 }, { target := 488, numerator := 10982387872091444207243231232 }, { target := 489, numerator := 537842060086626809517441024 }, { target := 490, numerator := 13029657649195378514438651904 }, { target := 491, numerator := 537842060086626809517441024 }, { target := 613, numerator := 48525087640611049052466839552 }, { target := 616, numerator := 180258607997405530515067371520 }, { target := 618, numerator := 48514873161908602009869615104 }, { target := 880, numerator := 48525087640611049052466839552 }, { target := 883, numerator := 180258607997405530515067371520 }, { target := 885, numerator := 48514873161908602009869615104 }, { target := 976, numerator := 48525087640611049052466839552 }, { target := 979, numerator := 180258607997405530515067371520 }, { target := 981, numerator := 48514873161908602009869615104 }, { target := 1002, numerator := 48525087640611049052466839552 }, { target := 1005, numerator := 180258607997405530515067371520 }, { target := 1007, numerator := 48514873161908602009869615104 }]

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
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 42245477966767479995760640 }, { target := 122, numerator := 13608170783693153738246062080 }, { target := 124, numerator := 144728618906240100911728820224 }, { target := 132, numerator := 13608211798720305939682951168 }, { target := 139, numerator := 42245477966767479995760640 }, { target := 196, numerator := 7409459937342217881407979520 }, { target := 197, numerator := 2386745306127269669692181053440 }, { target := 199, numerator := 25384040024739005823535475064832 }, { target := 207, numerator := 2386752499777694273787211546624 }, { target := 214, numerator := 7409459937342217881407979520 }, { target := 250, numerator := 515424575952388963650502656 }, { target := 252, numerator := 20171706650995850411784536064 }, { target := 255, numerator := 20171714049293145473921581056 }, { target := 262, numerator := 515431974249684025787547648 }, { target := 466, numerator := 12486576017427229409726693376 }, { target := 468, numerator := 488675861125738182556457631744 }, { target := 471, numerator := 488676040355456524223067979776 }, { target := 478, numerator := 12486755247145571076337041408 }, { target := 492, numerator := 13554915930056910485611085824 }, { target := 493, numerator := 2377404905131045340600055365632 }, { target := 498, numerator := 2377405190155666953757119217664 }, { target := 506, numerator := 13554630905435297328547233792 }, { target := 508, numerator := 7409460825654726382101463040 }, { target := 509, numerator := 2386745592271702322995663994880 }, { target := 511, numerator := 25384043068005378938746714456064 }, { target := 519, numerator := 2386752785922989366419335938048 }, { target := 526, numerator := 7409460825654726382101463040 }, { target := 562, numerator := 9460534958609978074746322944 }, { target := 564, numerator := 370248422077956093042109710336 }, { target := 567, numerator := 370248557872509670150367084544 }, { target := 574, numerator := 9460670753163555183003697152 }, { target := 597, numerator := 10541263908187567837239312384 }, { target := 599, numerator := 412543936023592553582948253696 }, { target := 602, numerator := 412544087330704975176331689984 }, { target := 609, numerator := 10541415215299989430622748672 }, { target := 733, numerator := 515424575952388963650502656 }, { target := 735, numerator := 20171706650995850411784536064 }, { target := 738, numerator := 20171714049293145473921581056 }, { target := 745, numerator := 515431974249684025787547648 }, { target := 829, numerator := 10541263908187567837239312384 }, { target := 831, numerator := 412543936023592553582948253696 }, { target := 834, numerator := 412544087330704975176331689984 }, { target := 841, numerator := 10541415215299989430622748672 }, { target := 864, numerator := 10524637308963297225508651008 }, { target := 866, numerator := 411893235809044300343858429952 }, { target := 869, numerator := 411893386877501970483624542208 }, { target := 876, numerator := 10524788377420967365274763264 }, { target := 890, numerator := 42080025703190061666795520 }, { target := 891, numerator := 7380441164741660892316303360 }, { target := 896, numerator := 7380442049575138680866078720 }, { target := 904, numerator := 42079140869712273117020160 }, { target := 906, numerator := 42244589654258979302277120 }, { target := 907, numerator := 13607884639260500434763120640 }, { target := 909, numerator := 144725575639866985700489428992 }, { target := 917, numerator := 13607925653425213307558559744 }, { target := 924, numerator := 42244589654258979302277120 }, { target := 925, numerator := 515424575952388963650502656 }, { target := 927, numerator := 20171706650995850411784536064 }, { target := 930, numerator := 20171714049293145473921581056 }, { target := 937, numerator := 515431974249684025787547648 }, { target := 960, numerator := 12486576017427229409726693376 }, { target := 962, numerator := 488675861125738182556457631744 }, { target := 965, numerator := 488676040355456524223067979776 }, { target := 972, numerator := 12486755247145571076337041408 }]

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
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 48525087640611049052466839552 }, { target := 2, numerator := 48525087640611049052466839552 }, { target := 3, numerator := 48525087640611049052466839552 }, { target := 4, numerator := 48525087640611049052466839552 }, { target := 10, numerator := 1881892861390768967988019200 }, { target := 12, numerator := 85058133718709117123769139200 }, { target := 17, numerator := 1891937092512723058556928000 }, { target := 34, numerator := 75107613660015380913979392 }, { target := 35, numerator := 14896456410038730061617561600 }, { target := 40, numerator := 14896456410038730061617561600 }, { target := 48, numerator := 75107613660015380913979392 }, { target := 51, numerator := 180258607997405530515067371520 }, { target := 52, numerator := 180258607997405530515067371520 }, { target := 53, numerator := 180258607997405530515067371520 }, { target := 54, numerator := 180258607997405530515067371520 }, { target := 55, numerator := 73647801948453237017448284160 }, { target := 57, numerator := 3328746664988687895351168860160 }, { target := 62, numerator := 74040882532141450190546534400 }, { target := 79, numerator := 8877237726199269287151009792 }, { target := 80, numerator := 1760665508938653520113539481600 }, { target := 85, numerator := 1760665508938653520113539481600 }, { target := 93, numerator := 8877237726199269287151009792 }, { target := 121, numerator := 113238732697375645152313344 }, { target := 122, numerator := 18557647374820219337079521280 }, { target := 124, numerator := 191058165033117470754424750080 }, { target := 132, numerator := 18557647374820219337079521280 }, { target := 139, numerator := 113238732697375645152313344 }, { target := 140, numerator := 48514873161908602009869615104 }, { target := 141, numerator := 48514873161908602009869615104 }, { target := 142, numerator := 48514873161908602009869615104 }, { target := 143, numerator := 48514873161908602009869615104 }, { target := 144, numerator := 73647801948453237017448284160 }, { target := 146, numerator := 3328746664988687895351168860160 }, { target := 151, numerator := 74040882532141450190546534400 }, { target := 154, numerator := 84243216462873433655174234112 }, { target := 155, numerator := 16708364714677772160700357017600 }, { target := 160, numerator := 16708364714677772160700357017600 }, { target := 168, numerator := 84243216462873433655174234112 }, { target := 196, numerator := 84929049523031733864235008 }, { target := 197, numerator := 13918235531115164502809640960 }, { target := 199, numerator := 143293623774838103065818562560 }, { target := 207, numerator := 13918235531115164502809640960 }, { target := 214, numerator := 84929049523031733864235008 }, { target := 231, numerator := 89647330052089052412248064 }, { target := 232, numerator := 14691470838399340308521287680 }, { target := 234, numerator := 151254380651217997680586260480 }, { target := 242, numerator := 14691470838399340308521287680 }, { target := 249, numerator := 89647330052089052412248064 }, { target := 482, numerator := 1881892861390768967988019200 }, { target := 484, numerator := 85058133718709117123769139200 }, { target := 489, numerator := 1891937092512723058556928000 }, { target := 492, numerator := 8877243814689351973222744064 }, { target := 493, numerator := 1760666716498349534926287667200 }, { target := 498, numerator := 1760666716498349534926287667200 }, { target := 506, numerator := 8877243814689351973222744064 }, { target := 890, numerator := 75107613660015380913979392 }, { target := 891, numerator := 14896456410038730061617561600 }, { target := 896, numerator := 14896456410038730061617561600 }, { target := 904, numerator := 75107613660015380913979392 }, { target := 986, numerator := 515424575952388963650502656 }, { target := 988, numerator := 20171706650995850411784536064 }, { target := 991, numerator := 20171714049293145473921581056 }, { target := 998, numerator := 515431974249684025787547648 }]

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
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 115597872961904304426319872 }, { target := 338, numerator := 18944265028462307239935344640 }, { target := 340, numerator := 195038543471307418061808599040 }, { target := 348, numerator := 18944265028462307239935344640 }, { target := 355, numerator := 115597872961904304426319872 }, { target := 412, numerator := 1547596013530800483748282368 }, { target := 413, numerator := 253621180789209664273420124160 }, { target := 415, numerator := 2611128255452605433643804917760 }, { target := 423, numerator := 253621180789209664273420124160 }, { target := 430, numerator := 1547596013530800483748282368 }, { target := 447, numerator := 2705933883414372187285487616 }, { target := 448, numerator := 443450448727474824575629393920 }, { target := 450, numerator := 4565494068603869561569274757120 }, { target := 458, numerator := 443450448727474824575629393920 }, { target := 465, numerator := 2705933883414372187285487616 }, { target := 508, numerator := 82569909258503074590228480 }, { target := 509, numerator := 13531617877473076599953817600 }, { target := 511, numerator := 139313245336648155758434713600 }, { target := 519, numerator := 13531617877473076599953817600 }, { target := 526, numerator := 82569909258503074590228480 }, { target := 543, numerator := 1547596013530800483748282368 }, { target := 544, numerator := 253621180789209664273420124160 }, { target := 546, numerator := 2611128255452605433643804917760 }, { target := 554, numerator := 253621180789209664273420124160 }, { target := 561, numerator := 1547596013530800483748282368 }, { target := 578, numerator := 87288189787560393138241536 }, { target := 579, numerator := 14304853184757252405665464320 }, { target := 581, numerator := 147274002213028050373202411520 }, { target := 589, numerator := 14304853184757252405665464320 }, { target := 596, numerator := 87288189787560393138241536 }, { target := 679, numerator := 89647330052089052412248064 }, { target := 680, numerator := 14691470838399340308521287680 }, { target := 682, numerator := 151254380651217997680586260480 }, { target := 690, numerator := 14691470838399340308521287680 }, { target := 697, numerator := 89647330052089052412248064 }, { target := 714, numerator := 89647330052089052412248064 }, { target := 715, numerator := 14691470838399340308521287680 }, { target := 717, numerator := 151254380651217997680586260480 }, { target := 725, numerator := 14691470838399340308521287680 }, { target := 732, numerator := 89647330052089052412248064 }, { target := 775, numerator := 87288189787560393138241536 }, { target := 776, numerator := 14304853184757252405665464320 }, { target := 778, numerator := 147274002213028050373202411520 }, { target := 786, numerator := 14304853184757252405665464320 }, { target := 793, numerator := 87288189787560393138241536 }, { target := 810, numerator := 2705933883414372187285487616 }, { target := 811, numerator := 443450448727474824575629393920 }, { target := 813, numerator := 4565494068603869561569274757120 }, { target := 821, numerator := 443450448727474824575629393920 }, { target := 828, numerator := 2705933883414372187285487616 }, { target := 845, numerator := 87288189787560393138241536 }, { target := 846, numerator := 14304853184757252405665464320 }, { target := 848, numerator := 147274002213028050373202411520 }, { target := 856, numerator := 14304853184757252405665464320 }, { target := 863, numerator := 87288189787560393138241536 }, { target := 906, numerator := 113238732697375645152313344 }, { target := 907, numerator := 18557647374820219337079521280 }, { target := 909, numerator := 191058165033117470754424750080 }, { target := 917, numerator := 18557647374820219337079521280 }, { target := 924, numerator := 113238732697375645152313344 }]

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
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 118842257938495954999251566592 }, { target := 1, numerator := 24868968094011534336944242688 }, { target := 2, numerator := 24796393284398660209501798400 }, { target := 3, numerator := 24627052061968620578802761728 }, { target := 4, numerator := 24796393284398660209501798400 }, { target := 10, numerator := 209841301533678460171452416 }, { target := 11, numerator := 5144496424696633217106575360 }, { target := 12, numerator := 3804219724578299826334072832 }, { target := 13, numerator := 4244209550374722404112924672 }, { target := 14, numerator := 209841301533678460171452416 }, { target := 15, numerator := 4237440476131700518300942336 }, { target := 16, numerator := 4311900292804941262232748032 }, { target := 17, numerator := 209841301533678460171452416 }, { target := 18, numerator := 5144496424696633217106575360 }, { target := 19, numerator := 209841301533678460171452416 }, { target := 50, numerator := 118842229604297057781380284416 }, { target := 51, numerator := 89452938682703728834210955264 }, { target := 52, numerator := 89191889250750313283138355200 }, { target := 53, numerator := 88582773909525676997302288384 }, { target := 54, numerator := 89191889250750313283138355200 }, { target := 55, numerator := 8184940590606172527731408896 }, { target := 56, numerator := 200663059640667455518576476160 }, { target := 57, numerator := 148385051997440934212421025792 }, { target := 58, numerator := 165547024203550650802825592832 }, { target := 59, numerator := 8184940590606172527731408896 }, { target := 60, numerator := 165282993861918193624511676416 }, { target := 61, numerator := 168187327619875222585964756992 }, { target := 62, numerator := 8184940590606172527731408896 }, { target := 63, numerator := 200663059640667455518576476160 }, { target := 64, numerator := 8184940590606172527731408896 }, { target := 140, numerator := 24868976390434681487815081984 }, { target := 141, numerator := 24796401556610455763628851200 }, { target := 142, numerator := 24627060277687262407194312704 }, { target := 143, numerator := 24796401556610455763628851200 }, { target := 144, numerator := 8184937588398574531501883392 }, { target := 145, numerator := 200662986038158601417465528320 }, { target := 146, numerator := 148384997570322544732388982784 }, { target := 147, numerator := 165546963481480846169409060864 }, { target := 148, numerator := 8184937588398574531501883392 }, { target := 149, numerator := 165282933236693795378070290432 }, { target := 150, numerator := 168187265929351354082796765184 }, { target := 151, numerator := 8184937588398574531501883392 }, { target := 152, numerator := 200662986038158601417465528320 }, { target := 153, numerator := 8184937588398574531501883392 }, { target := 482, numerator := 209842302269544458914627584 }, { target := 483, numerator := 5144520958866251250810224640 }, { target := 484, numerator := 3804237866951096319678087168 }, { target := 485, numerator := 4244229791064657281918435328 }, { target := 486, numerator := 209842302269544458914627584 }, { target := 487, numerator := 4237460684539833267114737664 }, { target := 488, numerator := 4311920856312897429955411968 }, { target := 489, numerator := 209842302269544458914627584 }, { target := 490, numerator := 5144520958866251250810224640 }, { target := 491, numerator := 209842302269544458914627584 }, { target := 941, numerator := 115597872961904304426319872 }, { target := 942, numerator := 18944265028462307239935344640 }, { target := 944, numerator := 195038543471307418061808599040 }, { target := 952, numerator := 18944265028462307239935344640 }, { target := 959, numerator := 115597872961904304426319872 }]

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
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 78570733541985157065474048 }, { target := 35, numerator := 58510120722754904197693440 }, { target := 36, numerator := 61853556192626613008990208 }, { target := 37, numerator := 80242451276921011471122432 }, { target := 38, numerator := 1074914503563754382831910912 }, { target := 39, numerator := 1944207725730398673769070592 }, { target := 40, numerator := 58510120722754904197693440 }, { target := 41, numerator := 1074914503563754382831910912 }, { target := 42, numerator := 63525273927562467414638592 }, { target := 43, numerator := 63525273927562467414638592 }, { target := 44, numerator := 61853556192626613008990208 }, { target := 45, numerator := 61853556192626613008990208 }, { target := 46, numerator := 1944207725730398673769070592 }, { target := 47, numerator := 61853556192626613008990208 }, { target := 48, numerator := 78570733541985157065474048 }, { target := 49, numerator := 80242451276921011471122432 }, { target := 79, numerator := 1178561003129777355982110720 }, { target := 80, numerator := 877651810841323562965401600 }, { target := 81, numerator := 927803342889399195134853120 }, { target := 82, numerator := 1203636769153815172066836480 }, { target := 83, numerator := 16123717553456315742478663680 }, { target := 84, numerator := 29163115885955980106536058880 }, { target := 85, numerator := 877651810841323562965401600 }, { target := 86, numerator := 16123717553456315742478663680 }, { target := 87, numerator := 952879108913437011219578880 }, { target := 88, numerator := 952879108913437011219578880 }, { target := 89, numerator := 927803342889399195134853120 }, { target := 90, numerator := 927803342889399195134853120 }, { target := 91, numerator := 29163115885955980106536058880 }, { target := 92, numerator := 927803342889399195134853120 }, { target := 93, numerator := 1178561003129777355982110720 }, { target := 94, numerator := 1203636769153815172066836480 }, { target := 105, numerator := 2069029316605609136057483264 }, { target := 106, numerator := 1540766512365879143872593920 }, { target := 107, numerator := 1628810313072500809236742144 }, { target := 108, numerator := 2113051216958919968739557376 }, { target := 109, numerator := 28306081927178865414573654016 }, { target := 110, numerator := 51197470110900498409252192256 }, { target := 111, numerator := 1540766512365879143872593920 }, { target := 112, numerator := 28306081927178865414573654016 }, { target := 113, numerator := 1672832213425811641918816256 }, { target := 114, numerator := 1672832213425811641918816256 }, { target := 115, numerator := 1628810313072500809236742144 }, { target := 116, numerator := 1628810313072500809236742144 }, { target := 117, numerator := 51197470110900498409252192256 }, { target := 118, numerator := 1628810313072500809236742144 }, { target := 119, numerator := 2069029316605609136057483264 }, { target := 120, numerator := 2113051216958919968739557376 }, { target := 154, numerator := 78570733541985157065474048 }, { target := 155, numerator := 58510120722754904197693440 }, { target := 156, numerator := 61853556192626613008990208 }, { target := 157, numerator := 80242451276921011471122432 }, { target := 158, numerator := 1074914503563754382831910912 }, { target := 159, numerator := 1944207725730398673769070592 }, { target := 160, numerator := 58510120722754904197693440 }, { target := 161, numerator := 1074914503563754382831910912 }, { target := 162, numerator := 63525273927562467414638592 }, { target := 163, numerator := 63525273927562467414638592 }, { target := 164, numerator := 61853556192626613008990208 }, { target := 165, numerator := 61853556192626613008990208 }, { target := 166, numerator := 1944207725730398673769070592 }, { target := 167, numerator := 61853556192626613008990208 }, { target := 168, numerator := 78570733541985157065474048 }, { target := 169, numerator := 80242451276921011471122432 }]

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
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 180, numerator := 1309512225699752617757900800 }, { target := 181, numerator := 975168678712581736628224000 }, { target := 182, numerator := 1030892603210443550149836800 }, { target := 183, numerator := 1337374187948683524518707200 }, { target := 184, numerator := 17915241726062573047198515200 }, { target := 185, numerator := 32403462095506644562817843200 }, { target := 186, numerator := 975168678712581736628224000 }, { target := 187, numerator := 17915241726062573047198515200 }, { target := 188, numerator := 1058754565459374456910643200 }, { target := 189, numerator := 1058754565459374456910643200 }, { target := 190, numerator := 1030892603210443550149836800 }, { target := 191, numerator := 1030892603210443550149836800 }, { target := 192, numerator := 32403462095506644562817843200 }, { target := 193, numerator := 1030892603210443550149836800 }, { target := 194, numerator := 1309512225699752617757900800 }, { target := 195, numerator := 1337374187948683524518707200 }, { target := 215, numerator := 78570733541985157065474048 }, { target := 216, numerator := 58510120722754904197693440 }, { target := 217, numerator := 61853556192626613008990208 }, { target := 218, numerator := 80242451276921011471122432 }, { target := 219, numerator := 1074914503563754382831910912 }, { target := 220, numerator := 1944207725730398673769070592 }, { target := 221, numerator := 58510120722754904197693440 }, { target := 222, numerator := 1074914503563754382831910912 }, { target := 223, numerator := 63525273927562467414638592 }, { target := 224, numerator := 63525273927562467414638592 }, { target := 225, numerator := 61853556192626613008990208 }, { target := 226, numerator := 61853556192626613008990208 }, { target := 227, numerator := 1944207725730398673769070592 }, { target := 228, numerator := 61853556192626613008990208 }, { target := 229, numerator := 78570733541985157065474048 }, { target := 230, numerator := 80242451276921011471122432 }, { target := 295, numerator := 2069029316605609136057483264 }, { target := 296, numerator := 1540766512365879143872593920 }, { target := 297, numerator := 1628810313072500809236742144 }, { target := 298, numerator := 2113051216958919968739557376 }, { target := 299, numerator := 28306081927178865414573654016 }, { target := 300, numerator := 51197470110900498409252192256 }, { target := 301, numerator := 1540766512365879143872593920 }, { target := 302, numerator := 28306081927178865414573654016 }, { target := 303, numerator := 1672832213425811641918816256 }, { target := 304, numerator := 1672832213425811641918816256 }, { target := 305, numerator := 1628810313072500809236742144 }, { target := 306, numerator := 1628810313072500809236742144 }, { target := 307, numerator := 51197470110900498409252192256 }, { target := 308, numerator := 1628810313072500809236742144 }, { target := 309, numerator := 2069029316605609136057483264 }, { target := 310, numerator := 2113051216958919968739557376 }, { target := 321, numerator := 2055934194348611609879904256 }, { target := 322, numerator := 1531014825578753326506311680 }, { target := 323, numerator := 1618501387040396373735243776 }, { target := 324, numerator := 2099677475079433133494370304 }, { target := 325, numerator := 28126929509918239684101668864 }, { target := 326, numerator := 50873435489945431963624013824 }, { target := 327, numerator := 1531014825578753326506311680 }, { target := 328, numerator := 28126929509918239684101668864 }, { target := 329, numerator := 1662244667771217897349709824 }, { target := 330, numerator := 1662244667771217897349709824 }, { target := 331, numerator := 1618501387040396373735243776 }, { target := 332, numerator := 1618501387040396373735243776 }, { target := 333, numerator := 50873435489945431963624013824 }, { target := 334, numerator := 1618501387040396373735243776 }, { target := 335, numerator := 2055934194348611609879904256 }, { target := 336, numerator := 2099677475079433133494370304 }]

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
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 370, numerator := 1309512225699752617757900800 }, { target := 371, numerator := 975168678712581736628224000 }, { target := 372, numerator := 1030892603210443550149836800 }, { target := 373, numerator := 1337374187948683524518707200 }, { target := 374, numerator := 17915241726062573047198515200 }, { target := 375, numerator := 32403462095506644562817843200 }, { target := 376, numerator := 975168678712581736628224000 }, { target := 377, numerator := 17915241726062573047198515200 }, { target := 378, numerator := 1058754565459374456910643200 }, { target := 379, numerator := 1058754565459374456910643200 }, { target := 380, numerator := 1030892603210443550149836800 }, { target := 381, numerator := 1030892603210443550149836800 }, { target := 382, numerator := 32403462095506644562817843200 }, { target := 383, numerator := 1030892603210443550149836800 }, { target := 384, numerator := 1309512225699752617757900800 }, { target := 385, numerator := 1337374187948683524518707200 }, { target := 396, numerator := 31729481228705005928273936384 }, { target := 397, numerator := 23628337085205855478501867520 }, { target := 398, numerator := 24978527775789047220130545664 }, { target := 399, numerator := 32404576573996601799088275456 }, { target := 400, numerator := 434086307022496144933620023296 }, { target := 401, numerator := 785135886574125997757076340736 }, { target := 402, numerator := 23628337085205855478501867520 }, { target := 403, numerator := 434086307022496144933620023296 }, { target := 404, numerator := 25653623121080643090944884736 }, { target := 405, numerator := 25653623121080643090944884736 }, { target := 406, numerator := 24978527775789047220130545664 }, { target := 407, numerator := 24978527775789047220130545664 }, { target := 408, numerator := 785135886574125997757076340736 }, { target := 409, numerator := 24978527775789047220130545664 }, { target := 410, numerator := 31729481228705005928273936384 }, { target := 411, numerator := 32404576573996601799088275456 }, { target := 431, numerator := 2029743949834616557524746240 }, { target := 432, numerator := 1511511452004501691773747200 }, { target := 433, numerator := 1597883534976187502732247040 }, { target := 434, numerator := 2072929991320459463003996160 }, { target := 435, numerator := 27768624675396988223157698560 }, { target := 436, numerator := 50225366248035299072367656960 }, { target := 437, numerator := 1511511452004501691773747200 }, { target := 438, numerator := 27768624675396988223157698560 }, { target := 439, numerator := 1641069576462030408211496960 }, { target := 440, numerator := 1641069576462030408211496960 }, { target := 441, numerator := 1597883534976187502732247040 }, { target := 442, numerator := 1597883534976187502732247040 }, { target := 443, numerator := 50225366248035299072367656960 }, { target := 444, numerator := 1597883534976187502732247040 }, { target := 445, numerator := 2029743949834616557524746240 }, { target := 446, numerator := 2072929991320459463003996160 }, { target := 492, numerator := 1178561003129777355982110720 }, { target := 493, numerator := 877651810841323562965401600 }, { target := 494, numerator := 927803342889399195134853120 }, { target := 495, numerator := 1203636769153815172066836480 }, { target := 496, numerator := 16123717553456315742478663680 }, { target := 497, numerator := 29163115885955980106536058880 }, { target := 498, numerator := 877651810841323562965401600 }, { target := 499, numerator := 16123717553456315742478663680 }, { target := 500, numerator := 952879108913437011219578880 }, { target := 501, numerator := 952879108913437011219578880 }, { target := 502, numerator := 927803342889399195134853120 }, { target := 503, numerator := 927803342889399195134853120 }, { target := 504, numerator := 29163115885955980106536058880 }, { target := 505, numerator := 927803342889399195134853120 }, { target := 506, numerator := 1178561003129777355982110720 }, { target := 507, numerator := 1203636769153815172066836480 }]

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
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 527, numerator := 2069029316605609136057483264 }, { target := 528, numerator := 1540766512365879143872593920 }, { target := 529, numerator := 1628810313072500809236742144 }, { target := 530, numerator := 2113051216958919968739557376 }, { target := 531, numerator := 28306081927178865414573654016 }, { target := 532, numerator := 51197470110900498409252192256 }, { target := 533, numerator := 1540766512365879143872593920 }, { target := 534, numerator := 28306081927178865414573654016 }, { target := 535, numerator := 1672832213425811641918816256 }, { target := 536, numerator := 1672832213425811641918816256 }, { target := 537, numerator := 1628810313072500809236742144 }, { target := 538, numerator := 1628810313072500809236742144 }, { target := 539, numerator := 51197470110900498409252192256 }, { target := 540, numerator := 1628810313072500809236742144 }, { target := 541, numerator := 2069029316605609136057483264 }, { target := 542, numerator := 2113051216958919968739557376 }, { target := 637, numerator := 78570733541985157065474048 }, { target := 638, numerator := 58510120722754904197693440 }, { target := 639, numerator := 61853556192626613008990208 }, { target := 640, numerator := 80242451276921011471122432 }, { target := 641, numerator := 1074914503563754382831910912 }, { target := 642, numerator := 1944207725730398673769070592 }, { target := 643, numerator := 58510120722754904197693440 }, { target := 644, numerator := 1074914503563754382831910912 }, { target := 645, numerator := 63525273927562467414638592 }, { target := 646, numerator := 63525273927562467414638592 }, { target := 647, numerator := 61853556192626613008990208 }, { target := 648, numerator := 61853556192626613008990208 }, { target := 649, numerator := 1944207725730398673769070592 }, { target := 650, numerator := 61853556192626613008990208 }, { target := 651, numerator := 78570733541985157065474048 }, { target := 652, numerator := 80242451276921011471122432 }, { target := 663, numerator := 2029743949834616557524746240 }, { target := 664, numerator := 1511511452004501691773747200 }, { target := 665, numerator := 1597883534976187502732247040 }, { target := 666, numerator := 2072929991320459463003996160 }, { target := 667, numerator := 27768624675396988223157698560 }, { target := 668, numerator := 50225366248035299072367656960 }, { target := 669, numerator := 1511511452004501691773747200 }, { target := 670, numerator := 27768624675396988223157698560 }, { target := 671, numerator := 1641069576462030408211496960 }, { target := 672, numerator := 1641069576462030408211496960 }, { target := 673, numerator := 1597883534976187502732247040 }, { target := 674, numerator := 1597883534976187502732247040 }, { target := 675, numerator := 50225366248035299072367656960 }, { target := 676, numerator := 1597883534976187502732247040 }, { target := 677, numerator := 2029743949834616557524746240 }, { target := 678, numerator := 2072929991320459463003996160 }, { target := 698, numerator := 78570733541985157065474048 }, { target := 699, numerator := 58510120722754904197693440 }, { target := 700, numerator := 61853556192626613008990208 }, { target := 701, numerator := 80242451276921011471122432 }, { target := 702, numerator := 1074914503563754382831910912 }, { target := 703, numerator := 1944207725730398673769070592 }, { target := 704, numerator := 58510120722754904197693440 }, { target := 705, numerator := 1074914503563754382831910912 }, { target := 706, numerator := 63525273927562467414638592 }, { target := 707, numerator := 63525273927562467414638592 }, { target := 708, numerator := 61853556192626613008990208 }, { target := 709, numerator := 61853556192626613008990208 }, { target := 710, numerator := 1944207725730398673769070592 }, { target := 711, numerator := 61853556192626613008990208 }, { target := 712, numerator := 78570733541985157065474048 }, { target := 713, numerator := 80242451276921011471122432 }]

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
    Slot19.Left16.expected,
    Slot19.Left17.expected,
    Slot19.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 759, numerator := 2069029316605609136057483264 }, { target := 760, numerator := 1540766512365879143872593920 }, { target := 761, numerator := 1628810313072500809236742144 }, { target := 762, numerator := 2113051216958919968739557376 }, { target := 763, numerator := 28306081927178865414573654016 }, { target := 764, numerator := 51197470110900498409252192256 }, { target := 765, numerator := 1540766512365879143872593920 }, { target := 766, numerator := 28306081927178865414573654016 }, { target := 767, numerator := 1672832213425811641918816256 }, { target := 768, numerator := 1672832213425811641918816256 }, { target := 769, numerator := 1628810313072500809236742144 }, { target := 770, numerator := 1628810313072500809236742144 }, { target := 771, numerator := 51197470110900498409252192256 }, { target := 772, numerator := 1628810313072500809236742144 }, { target := 773, numerator := 2069029316605609136057483264 }, { target := 774, numerator := 2113051216958919968739557376 }, { target := 794, numerator := 2069029316605609136057483264 }, { target := 795, numerator := 1540766512365879143872593920 }, { target := 796, numerator := 1628810313072500809236742144 }, { target := 797, numerator := 2113051216958919968739557376 }, { target := 798, numerator := 28306081927178865414573654016 }, { target := 799, numerator := 51197470110900498409252192256 }, { target := 800, numerator := 1540766512365879143872593920 }, { target := 801, numerator := 28306081927178865414573654016 }, { target := 802, numerator := 1672832213425811641918816256 }, { target := 803, numerator := 1672832213425811641918816256 }, { target := 804, numerator := 1628810313072500809236742144 }, { target := 805, numerator := 1628810313072500809236742144 }, { target := 806, numerator := 51197470110900498409252192256 }, { target := 807, numerator := 1628810313072500809236742144 }, { target := 808, numerator := 2069029316605609136057483264 }, { target := 809, numerator := 2113051216958919968739557376 }, { target := 890, numerator := 78570733541985157065474048 }, { target := 891, numerator := 58510120722754904197693440 }, { target := 892, numerator := 61853556192626613008990208 }, { target := 893, numerator := 80242451276921011471122432 }, { target := 894, numerator := 1074914503563754382831910912 }, { target := 895, numerator := 1944207725730398673769070592 }, { target := 896, numerator := 58510120722754904197693440 }, { target := 897, numerator := 1074914503563754382831910912 }, { target := 898, numerator := 63525273927562467414638592 }, { target := 899, numerator := 63525273927562467414638592 }, { target := 900, numerator := 61853556192626613008990208 }, { target := 901, numerator := 61853556192626613008990208 }, { target := 902, numerator := 1944207725730398673769070592 }, { target := 903, numerator := 61853556192626613008990208 }, { target := 904, numerator := 78570733541985157065474048 }, { target := 905, numerator := 80242451276921011471122432 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1
