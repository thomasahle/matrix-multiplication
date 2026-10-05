import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 58, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 77239026193815917115211776 }, some { target := 122, numerator := 1158585392907238756728176640 }, some { target := 123, numerator := 2033961023103819150700576768 }, some { target := 124, numerator := 77239026193815917115211776 }, some { target := 125, numerator := 1287317103230265285253529600 }, some { target := 126, numerator := 77239026193815917115211776 }, some { target := 127, numerator := 2033961023103819150700576768 }, some { target := 128, numerator := 2021087852071516497848041472 }, some { target := 129, numerator := 1287317103230265285253529600 }, some { target := 130, numerator := 31191693411269327861693022208 }, some { target := 131, numerator := 1995341510006911192142970880 }, some { target := 132, numerator := 1158585392907238756728176640 }, some { target := 133, numerator := 2033961023103819150700576768 }, some { target := 134, numerator := 77239026193815917115211776 }, some { target := 135, numerator := 1995341510006911192142970880 }, some { target := 136, numerator := 77239026193815917115211776 }, some { target := 137, numerator := 2033961023103819150700576768 }, some { target := 138, numerator := 2033961023103819150700576768 }, some { target := 139, numerator := 77239026193815917115211776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 57518423761352278702817280 }, some { target := 197, numerator := 862776356420284180542259200 }, some { target := 198, numerator := 1514651825715610005840855040 }, some { target := 199, numerator := 57518423761352278702817280 }, some { target := 200, numerator := 958640396022537978380288000 }, some { target := 201, numerator := 57518423761352278702817280 }, some { target := 202, numerator := 1514651825715610005840855040 }, some { target := 203, numerator := 1505065421755384626057052160 }, some { target := 204, numerator := 958640396022537978380288000 }, some { target := 205, numerator := 23227856795626095216154378240 }, some { target := 206, numerator := 1485892613834933866489446400 }, some { target := 207, numerator := 862776356420284180542259200 }, some { target := 208, numerator := 1514651825715610005840855040 }, some { target := 209, numerator := 57518423761352278702817280 }, some { target := 210, numerator := 1485892613834933866489446400 }, some { target := 211, numerator := 57518423761352278702817280 }, some { target := 212, numerator := 1514651825715610005840855040 }, some { target := 213, numerator := 1514651825715610005840855040 }, some { target := 214, numerator := 57518423761352278702817280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 60805190833429551771549696 }, some { target := 232, numerator := 912077862501443276573245440 }, some { target := 233, numerator := 1601203358613644863317475328 }, some { target := 234, numerator := 60805190833429551771549696 }, some { target := 235, numerator := 1013419847223825862859161600 }, some { target := 236, numerator := 60805190833429551771549696 }, some { target := 237, numerator := 1601203358613644863317475328 }, some { target := 238, numerator := 1591069160141406604688883712 }, some { target := 239, numerator := 1013419847223825862859161600 }, some { target := 240, numerator := 24555162898233300657077485568 }, some { target := 241, numerator := 1570800763196930087431700480 }, some { target := 242, numerator := 912077862501443276573245440 }, some { target := 243, numerator := 1601203358613644863317475328 }, some { target := 244, numerator := 60805190833429551771549696 }, some { target := 245, numerator := 1570800763196930087431700480 }, some { target := 246, numerator := 60805190833429551771549696 }, some { target := 247, numerator := 1601203358613644863317475328 }, some { target := 248, numerator := 1601203358613644863317475328 }, some { target := 249, numerator := 60805190833429551771549696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 78882409729854553649577984 }, some { target := 338, numerator := 1183236145947818304743669760 }, some { target := 339, numerator := 2077236789552836579438886912 }, some { target := 340, numerator := 78882409729854553649577984 }, some { target := 341, numerator := 1314706828830909227492966400 }, some { target := 342, numerator := 78882409729854553649577984 }, some { target := 343, numerator := 2077236789552836579438886912 }, some { target := 344, numerator := 2064089721264527487163957248 }, some { target := 345, numerator := 1314706828830909227492966400 }, some { target := 346, numerator := 31855346462572930582154575872 }, some { target := 347, numerator := 2037795584687909302614097920 }, some { target := 348, numerator := 1183236145947818304743669760 }, some { target := 349, numerator := 2077236789552836579438886912 }, some { target := 350, numerator := 78882409729854553649577984 }, some { target := 351, numerator := 2037795584687909302614097920 }, some { target := 352, numerator := 78882409729854553649577984 }, some { target := 353, numerator := 2077236789552836579438886912 }, some { target := 354, numerator := 2077236789552836579438886912 }, some { target := 355, numerator := 78882409729854553649577984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 1056695613672843291597471744 }, some { target := 413, numerator := 15850434205092649373962076160 }, some { target := 414, numerator := 27826317826718206678733422592 }, some { target := 415, numerator := 1056695613672843291597471744 }, some { target := 416, numerator := 17611593561214054859957862400 }, some { target := 417, numerator := 1056695613672843291597471744 }, some { target := 418, numerator := 27826317826718206678733422592 }, some { target := 419, numerator := 27650201891106066130133843968 }, some { target := 420, numerator := 17611593561214054859957862400 }, some { target := 421, numerator := 426728911988216549256779005952 }, some { target := 422, numerator := 27297970019881785032934686720 }, some { target := 423, numerator := 15850434205092649373962076160 }, some { target := 424, numerator := 27826317826718206678733422592 }, some { target := 425, numerator := 1056695613672843291597471744 }, some { target := 426, numerator := 27297970019881785032934686720 }, some { target := 427, numerator := 1056695613672843291597471744 }, some { target := 428, numerator := 27826317826718206678733422592 }, some { target := 429, numerator := 27826317826718206678733422592 }, some { target := 430, numerator := 1056695613672843291597471744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 1911255052412934289467899904 }, some { target := 448, numerator := 28668825786194014342018498560 }, some { target := 449, numerator := 50329716380207269622654697472 }, some { target := 450, numerator := 1911255052412934289467899904 }, some { target := 451, numerator := 31854250873548904824464998400 }, some { target := 452, numerator := 1911255052412934289467899904 }, some { target := 453, numerator := 50329716380207269622654697472 }, some { target := 454, numerator := 50011173871471780574410047488 }, some { target := 455, numerator := 31854250873548904824464998400 }, some { target := 456, numerator := 771828498666089963896786911232 }, some { target := 457, numerator := 49374088854000802477920747520 }, some { target := 458, numerator := 28668825786194014342018498560 }, some { target := 459, numerator := 50329716380207269622654697472 }, some { target := 460, numerator := 1911255052412934289467899904 }, some { target := 461, numerator := 49374088854000802477920747520 }, some { target := 462, numerator := 1911255052412934289467899904 }, some { target := 463, numerator := 50329716380207269622654697472 }, some { target := 464, numerator := 50329716380207269622654697472 }, some { target := 465, numerator := 1911255052412934289467899904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 57518423761352278702817280 }, some { target := 509, numerator := 862776356420284180542259200 }, some { target := 510, numerator := 1514651825715610005840855040 }, some { target := 511, numerator := 57518423761352278702817280 }, some { target := 512, numerator := 958640396022537978380288000 }, some { target := 513, numerator := 57518423761352278702817280 }, some { target := 514, numerator := 1514651825715610005840855040 }, some { target := 515, numerator := 1505065421755384626057052160 }, some { target := 516, numerator := 958640396022537978380288000 }, some { target := 517, numerator := 23227856795626095216154378240 }, some { target := 518, numerator := 1485892613834933866489446400 }, some { target := 519, numerator := 862776356420284180542259200 }, some { target := 520, numerator := 1514651825715610005840855040 }, some { target := 521, numerator := 57518423761352278702817280 }, some { target := 522, numerator := 1485892613834933866489446400 }, some { target := 523, numerator := 57518423761352278702817280 }, some { target := 524, numerator := 1514651825715610005840855040 }, some { target := 525, numerator := 1514651825715610005840855040 }, some { target := 526, numerator := 57518423761352278702817280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 1056695613672843291597471744 }, some { target := 544, numerator := 15850434205092649373962076160 }, some { target := 545, numerator := 27826317826718206678733422592 }, some { target := 546, numerator := 1056695613672843291597471744 }, some { target := 547, numerator := 17611593561214054859957862400 }, some { target := 548, numerator := 1056695613672843291597471744 }, some { target := 549, numerator := 27826317826718206678733422592 }, some { target := 550, numerator := 27650201891106066130133843968 }, some { target := 551, numerator := 17611593561214054859957862400 }, some { target := 552, numerator := 426728911988216549256779005952 }, some { target := 553, numerator := 27297970019881785032934686720 }, some { target := 554, numerator := 15850434205092649373962076160 }, some { target := 555, numerator := 27826317826718206678733422592 }, some { target := 556, numerator := 1056695613672843291597471744 }, some { target := 557, numerator := 27297970019881785032934686720 }, some { target := 558, numerator := 1056695613672843291597471744 }, some { target := 559, numerator := 27826317826718206678733422592 }, some { target := 560, numerator := 27826317826718206678733422592 }, some { target := 561, numerator := 1056695613672843291597471744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 62448574369468188305915904 }, some { target := 579, numerator := 936728615542022824588738560 }, some { target := 580, numerator := 1644479125062662292055785472 }, some { target := 581, numerator := 62448574369468188305915904 }, some { target := 582, numerator := 1040809572824469805098598400 }, some { target := 583, numerator := 62448574369468188305915904 }, some { target := 584, numerator := 1644479125062662292055785472 }, some { target := 585, numerator := 1634071029334417594004799488 }, some { target := 586, numerator := 1040809572824469805098598400 }, some { target := 587, numerator := 25218815949536903377539039232 }, some { target := 588, numerator := 1613254837877928197902827520 }, some { target := 589, numerator := 936728615542022824588738560 }, some { target := 590, numerator := 1644479125062662292055785472 }, some { target := 591, numerator := 62448574369468188305915904 }, some { target := 592, numerator := 1613254837877928197902827520 }, some { target := 593, numerator := 62448574369468188305915904 }, some { target := 594, numerator := 1644479125062662292055785472 }, some { target := 595, numerator := 1644479125062662292055785472 }, some { target := 596, numerator := 62448574369468188305915904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 62448574369468188305915904 }, some { target := 680, numerator := 936728615542022824588738560 }, some { target := 681, numerator := 1644479125062662292055785472 }, some { target := 682, numerator := 62448574369468188305915904 }, some { target := 683, numerator := 1040809572824469805098598400 }, some { target := 684, numerator := 62448574369468188305915904 }, some { target := 685, numerator := 1644479125062662292055785472 }, some { target := 686, numerator := 1634071029334417594004799488 }, some { target := 687, numerator := 1040809572824469805098598400 }, some { target := 688, numerator := 25218815949536903377539039232 }, some { target := 689, numerator := 1613254837877928197902827520 }, some { target := 690, numerator := 936728615542022824588738560 }, some { target := 691, numerator := 1644479125062662292055785472 }, some { target := 692, numerator := 62448574369468188305915904 }, some { target := 693, numerator := 1613254837877928197902827520 }, some { target := 694, numerator := 62448574369468188305915904 }, some { target := 695, numerator := 1644479125062662292055785472 }, some { target := 696, numerator := 1644479125062662292055785472 }, some { target := 697, numerator := 62448574369468188305915904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 60805190833429551771549696 }, some { target := 715, numerator := 912077862501443276573245440 }, some { target := 716, numerator := 1601203358613644863317475328 }, some { target := 717, numerator := 60805190833429551771549696 }, some { target := 718, numerator := 1013419847223825862859161600 }, some { target := 719, numerator := 60805190833429551771549696 }, some { target := 720, numerator := 1601203358613644863317475328 }, some { target := 721, numerator := 1591069160141406604688883712 }, some { target := 722, numerator := 1013419847223825862859161600 }, some { target := 723, numerator := 24555162898233300657077485568 }, some { target := 724, numerator := 1570800763196930087431700480 }, some { target := 725, numerator := 912077862501443276573245440 }, some { target := 726, numerator := 1601203358613644863317475328 }, some { target := 727, numerator := 60805190833429551771549696 }, some { target := 728, numerator := 1570800763196930087431700480 }, some { target := 729, numerator := 60805190833429551771549696 }, some { target := 730, numerator := 1601203358613644863317475328 }, some { target := 731, numerator := 1601203358613644863317475328 }, some { target := 732, numerator := 60805190833429551771549696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 60805190833429551771549696 }, some { target := 776, numerator := 912077862501443276573245440 }, some { target := 777, numerator := 1601203358613644863317475328 }, some { target := 778, numerator := 60805190833429551771549696 }, some { target := 779, numerator := 1013419847223825862859161600 }, some { target := 780, numerator := 60805190833429551771549696 }, some { target := 781, numerator := 1601203358613644863317475328 }, some { target := 782, numerator := 1591069160141406604688883712 }, some { target := 783, numerator := 1013419847223825862859161600 }, some { target := 784, numerator := 24555162898233300657077485568 }, some { target := 785, numerator := 1570800763196930087431700480 }, some { target := 786, numerator := 912077862501443276573245440 }, some { target := 787, numerator := 1601203358613644863317475328 }, some { target := 788, numerator := 60805190833429551771549696 }, some { target := 789, numerator := 1570800763196930087431700480 }, some { target := 790, numerator := 60805190833429551771549696 }, some { target := 791, numerator := 1601203358613644863317475328 }, some { target := 792, numerator := 1601203358613644863317475328 }, some { target := 793, numerator := 60805190833429551771549696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 1911255052412934289467899904 }, some { target := 811, numerator := 28668825786194014342018498560 }, some { target := 812, numerator := 50329716380207269622654697472 }, some { target := 813, numerator := 1911255052412934289467899904 }, some { target := 814, numerator := 31854250873548904824464998400 }, some { target := 815, numerator := 1911255052412934289467899904 }, some { target := 816, numerator := 50329716380207269622654697472 }, some { target := 817, numerator := 50011173871471780574410047488 }, some { target := 818, numerator := 31854250873548904824464998400 }, some { target := 819, numerator := 771828498666089963896786911232 }, some { target := 820, numerator := 49374088854000802477920747520 }, some { target := 821, numerator := 28668825786194014342018498560 }, some { target := 822, numerator := 50329716380207269622654697472 }, some { target := 823, numerator := 1911255052412934289467899904 }, some { target := 824, numerator := 49374088854000802477920747520 }, some { target := 825, numerator := 1911255052412934289467899904 }, some { target := 826, numerator := 50329716380207269622654697472 }, some { target := 827, numerator := 50329716380207269622654697472 }, some { target := 828, numerator := 1911255052412934289467899904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 60805190833429551771549696 }, some { target := 846, numerator := 912077862501443276573245440 }, some { target := 847, numerator := 1601203358613644863317475328 }, some { target := 848, numerator := 60805190833429551771549696 }, some { target := 849, numerator := 1013419847223825862859161600 }, some { target := 850, numerator := 60805190833429551771549696 }, some { target := 851, numerator := 1601203358613644863317475328 }, some { target := 852, numerator := 1591069160141406604688883712 }, some { target := 853, numerator := 1013419847223825862859161600 }, some { target := 854, numerator := 24555162898233300657077485568 }, some { target := 855, numerator := 1570800763196930087431700480 }, some { target := 856, numerator := 912077862501443276573245440 }, some { target := 857, numerator := 1601203358613644863317475328 }, some { target := 858, numerator := 60805190833429551771549696 }, some { target := 859, numerator := 1570800763196930087431700480 }, some { target := 860, numerator := 60805190833429551771549696 }, some { target := 861, numerator := 1601203358613644863317475328 }, some { target := 862, numerator := 1601203358613644863317475328 }, some { target := 863, numerator := 60805190833429551771549696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 77239026193815917115211776 }, some { target := 907, numerator := 1158585392907238756728176640 }, some { target := 908, numerator := 2033961023103819150700576768 }, some { target := 909, numerator := 77239026193815917115211776 }, some { target := 910, numerator := 1287317103230265285253529600 }, some { target := 911, numerator := 77239026193815917115211776 }, some { target := 912, numerator := 2033961023103819150700576768 }, some { target := 913, numerator := 2021087852071516497848041472 }, some { target := 914, numerator := 1287317103230265285253529600 }, some { target := 915, numerator := 31191693411269327861693022208 }, some { target := 916, numerator := 1995341510006911192142970880 }, some { target := 917, numerator := 1158585392907238756728176640 }, some { target := 918, numerator := 2033961023103819150700576768 }, some { target := 919, numerator := 77239026193815917115211776 }, some { target := 920, numerator := 1995341510006911192142970880 }, some { target := 921, numerator := 77239026193815917115211776 }, some { target := 922, numerator := 2033961023103819150700576768 }, some { target := 923, numerator := 2033961023103819150700576768 }, some { target := 924, numerator := 77239026193815917115211776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 78882409729854553649577984 }, some { target := 942, numerator := 1183236145947818304743669760 }, some { target := 943, numerator := 2077236789552836579438886912 }, some { target := 944, numerator := 78882409729854553649577984 }, some { target := 945, numerator := 1314706828830909227492966400 }, some { target := 946, numerator := 78882409729854553649577984 }, some { target := 947, numerator := 2077236789552836579438886912 }, some { target := 948, numerator := 2064089721264527487163957248 }, some { target := 949, numerator := 1314706828830909227492966400 }, some { target := 950, numerator := 31855346462572930582154575872 }, some { target := 951, numerator := 2037795584687909302614097920 }, some { target := 952, numerator := 1183236145947818304743669760 }, some { target := 953, numerator := 2077236789552836579438886912 }, some { target := 954, numerator := 78882409729854553649577984 }, some { target := 955, numerator := 2037795584687909302614097920 }, some { target := 956, numerator := 78882409729854553649577984 }, some { target := 957, numerator := 2077236789552836579438886912 }, some { target := 958, numerator := 2077236789552836579438886912 }, some { target := 959, numerator := 78882409729854553649577984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 29, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 250, numerator := 217335633731309833749004288 }, some { target := 252, numerator := 8477259897413535832293244928 }, some { target := 255, numerator := 8477256787984237907626950656 }, some { target := 262, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 5328228439864370117717524480 }, some { target := 468, numerator := 207829597484977007501382778880 }, some { target := 471, numerator := 207829521253807122896660725760 }, some { target := 478, numerator := 5328253850254331652624875520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 3940084714741810534417432576 }, some { target := 564, numerator := 153684518140206681862864633856 }, some { target := 567, numerator := 153684461769262635615688589312 }, some { target := 574, numerator := 3940103505056492616809447424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 4395788462888105347116957696 }, some { target := 599, numerator := 171459417925106031188640792576 }, some { target := 602, numerator := 171459355034390876389745098752 }, some { target := 609, numerator := 4395809426459823613415522304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 217335633731309833749004288 }, some { target := 735, numerator := 8477259897413535832293244928 }, some { target := 738, numerator := 8477256787984237907626950656 }, some { target := 745, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 4388777635993546965383118848 }, some { target := 831, numerator := 171185957928415271968244236288 }, some { target := 834, numerator := 171185895138004288070144229376 }, some { target := 841, numerator := 4388798566130541598083121152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 4465896731833689164455346176 }, some { target := 866, numerator := 174194017892013623392606355456 }, some { target := 869, numerator := 174193953998256759585753792512 }, some { target := 876, numerator := 4465918029752643766739533824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 217335633731309833749004288 }, some { target := 927, numerator := 8477259897413535832293244928 }, some { target := 930, numerator := 8477256787984237907626950656 }, some { target := 937, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 5328228439864370117717524480 }, some { target := 962, numerator := 207829597484977007501382778880 }, some { target := 965, numerator := 207829521253807122896660725760 }, some { target := 972, numerator := 5328253850254331652624875520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 217335633731309833749004288 }, some { target := 988, numerator := 8477259897413535832293244928 }, some { target := 991, numerator := 8477256787984237907626950656 }, some { target := 998, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 8, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 613, numerator := 28421677821727467813650563072 }, some { target := 616, numerator := 102231929923089975810526806016 }, some { target := 618, numerator := 28421687303353921700360093696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 880, numerator := 28338735182169897382287769600 }, some { target := 883, numerator := 101933587715143215180729548800 }, some { target := 885, numerator := 28338744636126235158432972800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 976, numerator := 28145202356535566375774584832 }, some { target := 979, numerator := 101237455896600773711202615296 }, some { target := 981, numerator := 28145211745928299893936357376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1002, numerator := 28338735182169897382287769600 }, some { target := 1005, numerator := 101933587715143215180729548800 }, some { target := 1007, numerator := 28338744636126235158432972800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1
