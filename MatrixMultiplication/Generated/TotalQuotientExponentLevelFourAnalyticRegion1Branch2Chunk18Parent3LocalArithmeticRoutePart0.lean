import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 77; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 8447818192895620586951147520 }, { target := 258, numerator := 364172789927958653586898944 }, { target := 259, numerator := 20459145501570710875668480 }, { target := 260, numerator := 30472257043869475010594734080 }, { target := 261, numerator := 553078900059128217338904576 }, { target := 262, numerator := 8447815391296364392312995840 }, { target := 263, numerator := 553078900059128217338904576 }, { target := 264, numerator := 553078900059128217338904576 }, { target := 265, numerator := 364172789927958653586898944 }, { target := 266, numerator := 20459145501570710875668480 }, { target := 353, numerator := 1720394034743495300701224960 }, { target := 354, numerator := 30623013818434216352481804288 }, { target := 355, numerator := 1720394034743495300701224960 }, { target := 356, numerator := 27239572216772008927769395200 }, { target := 357, numerator := 46507985405899156295623114752 }, { target := 358, numerator := 1720394034743495300701224960 }, { target := 359, numerator := 46507985405899156295623114752 }, { target := 360, numerator := 46507985405899156295623114752 }, { target := 361, numerator := 30623013818434216352481804288 }, { target := 362, numerator := 1720394034743495300701224960 }, { target := 389, numerator := 299813603264428035327131648 }, { target := 391, numerator := 299813603264428035327131648 }, { target := 656, numerator := 7176183665232438781055860736 }, { target := 658, numerator := 7176183665232438781055860736 }, { target := 695, numerator := 1720393619691753642236313600 }, { target := 696, numerator := 30623006430513214831806382080 }, { target := 697, numerator := 1720393619691753642236313600 }, { target := 698, numerator := 27239565645119432668741632000 }, { target := 699, numerator := 46507974185667073461788344320 }, { target := 700, numerator := 1720393619691753642236313600 }, { target := 701, numerator := 46507974185667073461788344320 }, { target := 702, numerator := 46507974185667073461788344320 }, { target := 703, numerator := 30623006430513214831806382080 }, { target := 704, numerator := 1720393619691753642236313600 }, { target := 731, numerator := 5367630639088953535695421440 }, { target := 733, numerator := 5367630639088953535695421440 }, { target := 745, numerator := 6228385822654569508086218752 }, { target := 747, numerator := 6228385822654569508086218752 }, { target := 872, numerator := 299813603264428035327131648 }, { target := 874, numerator := 299813603264428035327131648 }, { target := 947, numerator := 6218714416097652474688569344 }, { target := 949, numerator := 6218714416097652474688569344 }, { target := 961, numerator := 6247728635768403574881517568 }, { target := 963, numerator := 6247728635768403574881517568 }, { target := 982, numerator := 20459560553312369340579840 }, { target := 983, numerator := 364180177848960174262321152 }, { target := 984, numerator := 20459560553312369340579840 }, { target := 985, numerator := 323943042094112514559180800 }, { target := 986, numerator := 553090120291211051173675008 }, { target := 987, numerator := 20459560553312369340579840 }, { target := 988, numerator := 553090120291211051173675008 }, { target := 989, numerator := 553090120291211051173675008 }, { target := 990, numerator := 364180177848960174262321152 }, { target := 991, numerator := 20459560553312369340579840 }, { target := 992, numerator := 299813603264428035327131648 }, { target := 994, numerator := 299813603264428035327131648 }, { target := 1006, numerator := 7176183665232438781055860736 }, { target := 1008, numerator := 7176183665232438781055860736 }, { target := 1011, numerator := 299813603264428035327131648 }, { target := 1013, numerator := 299813603264428035327131648 }]

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
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 81156967061119236202037248 }, { target := 111, numerator := 96373898385079092989919232 }, { target := 112, numerator := 73548501399139307808096256 }, { target := 113, numerator := 758310410977332863262785536 }, { target := 114, numerator := 91301587943759140727291904 }, { target := 115, numerator := 73548501399139307808096256 }, { target := 116, numerator := 91301587943759140727291904 }, { target := 117, numerator := 91301587943759140727291904 }, { target := 118, numerator := 3910751350257683194485669888 }, { target := 119, numerator := 91301587943759140727291904 }, { target := 120, numerator := 758310410977332863262785536 }, { target := 121, numerator := 3910751350257683194485669888 }, { target := 122, numerator := 81156967061119236202037248 }, { target := 123, numerator := 91301587943759140727291904 }, { target := 124, numerator := 91301587943759140727291904 }, { target := 125, numerator := 96373898385079092989919232 }, { target := 353, numerator := 6554612592417594348058705920 }, { target := 356, numerator := 23448693779332841253938135040 }, { target := 358, numerator := 6554610413395950641117921280 }, { target := 379, numerator := 7490985819905822112067092480 }, { target := 382, numerator := 26798507176380390004500725760 }, { target := 384, numerator := 7490983329595372161277624320 }, { target := 524, numerator := 8801908338389340981678833664 }, { target := 527, numerator := 31488245932246958255288352768 }, { target := 529, numerator := 8801905412274562289501208576 }, { target := 620, numerator := 103937428251193281804930908160 }, { target := 623, numerator := 371829287072277911312447569920 }, { target := 625, numerator := 103937393698135788737727037440 }, { target := 646, numerator := 233718757581061649896493285376 }, { target := 649, numerator := 836113423903068168140422643712 }, { target := 651, numerator := 233718679883375611431861878784 }, { target := 695, numerator := 6554612592417594348058705920 }, { target := 698, numerator := 23448693779332841253938135040 }, { target := 700, numerator := 6554610413395950641117921280 }, { target := 721, numerator := 103937428251193281804930908160 }, { target := 724, numerator := 371829287072277911312447569920 }, { target := 726, numerator := 103937393698135788737727037440 }, { target := 735, numerator := 7490985819905822112067092480 }, { target := 738, numerator := 26798507176380390004500725760 }, { target := 740, numerator := 7490983329595372161277624320 }, { target := 836, numerator := 7303711174408176559265415168 }, { target := 839, numerator := 26128544496970880254388207616 }, { target := 841, numerator := 7303708746355487857245683712 }, { target := 862, numerator := 7303711174408176559265415168 }, { target := 865, numerator := 26128544496970880254388207616 }, { target := 867, numerator := 7303708746355487857245683712 }, { target := 911, numerator := 7303711174408176559265415168 }, { target := 914, numerator := 26128544496970880254388207616 }, { target := 916, numerator := 7303708746355487857245683712 }, { target := 937, numerator := 233718757581061649896493285376 }, { target := 940, numerator := 836113423903068168140422643712 }, { target := 942, numerator := 233718679883375611431861878784 }, { target := 951, numerator := 7303711174408176559265415168 }, { target := 954, numerator := 26128544496970880254388207616 }, { target := 956, numerator := 7303708746355487857245683712 }, { target := 982, numerator := 8427359047394049876075479040 }, { target := 985, numerator := 30148320573427938755063316480 }, { target := 987, numerator := 8427356245794793681437327360 }, { target := 996, numerator := 8801908338389340981678833664 }, { target := 999, numerator := 31488245932246958255288352768 }, { target := 1001, numerator := 8801905412274562289501208576 }]

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
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 12956481988775771005660430336 }, { target := 207, numerator := 15385822361671228069221761024 }, { target := 208, numerator := 11741811802328042473879764992 }, { target := 209, numerator := 121062128582623610334139645952 }, { target := 210, numerator := 14576042237372742381367984128 }, { target := 211, numerator := 11741811802328042473879764992 }, { target := 212, numerator := 14576042237372742381367984128 }, { target := 213, numerator := 14576042237372742381367984128 }, { target := 214, numerator := 624340475834132465335261986816 }, { target := 215, numerator := 14576042237372742381367984128 }, { target := 216, numerator := 121062128582623610334139645952 }, { target := 217, numerator := 624340475834132465335261986816 }, { target := 218, numerator := 12956481988775771005660430336 }, { target := 219, numerator := 14576042237372742381367984128 }, { target := 220, numerator := 14576042237372742381367984128 }, { target := 221, numerator := 15385822361671228069221761024 }, { target := 302, numerator := 129286206278906969018310066176 }, { target := 303, numerator := 153527369956202025709243203584 }, { target := 304, numerator := 117165624440259440672843497472 }, { target := 305, numerator := 1208017989918536991764834680832 }, { target := 306, numerator := 145446982063770340145598824448 }, { target := 307, numerator := 117165624440259440672843497472 }, { target := 308, numerator := 145446982063770340145598824448 }, { target := 309, numerator := 145446982063770340145598824448 }, { target := 310, numerator := 6229979065064829569569816313856 }, { target := 311, numerator := 145446982063770340145598824448 }, { target := 312, numerator := 1208017989918536991764834680832 }, { target := 313, numerator := 6229979065064829569569816313856 }, { target := 314, numerator := 129286206278906969018310066176 }, { target := 315, numerator := 145446982063770340145598824448 }, { target := 316, numerator := 145446982063770340145598824448 }, { target := 317, numerator := 153527369956202025709243203584 }, { target := 679, numerator := 12956481988775771005660430336 }, { target := 680, numerator := 15385822361671228069221761024 }, { target := 681, numerator := 11741811802328042473879764992 }, { target := 682, numerator := 121062128582623610334139645952 }, { target := 683, numerator := 14576042237372742381367984128 }, { target := 684, numerator := 11741811802328042473879764992 }, { target := 685, numerator := 14576042237372742381367984128 }, { target := 686, numerator := 14576042237372742381367984128 }, { target := 687, numerator := 624340475834132465335261986816 }, { target := 688, numerator := 14576042237372742381367984128 }, { target := 689, numerator := 121062128582623610334139645952 }, { target := 690, numerator := 624340475834132465335261986816 }, { target := 691, numerator := 12956481988775771005660430336 }, { target := 692, numerator := 14576042237372742381367984128 }, { target := 693, numerator := 14576042237372742381367984128 }, { target := 694, numerator := 15385822361671228069221761024 }, { target := 966, numerator := 81147706795594234007126016 }, { target := 967, numerator := 96362901819768152883462144 }, { target := 968, numerator := 73540109283507274568957952 }, { target := 969, numerator := 758223885371333624004083712 }, { target := 970, numerator := 91291170145043513258016768 }, { target := 971, numerator := 73540109283507274568957952 }, { target := 972, numerator := 91291170145043513258016768 }, { target := 973, numerator := 91291170145043513258016768 }, { target := 974, numerator := 3910305121212697151218384896 }, { target := 975, numerator := 91291170145043513258016768 }, { target := 976, numerator := 758223885371333624004083712 }, { target := 977, numerator := 3910305121212697151218384896 }, { target := 978, numerator := 81147706795594234007126016 }, { target := 979, numerator := 91291170145043513258016768 }, { target := 980, numerator := 91291170145043513258016768 }, { target := 981, numerator := 96362901819768152883462144 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot7.Left10.expected,
    Slot7.Left11.expected,
    Slot7.Left12.expected,
    Slot7.Left13.expected,
    Slot7.Left14.expected,
    Slot7.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 687196280276740820707573760 }, { target := 112, numerator := 25377244390614664185957580800 }, { target := 115, numerator := 25377238176367754355052380160 }, { target := 122, numerator := 687202494523650651612774400 }, { target := 206, numerator := 11544897508649245787887239168 }, { target := 208, numerator := 426337705762326358324087357440 }, { target := 211, numerator := 426337601362978273164879986688 }, { target := 218, numerator := 11545001907997330947094609920 }, { target := 241, numerator := 25013944602073365873755684864 }, { target := 243, numerator := 923731695818373776368855941120 }, { target := 246, numerator := 923731469619786258523906637824 }, { target := 253, numerator := 25014170800660883718704988160 }, { target := 302, numerator := 824635536332088984849088512 }, { target := 304, numerator := 30452693268737597023149096960 }, { target := 307, numerator := 30452685811641305226062856192 }, { target := 314, numerator := 824642993428380781935329280 }, { target := 337, numerator := 13194168581313423757585416192 }, { target := 339, numerator := 487243092299801552370385551360 }, { target := 342, numerator := 487242972986260883617005699072 }, { target := 349, numerator := 13194287894854092510965268480 }, { target := 363, numerator := 962074792387437148990603264 }, { target := 365, numerator := 35528142146860529860340613120 }, { target := 368, numerator := 35528133446914856097073332224 }, { target := 375, numerator := 962083492333110912257884160 }, { target := 473, numerator := 25013944602073365873755684864 }, { target := 475, numerator := 923731695818373776368855941120 }, { target := 478, numerator := 923731469619786258523906637824 }, { target := 485, numerator := 25014170800660883718704988160 }, { target := 508, numerator := 25013944602073365873755684864 }, { target := 510, numerator := 923731695818373776368855941120 }, { target := 513, numerator := 923731469619786258523906637824 }, { target := 520, numerator := 25014170800660883718704988160 }, { target := 569, numerator := 13194168581313423757585416192 }, { target := 571, numerator := 487243092299801552370385551360 }, { target := 574, numerator := 487242972986260883617005699072 }, { target := 581, numerator := 13194287894854092510965268480 }, { target := 604, numerator := 308688569100311976661842132992 }, { target := 606, numerator := 11399458180264107152332145295360 }, { target := 609, numerator := 11399455388824395256289529167872 }, { target := 616, numerator := 308691360540023872704458260480 }, { target := 630, numerator := 24739066089962669545472655360 }, { target := 632, numerator := 913580798062127910694472908800 }, { target := 635, numerator := 913580574349239156781885685760 }, { target := 642, numerator := 24739289802851423458059878400 }, { target := 679, numerator := 11544897508649245787887239168 }, { target := 681, numerator := 426337705762326358324087357440 }, { target := 684, numerator := 426337601362978273164879986688 }, { target := 691, numerator := 11545001907997330947094609920 }, { target := 705, numerator := 25013944602073365873755684864 }, { target := 707, numerator := 923731695818373776368855941120 }, { target := 710, numerator := 923731469619786258523906637824 }, { target := 717, numerator := 25014170800660883718704988160 }, { target := 785, numerator := 962074792387437148990603264 }, { target := 787, numerator := 35528142146860529860340613120 }, { target := 790, numerator := 35528133446914856097073332224 }, { target := 797, numerator := 962083492333110912257884160 }, { target := 820, numerator := 24739066089962669545472655360 }, { target := 822, numerator := 913580798062127910694472908800 }, { target := 825, numerator := 913580574349239156781885685760 }, { target := 832, numerator := 24739289802851423458059878400 }, { target := 846, numerator := 962074792387437148990603264 }, { target := 848, numerator := 35528142146860529860340613120 }, { target := 851, numerator := 35528133446914856097073332224 }, { target := 858, numerator := 962083492333110912257884160 }]

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
    Slot7.Left16.expected,
    Slot7.Left17.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 692296067143358563347333120 }, { target := 57, numerator := 11630573928008423864235196416 }, { target := 58, numerator := 25199576844018251705842925568 }, { target := 59, numerator := 830755280572030276016799744 }, { target := 60, numerator := 13292084489152484416268795904 }, { target := 61, numerator := 969214494000701988686266368 }, { target := 62, numerator := 25199576844018251705842925568 }, { target := 63, numerator := 25199576844018251705842925568 }, { target := 64, numerator := 13292084489152484416268795904 }, { target := 65, numerator := 310979393360796666655622037504 }, { target := 66, numerator := 24922658417160908280503992320 }, { target := 67, numerator := 11630573928008423864235196416 }, { target := 68, numerator := 25199576844018251705842925568 }, { target := 69, numerator := 969214494000701988686266368 }, { target := 70, numerator := 24922658417160908280503992320 }, { target := 71, numerator := 969214494000701988686266368 }, { target := 72, numerator := 25199576844018251705842925568 }, { target := 73, numerator := 25199576844018251705842925568 }, { target := 74, numerator := 830755280572030276016799744 }, { target := 152, numerator := 25565572734886387111270809600 }, { target := 153, numerator := 429501621946091303469349601280 }, { target := 154, numerator := 930586847549864490850257469440 }, { target := 155, numerator := 30678687281863664533524971520 }, { target := 156, numerator := 490858996509818632536399544320 }, { target := 157, numerator := 35791801828840941955779133440 }, { target := 158, numerator := 930586847549864490850257469440 }, { target := 159, numerator := 930586847549864490850257469440 }, { target := 160, numerator := 490858996509818632536399544320 }, { target := 161, numerator := 11484055272510965090382847672320 }, { target := 162, numerator := 920360618455909936005749145600 }, { target := 163, numerator := 429501621946091303469349601280 }, { target := 164, numerator := 930586847549864490850257469440 }, { target := 165, numerator := 35791801828840941955779133440 }, { target := 166, numerator := 920360618455909936005749145600 }, { target := 167, numerator := 35791801828840941955779133440 }, { target := 168, numerator := 930586847549864490850257469440 }, { target := 169, numerator := 930586847549864490850257469440 }, { target := 170, numerator := 30678687281863664533524971520 }, { target := 895, numerator := 25013944602073365873755684864 }, { target := 897, numerator := 923731695818373776368855941120 }, { target := 900, numerator := 923731469619786258523906637824 }, { target := 907, numerator := 25014170800660883718704988160 }, { target := 921, numerator := 25013944602073365873755684864 }, { target := 923, numerator := 923731695818373776368855941120 }, { target := 926, numerator := 923731469619786258523906637824 }, { target := 933, numerator := 25014170800660883718704988160 }, { target := 966, numerator := 824635536332088984849088512 }, { target := 968, numerator := 30452693268737597023149096960 }, { target := 971, numerator := 30452685811641305226062856192 }, { target := 978, numerator := 824642993428380781935329280 }]

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
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 84713646892483027430014976 }, { target := 57, numerator := 13524295940475107583597740032 }, { target := 59, numerator := 134952135637743529413534810112 }, { target := 67, numerator := 13524295940475107583597740032 }, { target := 74, numerator := 84703980798588403624968192 }, { target := 91, numerator := 100597455684823595073142784 }, { target := 92, numerator := 16060101429314190255522316288 }, { target := 94, numerator := 160255661069820441178572587008 }, { target := 102, numerator := 16060101429314190255522316288 }, { target := 109, numerator := 100585977198323729304649728 }, { target := 152, numerator := 76771742496312743608451072 }, { target := 153, numerator := 12256393196055566247635451904 }, { target := 155, numerator := 122300372921705073531015921664 }, { target := 163, numerator := 12256393196055566247635451904 }, { target := 170, numerator := 76762982598720740785127424 }, { target := 187, numerator := 791543138151638287549202432 }, { target := 188, numerator := 126367640193814286484241383424 }, { target := 190, numerator := 1260959017365166102957715881984 }, { target := 198, numerator := 126367640193814286484241383424 }, { target := 205, numerator := 791452820586810396370796544 }, { target := 222, numerator := 95302852754043405858766848 }, { target := 223, numerator := 15214832933034496031547457536 }, { target := 225, numerator := 151821152592461470590226661376 }, { target := 233, numerator := 15214832933034496031547457536 }, { target := 240, numerator := 95291978398411954078089216 }, { target := 283, numerator := 25565566474522617096091729920 }, { target := 284, numerator := 429501516771979967214341062656 }, { target := 285, numerator := 930586619672623262297738969088 }, { target := 286, numerator := 30678679769427140515310075904 }, { target := 287, numerator := 490858876310834248244961214464 }, { target := 288, numerator := 35791793064331663934528421888 }, { target := 289, numerator := 930586619672623262297738969088 }, { target := 290, numerator := 930586619672623262297738969088 }, { target := 291, numerator := 490858876310834248244961214464 }, { target := 292, numerator := 11484052460355559599564405080064 }, { target := 293, numerator := 920360393082814215459302277120 }, { target := 294, numerator := 429501516771979967214341062656 }, { target := 295, numerator := 930586619672623262297738969088 }, { target := 296, numerator := 35791793064331663934528421888 }, { target := 297, numerator := 920360393082814215459302277120 }, { target := 298, numerator := 35791793064331663934528421888 }, { target := 299, numerator := 930586619672623262297738969088 }, { target := 300, numerator := 930586619672623262297738969088 }, { target := 301, numerator := 30678679769427140515310075904 }, { target := 660, numerator := 692302327507128578526412800 }, { target := 661, numerator := 11630679102119760119243735040 }, { target := 662, numerator := 25199804721259480258361425920 }, { target := 663, numerator := 830762793008554294231695360 }, { target := 664, numerator := 13292204688136868707707125760 }, { target := 665, numerator := 969223258509980009936977920 }, { target := 666, numerator := 25199804721259480258361425920 }, { target := 667, numerator := 25199804721259480258361425920 }, { target := 668, numerator := 13292204688136868707707125760 }, { target := 669, numerator := 310982205516202157474064629760 }, { target := 670, numerator := 24922883790256628826950860800 }, { target := 671, numerator := 11630679102119760119243735040 }, { target := 672, numerator := 25199804721259480258361425920 }, { target := 673, numerator := 969223258509980009936977920 }, { target := 674, numerator := 24922883790256628826950860800 }, { target := 675, numerator := 969223258509980009936977920 }, { target := 676, numerator := 25199804721259480258361425920 }, { target := 677, numerator := 25199804721259480258361425920 }, { target := 678, numerator := 830762793008554294231695360 }]

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
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 283, numerator := 76771742496312743608451072 }, { target := 284, numerator := 12256393196055566247635451904 }, { target := 286, numerator := 122300372921705073531015921664 }, { target := 294, numerator := 12256393196055566247635451904 }, { target := 301, numerator := 76762982598720740785127424 }, { target := 318, numerator := 95302852754043405858766848 }, { target := 319, numerator := 15214832933034496031547457536 }, { target := 321, numerator := 151821152592461470590226661376 }, { target := 329, numerator := 15214832933034496031547457536 }, { target := 336, numerator := 95291978398411954078089216 }, { target := 419, numerator := 95302852754043405858766848 }, { target := 420, numerator := 15214832933034496031547457536 }, { target := 422, numerator := 151821152592461470590226661376 }, { target := 430, numerator := 15214832933034496031547457536 }, { target := 437, numerator := 95291978398411954078089216 }, { target := 454, numerator := 4082138859631525884283846656 }, { target := 455, numerator := 651702010631644246684616097792 }, { target := 457, numerator := 6503006036043766323614708662272 }, { target := 465, numerator := 651702010631644246684616097792 }, { target := 472, numerator := 4081673074731978699678154752 }, { target := 489, numerator := 95302852754043405858766848 }, { target := 490, numerator := 15214832933034496031547457536 }, { target := 492, numerator := 151821152592461470590226661376 }, { target := 500, numerator := 15214832933034496031547457536 }, { target := 507, numerator := 95291978398411954078089216 }, { target := 550, numerator := 791543138151638287549202432 }, { target := 551, numerator := 126367640193814286484241383424 }, { target := 553, numerator := 1260959017365166102957715881984 }, { target := 561, numerator := 126367640193814286484241383424 }, { target := 568, numerator := 791452820586810396370796544 }, { target := 585, numerator := 4082138859631525884283846656 }, { target := 586, numerator := 651702010631644246684616097792 }, { target := 588, numerator := 6503006036043766323614708662272 }, { target := 596, numerator := 651702010631644246684616097792 }, { target := 603, numerator := 4081673074731978699678154752 }, { target := 660, numerator := 84713646892483027430014976 }, { target := 661, numerator := 13524295940475107583597740032 }, { target := 663, numerator := 134952135637743529413534810112 }, { target := 671, numerator := 13524295940475107583597740032 }, { target := 678, numerator := 84703980798588403624968192 }, { target := 766, numerator := 95302852754043405858766848 }, { target := 767, numerator := 15214832933034496031547457536 }, { target := 769, numerator := 151821152592461470590226661376 }, { target := 777, numerator := 15214832933034496031547457536 }, { target := 784, numerator := 95291978398411954078089216 }, { target := 801, numerator := 95302852754043405858766848 }, { target := 802, numerator := 15214832933034496031547457536 }, { target := 804, numerator := 151821152592461470590226661376 }, { target := 812, numerator := 15214832933034496031547457536 }, { target := 819, numerator := 95291978398411954078089216 }, { target := 876, numerator := 100597455684823595073142784 }, { target := 877, numerator := 16060101429314190255522316288 }, { target := 879, numerator := 160255661069820441178572587008 }, { target := 887, numerator := 16060101429314190255522316288 }, { target := 894, numerator := 100585977198323729304649728 }]

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
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 8139103641316473117427630080 }, { target := 15, numerator := 8318975536936205741541294080 }, { target := 16, numerator := 7213541900650050922731274240 }, { target := 17, numerator := 8475911733263809834209247232 }, { target := 18, numerator := 100087893871519456552896430080 }, { target := 19, numerator := 225062507300281588789215756288 }, { target := 20, numerator := 8318975052709173806665564160 }, { target := 21, numerator := 100087893871519456552896430080 }, { target := 22, numerator := 7213541900650050922731274240 }, { target := 23, numerator := 7033203353133799649662992384 }, { target := 24, numerator := 7033203353133799649662992384 }, { target := 25, numerator := 7033203353133799649662992384 }, { target := 26, numerator := 225062507300281588789215756288 }, { target := 27, numerator := 7033203353133799649662992384 }, { target := 28, numerator := 8139104125543505052303360000 }, { target := 29, numerator := 8475911733263809834209247232 }, { target := 40, numerator := 424868254915951762518048768 }, { target := 41, numerator := 35726849454839919077895438336 }, { target := 46, numerator := 35726840835598750637107445760 }, { target := 54, numerator := 424876874157120203306041344 }, { target := 75, numerator := 23869003085165829354946560 }, { target := 76, numerator := 2007126373867411184151429120 }, { target := 81, numerator := 2007125889640379249275699200 }, { target := 89, numerator := 23869487312197764230676480 }, { target := 136, numerator := 29409641989927214802995773440 }, { target := 137, numerator := 54359724558924894586189905920 }, { target := 138, numerator := 25805969873551486671000698880 }, { target := 139, numerator := 30322014601422996838425821184 }, { target := 140, numerator := 358057831995526877560134696960 }, { target := 141, numerator := 805146260054806384135221805056 }, { target := 142, numerator := 54359716891996888950657515520 }, { target := 143, numerator := 358057831995526877560134696960 }, { target := 144, numerator := 25805969873551486671000698880 }, { target := 145, numerator := 25160820626712699504225681408 }, { target := 146, numerator := 25160820626712699504225681408 }, { target := 147, numerator := 25160820626712699504225681408 }, { target := 148, numerator := 805146260054806384135221805056 }, { target := 149, numerator := 25160820626712699504225681408 }, { target := 150, numerator := 29409649656855220438528163840 }, { target := 151, numerator := 30322014601422996838425821184 }, { target := 267, numerator := 8115231940394986508050759680 }, { target := 268, numerator := 6311847064751656172928368640 }, { target := 269, numerator := 7213539502573321340489564160 }, { target := 270, numerator := 8475908915523652575075237888 }, { target := 271, numerator := 100087860598204833599292702720 }, { target := 272, numerator := 225062432480287625823274401792 }, { target := 273, numerator := 6311847064751656172928368640 }, { target := 274, numerator := 100087860598204833599292702720 }, { target := 275, numerator := 7213539502573321340489564160 }, { target := 276, numerator := 7033201015008988306977325056 }, { target := 277, numerator := 7033201015008988306977325056 }, { target := 278, numerator := 7033201015008988306977325056 }, { target := 279, numerator := 225062432480287625823274401792 }, { target := 280, numerator := 7033201015008988306977325056 }, { target := 281, numerator := 8115231940394986508050759680 }, { target := 282, numerator := 8475908915523652575075237888 }]

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
    Slot11.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 645258716735649586895388672 }, { target := 172, numerator := 54259316306882349011560300544 }, { target := 177, numerator := 54259303216611585705419735040 }, { target := 185, numerator := 645271807006412893035954176 }, { target := 267, numerator := 23869003085165829354946560 }, { target := 268, numerator := 2007126373867411184151429120 }, { target := 273, numerator := 2007125889640379249275699200 }, { target := 281, numerator := 23869487312197764230676480 }, { target := 403, numerator := 645258716735649586895388672 }, { target := 404, numerator := 54259316306882349011560300544 }, { target := 409, numerator := 54259303216611585705419735040 }, { target := 417, numerator := 645271807006412893035954176 }, { target := 438, numerator := 645258716735649586895388672 }, { target := 439, numerator := 54259316306882349011560300544 }, { target := 444, numerator := 54259303216611585705419735040 }, { target := 452, numerator := 645271807006412893035954176 }, { target := 534, numerator := 424868254915951762518048768 }, { target := 535, numerator := 35726849454839919077895438336 }, { target := 540, numerator := 35726840835598750637107445760 }, { target := 548, numerator := 424876874157120203306041344 }, { target := 750, numerator := 23869003085165829354946560 }, { target := 751, numerator := 2007126373867411184151429120 }, { target := 756, numerator := 2007125889640379249275699200 }, { target := 764, numerator := 23869487312197764230676480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3
