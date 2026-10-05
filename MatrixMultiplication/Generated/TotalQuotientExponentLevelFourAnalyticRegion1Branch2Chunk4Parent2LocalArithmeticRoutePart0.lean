import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2

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
    Slot2.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 57905738079342740339026821120 }, { target := 260, numerator := 196284813433027187064092753920 }, { target := 262, numerator := 57905738079342740339026821120 }, { target := 353, numerator := 59560187738752532920141873152 }, { target := 356, numerator := 201892950959685106694495404032 }, { target := 358, numerator := 59560187738752532920141873152 }, { target := 379, numerator := 57905738079342740339026821120 }, { target := 382, numerator := 196284813433027187064092753920 }, { target := 384, numerator := 57905738079342740339026821120 }, { target := 389, numerator := 1692496147460480844588646400 }, { target := 391, numerator := 1692496147460480844588646400 }, { target := 524, numerator := 51287939441703570014566612992 }, { target := 527, numerator := 173852263326395508542482153472 }, { target := 529, numerator := 51287939441703570014566612992 }, { target := 620, numerator := 2400606455803609035197940498432 }, { target := 623, numerator := 8137407551180641383714245312512 }, { target := 625, numerator := 2400606455803609035197940498432 }, { target := 646, numerator := 653507615466868069540445552640 }, { target := 649, numerator := 2215214323029878254009046794240 }, { target := 651, numerator := 653507615466868069540445552640 }, { target := 656, numerator := 33917622795108036125556473856 }, { target := 658, numerator := 33917622795108036125556473856 }, { target := 695, numerator := 59560187738752532920141873152 }, { target := 698, numerator := 201892950959685106694495404032 }, { target := 700, numerator := 59560187738752532920141873152 }, { target := 721, numerator := 2400606455803609035197940498432 }, { target := 724, numerator := 8137407551180641383714245312512 }, { target := 726, numerator := 2400606455803609035197940498432 }, { target := 731, numerator := 56935570400570575611962064896 }, { target := 733, numerator := 56935570400570575611962064896 }, { target := 735, numerator := 57905738079342740339026821120 }, { target := 738, numerator := 196284813433027187064092753920 }, { target := 740, numerator := 57905738079342740339026821120 }, { target := 745, numerator := 54633775640024321663321505792 }, { target := 747, numerator := 54633775640024321663321505792 }, { target := 836, numerator := 57905738079342740339026821120 }, { target := 839, numerator := 196284813433027187064092753920 }, { target := 841, numerator := 57905738079342740339026821120 }, { target := 862, numerator := 49633489782293777433451560960 }, { target := 865, numerator := 168244125799737588912079503360 }, { target := 867, numerator := 49633489782293777433451560960 }, { target := 872, numerator := 1692496147460480844588646400 }, { target := 874, numerator := 1692496147460480844588646400 }, { target := 911, numerator := 57905738079342740339026821120 }, { target := 914, numerator := 196284813433027187064092753920 }, { target := 916, numerator := 57905738079342740339026821120 }, { target := 937, numerator := 653507615466868069540445552640 }, { target := 940, numerator := 2215214323029878254009046794240 }, { target := 942, numerator := 653507615466868069540445552640 }, { target := 947, numerator := 54633775640024321663321505792 }, { target := 949, numerator := 54633775640024321663321505792 }, { target := 951, numerator := 49633489782293777433451560960 }, { target := 954, numerator := 168244125799737588912079503360 }, { target := 956, numerator := 49633489782293777433451560960 }, { target := 961, numerator := 36490216939247967009331216384 }, { target := 963, numerator := 36490216939247967009331216384 }, { target := 992, numerator := 1760195993358900078372192256 }, { target := 994, numerator := 1760195993358900078372192256 }, { target := 1006, numerator := 33917622795108036125556473856 }, { target := 1008, numerator := 33917622795108036125556473856 }, { target := 1011, numerator := 1624796301562061610805100544 }, { target := 1013, numerator := 1624796301562061610805100544 }]

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
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2764273265685666854300811264 }, { target := 112, numerator := 100178178126139236630279487488 }, { target := 115, numerator := 100178214941228721736117125120 }, { target := 122, numerator := 2764236450596181748463173632 }, { target := 206, numerator := 73713953751617782781354967040 }, { target := 208, numerator := 2671418083363712976807452999680 }, { target := 211, numerator := 2671419065099432579629790003200 }, { target := 218, numerator := 73712972015898179959017963520 }, { target := 241, numerator := 70488968274984504784670687232 }, { target := 243, numerator := 2554543542216550534072126930944 }, { target := 246, numerator := 2554544481001332404270986690560 }, { target := 253, numerator := 70488029490202634585810927616 }, { target := 302, numerator := 2303561054738055711917342720 }, { target := 304, numerator := 83481815105116030525232906240 }, { target := 307, numerator := 83481845784357268113430937600 }, { target := 314, numerator := 2303530375496818123719311360 }, { target := 337, numerator := 72331817118774949354204561408 }, { target := 339, numerator := 2621328994300643358492313255936 }, { target := 342, numerator := 2621329957628818218761731440640 }, { target := 349, numerator := 72330853790600089084786376704 }, { target := 363, numerator := 2303561054738055711917342720 }, { target := 365, numerator := 83481815105116030525232906240 }, { target := 368, numerator := 83481845784357268113430937600 }, { target := 375, numerator := 2303530375496818123719311360 }, { target := 473, numerator := 70488968274984504784670687232 }, { target := 475, numerator := 2554543542216550534072126930944 }, { target := 478, numerator := 2554544481001332404270986690560 }, { target := 485, numerator := 70488029490202634585810927616 }, { target := 508, numerator := 40081962352442169387361763328 }, { target := 510, numerator := 1452583582829018931139052568576 }, { target := 513, numerator := 1452584116647816465173698314240 }, { target := 520, numerator := 40081428533644635352716017664 }, { target := 569, numerator := 72331817118774949354204561408 }, { target := 571, numerator := 2621328994300643358492313255936 }, { target := 574, numerator := 2621329957628818218761731440640 }, { target := 581, numerator := 72330853790600089084786376704 }, { target := 604, numerator := 1129205629032594909981881401344 }, { target := 606, numerator := 40922785764527878163469170638848 }, { target := 609, numerator := 40922800803491932829203845611520 }, { target := 616, numerator := 1129190590068540244247206428672 }, { target := 630, numerator := 44228372250970669668812980224 }, { target := 632, numerator := 1602850850018227786084471799808 }, { target := 635, numerator := 1602851439059659547777874001920 }, { target := 642, numerator := 44227783209538907975410778112 }, { target := 679, numerator := 73713953751617782781354967040 }, { target := 681, numerator := 2671418083363712976807452999680 }, { target := 684, numerator := 2671419065099432579629790003200 }, { target := 691, numerator := 73712972015898179959017963520 }, { target := 705, numerator := 70488968274984504784670687232 }, { target := 707, numerator := 2554543542216550534072126930944 }, { target := 710, numerator := 2554544481001332404270986690560 }, { target := 717, numerator := 70488029490202634585810927616 }, { target := 785, numerator := 2303561054738055711917342720 }, { target := 787, numerator := 83481815105116030525232906240 }, { target := 790, numerator := 83481845784357268113430937600 }, { target := 797, numerator := 2303530375496818123719311360 }, { target := 982, numerator := 57905738079342740339026821120 }, { target := 985, numerator := 196284813433027187064092753920 }, { target := 987, numerator := 57905738079342740339026821120 }, { target := 996, numerator := 51287939441703570014566612992 }, { target := 999, numerator := 173852263326395508542482153472 }, { target := 1001, numerator := 51287939441703570014566612992 }]

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
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 164280246360031468349030400 }, { target := 57, numerator := 24263332676869092641498726400 }, { target := 59, numerator := 252892658729353193786966016000 }, { target := 67, numerator := 24263332676869092641498726400 }, { target := 74, numerator := 164280246360031468349030400 }, { target := 91, numerator := 160857741227530812758425600 }, { target := 92, numerator := 23757846579434319878134169600 }, { target := 94, numerator := 247624061672491668916404224000 }, { target := 102, numerator := 23757846579434319878134169600 }, { target := 109, numerator := 160857741227530812758425600 }, { target := 152, numerator := 126632689902524256852377600 }, { target := 153, numerator := 18702985605086592244488601600 }, { target := 155, numerator := 194938091103876420210786304000 }, { target := 163, numerator := 18702985605086592244488601600 }, { target := 170, numerator := 126632689902524256852377600 }, { target := 187, numerator := 3980373469098262451873382400 }, { target := 188, numerator := 587880331316640723792979558400 }, { target := 190, numerator := 6127378377129953424463364096000 }, { target := 198, numerator := 587880331316640723792979558400 }, { target := 205, numerator := 3980373469098262451873382400 }, { target := 222, numerator := 126632689902524256852377600 }, { target := 223, numerator := 18702985605086592244488601600 }, { target := 225, numerator := 194938091103876420210786304000 }, { target := 233, numerator := 18702985605086592244488601600 }, { target := 240, numerator := 126632689902524256852377600 }, { target := 283, numerator := 126632689902524256852377600 }, { target := 284, numerator := 18702985605086592244488601600 }, { target := 286, numerator := 194938091103876420210786304000 }, { target := 294, numerator := 18702985605086592244488601600 }, { target := 301, numerator := 126632689902524256852377600 }, { target := 318, numerator := 130055195035024912442982400 }, { target := 319, numerator := 19208471702521365007853158400 }, { target := 321, numerator := 200206688160737945081348096000 }, { target := 329, numerator := 19208471702521365007853158400 }, { target := 336, numerator := 130055195035024912442982400 }, { target := 419, numerator := 130055195035024912442982400 }, { target := 420, numerator := 19208471702521365007853158400 }, { target := 422, numerator := 200206688160737945081348096000 }, { target := 430, numerator := 19208471702521365007853158400 }, { target := 437, numerator := 130055195035024912442982400 }, { target := 820, numerator := 44228372250970669668812980224 }, { target := 822, numerator := 1602850850018227786084471799808 }, { target := 825, numerator := 1602851439059659547777874001920 }, { target := 832, numerator := 44227783209538907975410778112 }, { target := 846, numerator := 2303561054738055711917342720 }, { target := 848, numerator := 83481815105116030525232906240 }, { target := 851, numerator := 83481845784357268113430937600 }, { target := 858, numerator := 2303530375496818123719311360 }, { target := 895, numerator := 70949680485932115927054155776 }, { target := 897, numerator := 2571239905237573740177173512192 }, { target := 900, numerator := 2571240850158203857893672878080 }, { target := 907, numerator := 70948735565301998210554789888 }, { target := 921, numerator := 40081962352442169387361763328 }, { target := 923, numerator := 1452583582829018931139052568576 }, { target := 926, numerator := 1452584116647816465173698314240 }, { target := 933, numerator := 40081428533644635352716017664 }, { target := 966, numerator := 2764273265685666854300811264 }, { target := 968, numerator := 100178178126139236630279487488 }, { target := 971, numerator := 100178214941228721736117125120 }, { target := 978, numerator := 2764236450596181748463173632 }]

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
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 21141117018289734571524096 }, { target := 15, numerator := 1777740502568278477391265792 }, { target := 20, numerator := 1777740073681478763644190720 }, { target := 28, numerator := 21141545905089448318599168 }, { target := 40, numerator := 518298352706458008850268160 }, { target := 41, numerator := 43583315546835214284431032320 }, { target := 46, numerator := 43583305032191092269986611200 }, { target := 54, numerator := 518308867350580023294689280 }, { target := 75, numerator := 21141117018289734571524096 }, { target := 76, numerator := 1777740502568278477391265792 }, { target := 81, numerator := 1777740073681478763644190720 }, { target := 89, numerator := 21141545905089448318599168 }, { target := 136, numerator := 434415856150018094260027392 }, { target := 137, numerator := 36529700004386883551556009984 }, { target := 142, numerator := 36529691191454902336817725440 }, { target := 150, numerator := 434424669081999308998311936 }, { target := 171, numerator := 426914169466108833605615616 }, { target := 172, numerator := 35898888858314268607965560832 }, { target := 177, numerator := 35898880197567926001331077120 }, { target := 185, numerator := 426922830212451440240099328 }, { target := 267, numerator := 21141117018289734571524096 }, { target := 268, numerator := 1777740502568278477391265792 }, { target := 273, numerator := 1777740073681478763644190720 }, { target := 281, numerator := 21141545905089448318599168 }, { target := 454, numerator := 2200670800197921544758886400 }, { target := 455, numerator := 325027560650558886843410022400 }, { target := 457, numerator := 3387707907561960491771232256000 }, { target := 465, numerator := 325027560650558886843410022400 }, { target := 472, numerator := 2200670800197921544758886400 }, { target := 489, numerator := 119787679637522945671168000 }, { target := 490, numerator := 17692013410217046717759488000 }, { target := 492, numerator := 184400896990153370469662720000 }, { target := 500, numerator := 17692013410217046717759488000 }, { target := 507, numerator := 119787679637522945671168000 }, { target := 550, numerator := 3980373469098262451873382400 }, { target := 551, numerator := 587880331316640723792979558400 }, { target := 553, numerator := 6127378377129953424463364096000 }, { target := 561, numerator := 587880331316640723792979558400 }, { target := 568, numerator := 3980373469098262451873382400 }, { target := 585, numerator := 2200670800197921544758886400 }, { target := 586, numerator := 325027560650558886843410022400 }, { target := 588, numerator := 3387707907561960491771232256000 }, { target := 596, numerator := 325027560650558886843410022400 }, { target := 603, numerator := 2200670800197921544758886400 }, { target := 660, numerator := 164280246360031468349030400 }, { target := 661, numerator := 24263332676869092641498726400 }, { target := 663, numerator := 252892658729353193786966016000 }, { target := 671, numerator := 24263332676869092641498726400 }, { target := 678, numerator := 164280246360031468349030400 }, { target := 766, numerator := 126632689902524256852377600 }, { target := 767, numerator := 18702985605086592244488601600 }, { target := 769, numerator := 194938091103876420210786304000 }, { target := 777, numerator := 18702985605086592244488601600 }, { target := 784, numerator := 126632689902524256852377600 }, { target := 801, numerator := 119787679637522945671168000 }, { target := 802, numerator := 17692013410217046717759488000 }, { target := 804, numerator := 184400896990153370469662720000 }, { target := 812, numerator := 17692013410217046717759488000 }, { target := 819, numerator := 119787679637522945671168000 }, { target := 876, numerator := 160857741227530812758425600 }, { target := 877, numerator := 23757846579434319878134169600 }, { target := 879, numerator := 247624061672491668916404224000 }, { target := 887, numerator := 23757846579434319878134169600 }, { target := 894, numerator := 160857741227530812758425600 }]

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
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1873948509681984700720087040 }, { target := 57, numerator := 196480121448194700305036738560 }, { target := 59, numerator := 2117859327561191279327969280000 }, { target := 67, numerator := 196480271328104296560711434240 }, { target := 74, numerator := 1873948509681984700720087040 }, { target := 110, numerator := 1882149597251708922605076480 }, { target := 112, numerator := 65870543311275693763398205440 }, { target := 115, numerator := 65870575618281092169785671680 }, { target := 122, numerator := 1882133443749009719411343360 }, { target := 152, numerator := 65583525693361638452882309120 }, { target := 153, numerator := 6876314384656847076360642887680 }, { target := 155, numerator := 74119796198459166756270243840000 }, { target := 163, numerator := 6876319630080000988352840990720 }, { target := 170, numerator := 65583525693361638452882309120 }, { target := 206, numerator := 197339990688668200087553310720 }, { target := 208, numerator := 6906407664239590389605109596160 }, { target := 211, numerator := 6906411051570838559060939243520 }, { target := 218, numerator := 197338297023044115359638487040 }, { target := 257, numerator := 9231580021296079130171801600 }, { target := 260, numerator := 31563397558329346157046661120 }, { target := 262, numerator := 9231577039481061721652592640 }, { target := 302, numerator := 2127127858535200869171855360000 }, { target := 304, numerator := 74444171674163583240980398080000 }, { target := 307, numerator := 74444208186208804908312821760000 }, { target := 314, numerator := 2127109602512590035505643520000 }, { target := 353, numerator := 772952208871027134444821544960 }, { target := 356, numerator := 2642775971816773121473586921472 }, { target := 358, numerator := 772951959206235318327321821184 }, { target := 389, numerator := 3390620552867645163590123520 }, { target := 391, numerator := 3389087389562506814259462144 }, { target := 403, numerator := 427596140982827857301471232 }, { target := 404, numerator := 35956235326139051784655601664 }, { target := 409, numerator := 35956226651557651122738954240 }, { target := 417, numerator := 427604815564228519218118656 }, { target := 438, numerator := 383267992396091317070856192 }, { target := 439, numerator := 32228714917528145299802947584 }, { target := 444, numerator := 32228707142225518231226941440 }, { target := 452, numerator := 383275767698718385646862336 }, { target := 534, numerator := 518298352706458008850268160 }, { target := 535, numerator := 43583315546835214284431032320 }, { target := 540, numerator := 43583305032191092269986611200 }, { target := 548, numerator := 518308867350580023294689280 }, { target := 679, numerator := 197340141224507378821371002880 }, { target := 681, numerator := 6906412932618644318717623664640 }, { target := 684, numerator := 6906416319952476428459657134080 }, { target := 691, numerator := 197338447557591323950354268160 }, { target := 695, numerator := 772952488601748450421160017920 }, { target := 698, numerator := 2642776928235061844144547692544 }, { target := 700, numerator := 772952238936866280836136173568 }, { target := 731, numerator := 32841798480614882186562109440 }, { target := 733, numerator := 32826948148789151451282669568 }, { target := 750, numerator := 21141117018289734571524096 }, { target := 751, numerator := 1777740502568278477391265792 }, { target := 756, numerator := 1777740073681478763644190720 }, { target := 764, numerator := 21141545905089448318599168 }, { target := 966, numerator := 1882149597251708922605076480 }, { target := 968, numerator := 65870543311275693763398205440 }, { target := 971, numerator := 65870575618281092169785671680 }, { target := 978, numerator := 1882133443749009719411343360 }, { target := 982, numerator := 9231300290574763153833328640 }, { target := 985, numerator := 31562441140040623486085890048 }, { target := 987, numerator := 9231297308850099212838240256 }, { target := 992, numerator := 3390620552867645163590123520 }, { target := 994, numerator := 3389087389562506814259462144 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 3390620552867645163590123520 }, { target := 6, numerator := 32841798480614882186562109440 }, { target := 11, numerator := 3390620552867645163590123520 }, { target := 14, numerator := 9490409367687557984288768000 }, { target := 15, numerator := 794623766129093315784395980800 }, { target := 20, numerator := 794624053702732051834837401600 }, { target := 28, numerator := 9490121794048821933847347200 }, { target := 126, numerator := 3389087389562506814259462144 }, { target := 128, numerator := 32826948148789151451282669568 }, { target := 133, numerator := 3389087389562506814259462144 }, { target := 136, numerator := 32448352630058206329674137600 }, { target := 137, numerator := 2716872494391075171608360386560 }, { target := 142, numerator := 2716873477624829933232712581120 }, { target := 150, numerator := 32447369396303444705321943040 }, { target := 257, numerator := 21141117018289734571524096 }, { target := 258, numerator := 518298352706458008850268160 }, { target := 259, numerator := 21141117018289734571524096 }, { target := 260, numerator := 434415856150018094260027392 }, { target := 261, numerator := 426914169466108833605615616 }, { target := 262, numerator := 21141117018289734571524096 }, { target := 263, numerator := 427596140982827857301471232 }, { target := 264, numerator := 383267992396091317070856192 }, { target := 265, numerator := 518298352706458008850268160 }, { target := 266, numerator := 21141117018289734571524096 }, { target := 267, numerator := 9490406302270250368054067200 }, { target := 268, numerator := 794623509464354065570143928320 }, { target := 273, numerator := 794623797037899914878270832640 }, { target := 281, numerator := 9490118728724401059927162880 }, { target := 283, numerator := 65583557859595771506736496640 }, { target := 284, numerator := 6876317757228481964032351272960 }, { target := 286, numerator := 74119832551410509462089236480000 }, { target := 294, numerator := 6876323002654208557311684771840 }, { target := 301, numerator := 65583557859595771506736496640 }, { target := 353, numerator := 1777740502568278477391265792 }, { target := 354, numerator := 43583315546835214284431032320 }, { target := 355, numerator := 1777740502568278477391265792 }, { target := 356, numerator := 36529700004386883551556009984 }, { target := 357, numerator := 35898888858314268607965560832 }, { target := 358, numerator := 1777740502568278477391265792 }, { target := 359, numerator := 35956235326139051784655601664 }, { target := 360, numerator := 32228714917528145299802947584 }, { target := 361, numerator := 43583315546835214284431032320 }, { target := 362, numerator := 1777740502568278477391265792 }, { target := 660, numerator := 1873932426564918173792993280 }, { target := 661, numerator := 196478435162377256469182545920 }, { target := 663, numerator := 2117841151085519926418472960000 }, { target := 671, numerator := 196478585041000512081289543680 }, { target := 678, numerator := 1873932426564918173792993280 }, { target := 695, numerator := 1777740073681478763644190720 }, { target := 696, numerator := 43583305032191092269986611200 }, { target := 697, numerator := 1777740073681478763644190720 }, { target := 698, numerator := 36529691191454902336817725440 }, { target := 699, numerator := 35898880197567926001331077120 }, { target := 700, numerator := 1777740073681478763644190720 }, { target := 701, numerator := 35956226651557651122738954240 }, { target := 702, numerator := 32228707142225518231226941440 }, { target := 703, numerator := 43583305032191092269986611200 }, { target := 704, numerator := 1777740073681478763644190720 }]

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
    Slot16.Left14.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 166807634765570414015938560 }, { target := 111, numerator := 163332475707954363723939840 }, { target := 112, numerator := 128580885131793860803952640 }, { target := 113, numerator := 4041609984007466489594511360 }, { target := 114, numerator := 128580885131793860803952640 }, { target := 115, numerator := 128580885131793860803952640 }, { target := 116, numerator := 132056044189409911095951360 }, { target := 117, numerator := 132056044189409911095951360 }, { target := 118, numerator := 2234527274047120337755176960 }, { target := 119, numerator := 121630567016561760219955200 }, { target := 120, numerator := 4041609984007466489594511360 }, { target := 121, numerator := 2234527274047120337755176960 }, { target := 122, numerator := 166807634765570414015938560 }, { target := 123, numerator := 128580885131793860803952640 }, { target := 124, numerator := 121630567016561760219955200 }, { target := 125, numerator := 163332475707954363723939840 }, { target := 206, numerator := 24636614718051694066752552960 }, { target := 207, numerator := 24123351911425617107028541440 }, { target := 208, numerator := 18990723845164847509788426240 }, { target := 209, numerator := 596924644106127504159025397760 }, { target := 210, numerator := 18990723845164847509788426240 }, { target := 211, numerator := 18990723845164847509788426240 }, { target := 212, numerator := 19503986651790924469512437760 }, { target := 213, numerator := 19503986651790924469512437760 }, { target := 214, numerator := 330027984660567485102539407360 }, { target := 215, numerator := 17964198231912693590340403200 }, { target := 216, numerator := 596924644106127504159025397760 }, { target := 217, numerator := 330027984660567485102539407360 }, { target := 218, numerator := 24636614718051694066752552960 }, { target := 219, numerator := 18990723845164847509788426240 }, { target := 220, numerator := 17964198231912693590340403200 }, { target := 221, numerator := 24123351911425617107028541440 }, { target := 302, numerator := 256783315017497089075996262400 }, { target := 303, numerator := 251433662621299233053579673600 }, { target := 304, numerator := 197937138659320672829413785600 }, { target := 305, numerator := 6221645736778106554070492774400 }, { target := 306, numerator := 197937138659320672829413785600 }, { target := 307, numerator := 197937138659320672829413785600 }, { target := 308, numerator := 203286791055518528851830374400 }, { target := 309, numerator := 203286791055518528851830374400 }, { target := 310, numerator := 3439826490755221422413866598400 }, { target := 311, numerator := 187237833866924960784580608000 }, { target := 312, numerator := 6221645736778106554070492774400 }, { target := 313, numerator := 3439826490755221422413866598400 }, { target := 314, numerator := 256783315017497089075996262400 }, { target := 315, numerator := 197937138659320672829413785600 }, { target := 316, numerator := 187237833866924960784580608000 }, { target := 317, numerator := 251433662621299233053579673600 }, { target := 982, numerator := 21141545905089448318599168 }, { target := 983, numerator := 518308867350580023294689280 }, { target := 984, numerator := 21141545905089448318599168 }, { target := 985, numerator := 434424669081999308998311936 }, { target := 986, numerator := 426922830212451440240099328 }, { target := 987, numerator := 21141545905089448318599168 }, { target := 988, numerator := 427604815564228519218118656 }, { target := 989, numerator := 383275767698718385646862336 }, { target := 990, numerator := 518308867350580023294689280 }, { target := 991, numerator := 21141545905089448318599168 }]

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
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2761156835848366215231700992 }, { target := 57, numerator := 73630848955956432406178693120 }, { target := 58, numerator := 70409499314133338488408375296 }, { target := 59, numerator := 2300964029873638512693084160 }, { target := 60, numerator := 72250270538032249298562842624 }, { target := 61, numerator := 2300964029873638512693084160 }, { target := 62, numerator := 70409499314133338488408375296 }, { target := 63, numerator := 40036774119801310120859664384 }, { target := 64, numerator := 72250270538032249298562842624 }, { target := 65, numerator := 1127932567444057598922149855232 }, { target := 66, numerator := 44178509373573859443707215872 }, { target := 67, numerator := 73630848955956432406178693120 }, { target := 68, numerator := 70409499314133338488408375296 }, { target := 69, numerator := 2300964029873638512693084160 }, { target := 70, numerator := 44178509373573859443707215872 }, { target := 71, numerator := 2300964029873638512693084160 }, { target := 72, numerator := 70869692120108066190946992128 }, { target := 73, numerator := 40036774119801310120859664384 }, { target := 74, numerator := 2761156835848366215231700992 }, { target := 679, numerator := 24636614718051694066752552960 }, { target := 680, numerator := 24123351911425617107028541440 }, { target := 681, numerator := 18990723845164847509788426240 }, { target := 682, numerator := 596924644106127504159025397760 }, { target := 683, numerator := 18990723845164847509788426240 }, { target := 684, numerator := 18990723845164847509788426240 }, { target := 685, numerator := 19503986651790924469512437760 }, { target := 686, numerator := 19503986651790924469512437760 }, { target := 687, numerator := 330027984660567485102539407360 }, { target := 688, numerator := 17964198231912693590340403200 }, { target := 689, numerator := 596924644106127504159025397760 }, { target := 690, numerator := 330027984660567485102539407360 }, { target := 691, numerator := 24636614718051694066752552960 }, { target := 692, numerator := 18990723845164847509788426240 }, { target := 693, numerator := 17964198231912693590340403200 }, { target := 694, numerator := 24123351911425617107028541440 }, { target := 966, numerator := 166807634765570414015938560 }, { target := 967, numerator := 163332475707954363723939840 }, { target := 968, numerator := 128580885131793860803952640 }, { target := 969, numerator := 4041609984007466489594511360 }, { target := 970, numerator := 128580885131793860803952640 }, { target := 971, numerator := 128580885131793860803952640 }, { target := 972, numerator := 132056044189409911095951360 }, { target := 973, numerator := 132056044189409911095951360 }, { target := 974, numerator := 2234527274047120337755176960 }, { target := 975, numerator := 121630567016561760219955200 }, { target := 976, numerator := 4041609984007466489594511360 }, { target := 977, numerator := 2234527274047120337755176960 }, { target := 978, numerator := 166807634765570414015938560 }, { target := 979, numerator := 128580885131793860803952640 }, { target := 980, numerator := 121630567016561760219955200 }, { target := 981, numerator := 163332475707954363723939840 }]

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
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 100065237677293532868576804864 }, { target := 153, numerator := 2668406338061160876495381463040 }, { target := 154, numerator := 2551663560770985088148708524032 }, { target := 155, numerator := 83387698064411277390480670720 }, { target := 156, numerator := 2618373719222514110061093060608 }, { target := 157, numerator := 83387698064411277390480670720 }, { target := 158, numerator := 2551663560770985088148708524032 }, { target := 159, numerator := 1450945946320756226594363670528 }, { target := 160, numerator := 2618373719222514110061093060608 }, { target := 161, numerator := 40876649591174408176813624786944 }, { target := 162, numerator := 1601043802836696525897228877824 }, { target := 163, numerator := 2668406338061160876495381463040 }, { target := 164, numerator := 2551663560770985088148708524032 }, { target := 165, numerator := 83387698064411277390480670720 }, { target := 166, numerator := 1601043802836696525897228877824 }, { target := 167, numerator := 83387698064411277390480670720 }, { target := 168, numerator := 2568341100383867343626804658176 }, { target := 169, numerator := 1450945946320756226594363670528 }, { target := 170, numerator := 100065237677293532868576804864 }, { target := 283, numerator := 100065274450877843808567951360 }, { target := 284, numerator := 2668407318690075834895145369600 }, { target := 285, numerator := 2551664498497385017118482759680 }, { target := 286, numerator := 83387728709064869840473292800 }, { target := 287, numerator := 2618374681464636912990861393920 }, { target := 288, numerator := 83387728709064869840473292800 }, { target := 289, numerator := 2551664498497385017118482759680 }, { target := 290, numerator := 1450946479537728735224235294720 }, { target := 291, numerator := 2618374681464636912990861393920 }, { target := 292, numerator := 40876664613183599195800008130560 }, { target := 293, numerator := 1601044391214045500937087221760 }, { target := 294, numerator := 2668407318690075834895145369600 }, { target := 295, numerator := 2551664498497385017118482759680 }, { target := 296, numerator := 83387728709064869840473292800 }, { target := 297, numerator := 1601044391214045500937087221760 }, { target := 298, numerator := 83387728709064869840473292800 }, { target := 299, numerator := 2568342044239197991086577418240 }, { target := 300, numerator := 1450946479537728735224235294720 }, { target := 301, numerator := 100065274450877843808567951360 }, { target := 660, numerator := 2761120062264055275240554496 }, { target := 661, numerator := 73629868327041474006414786560 }, { target := 662, numerator := 70408561587733409518634139648 }, { target := 663, numerator := 2300933385220046062700462080 }, { target := 664, numerator := 72249308295909446368794509312 }, { target := 665, numerator := 2300933385220046062700462080 }, { target := 666, numerator := 70408561587733409518634139648 }, { target := 667, numerator := 40036240902828801490988040192 }, { target := 668, numerator := 72249308295909446368794509312 }, { target := 669, numerator := 1127917545434866579935766511616 }, { target := 670, numerator := 44177920996224884403848871936 }, { target := 671, numerator := 73629868327041474006414786560 }, { target := 672, numerator := 70408561587733409518634139648 }, { target := 673, numerator := 2300933385220046062700462080 }, { target := 674, numerator := 44177920996224884403848871936 }, { target := 675, numerator := 2300933385220046062700462080 }, { target := 676, numerator := 70868748264777418731174232064 }, { target := 677, numerator := 40036240902828801490988040192 }, { target := 678, numerator := 2761120062264055275240554496 }]

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
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1692496147460480844588646400 }, { target := 5, numerator := 33917622795108036125556473856 }, { target := 6, numerator := 56935570400570575611962064896 }, { target := 7, numerator := 54633775640024321663321505792 }, { target := 8, numerator := 1692496147460480844588646400 }, { target := 9, numerator := 54633775640024321663321505792 }, { target := 10, numerator := 36490216939247967009331216384 }, { target := 11, numerator := 1760195993358900078372192256 }, { target := 12, numerator := 33917622795108036125556473856 }, { target := 13, numerator := 1624796301562061610805100544 }, { target := 14, numerator := 56775257292544292046074019840 }, { target := 15, numerator := 58397407500902700390247563264 }, { target := 16, numerator := 56775257292544292046074019840 }, { target := 17, numerator := 50286656459110658669379846144 }, { target := 18, numerator := 2353739952328050507395811508224 }, { target := 19, numerator := 640749332301571295948549652480 }, { target := 20, numerator := 58397407500902700390247563264 }, { target := 21, numerator := 2353739952328050507395811508224 }, { target := 22, numerator := 56775257292544292046074019840 }, { target := 23, numerator := 56775257292544292046074019840 }, { target := 24, numerator := 48664506250752250325206302720 }, { target := 25, numerator := 56775257292544292046074019840 }, { target := 26, numerator := 640749332301571295948549652480 }, { target := 27, numerator := 48664506250752250325206302720 }, { target := 28, numerator := 56775257292544292046074019840 }, { target := 29, numerator := 50286656459110658669379846144 }, { target := 136, numerator := 192452788875766352609479229440 }, { target := 137, numerator := 197951439986502534112607207424 }, { target := 138, numerator := 192452788875766352609479229440 }, { target := 139, numerator := 170458184432821626596967317504 }, { target := 140, numerator := 7978542761678199361038696054784 }, { target := 141, numerator := 2171967188740791693735551303680 }, { target := 142, numerator := 197951439986502534112607207424 }, { target := 143, numerator := 7978542761678199361038696054784 }, { target := 144, numerator := 192452788875766352609479229440 }, { target := 145, numerator := 192452788875766352609479229440 }, { target := 146, numerator := 164959533322085445093839339520 }, { target := 147, numerator := 192452788875766352609479229440 }, { target := 148, numerator := 2171967188740791693735551303680 }, { target := 149, numerator := 164959533322085445093839339520 }, { target := 150, numerator := 192452788875766352609479229440 }, { target := 151, numerator := 170458184432821626596967317504 }, { target := 267, numerator := 56775257292544292046074019840 }, { target := 268, numerator := 58397407500902700390247563264 }, { target := 269, numerator := 56775257292544292046074019840 }, { target := 270, numerator := 50286656459110658669379846144 }, { target := 271, numerator := 2353739952328050507395811508224 }, { target := 272, numerator := 640749332301571295948549652480 }, { target := 273, numerator := 58397407500902700390247563264 }, { target := 274, numerator := 2353739952328050507395811508224 }, { target := 275, numerator := 56775257292544292046074019840 }, { target := 276, numerator := 56775257292544292046074019840 }, { target := 277, numerator := 48664506250752250325206302720 }, { target := 278, numerator := 56775257292544292046074019840 }, { target := 279, numerator := 640749332301571295948549652480 }, { target := 280, numerator := 48664506250752250325206302720 }, { target := 281, numerator := 56775257292544292046074019840 }, { target := 282, numerator := 50286656459110658669379846144 }]

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
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 126, numerator := 1692496147460480844588646400 }, { target := 127, numerator := 33917622795108036125556473856 }, { target := 128, numerator := 56935570400570575611962064896 }, { target := 129, numerator := 54633775640024321663321505792 }, { target := 130, numerator := 1692496147460480844588646400 }, { target := 131, numerator := 54633775640024321663321505792 }, { target := 132, numerator := 36490216939247967009331216384 }, { target := 133, numerator := 1760195993358900078372192256 }, { target := 134, numerator := 33917622795108036125556473856 }, { target := 135, numerator := 1624796301562061610805100544 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2
