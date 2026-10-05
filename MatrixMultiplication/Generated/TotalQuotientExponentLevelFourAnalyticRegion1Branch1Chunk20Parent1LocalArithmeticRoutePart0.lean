import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 83; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1

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
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 133634043241079284124614656 }, { target := 111, numerator := 152194327024562518030811136 }, { target := 112, numerator := 118785816214292696999657472 }, { target := 113, numerator := 1592472348622861469151657984 }, { target := 114, numerator := 141058156754472577687093248 }, { target := 115, numerator := 118785816214292696999657472 }, { target := 116, numerator := 141058156754472577687093248 }, { target := 117, numerator := 137346099997775930905853952 }, { target := 118, numerator := 5189455345861912200172535808 }, { target := 119, numerator := 137346099997775930905853952 }, { target := 120, numerator := 1592472348622861469151657984 }, { target := 121, numerator := 5189455345861912200172535808 }, { target := 122, numerator := 133634043241079284124614656 }, { target := 123, numerator := 137346099997775930905853952 }, { target := 124, numerator := 137346099997775930905853952 }, { target := 125, numerator := 152194327024562518030811136 }, { target := 257, numerator := 10746579646939213040975872 }, { target := 258, numerator := 214931592938784260819517440 }, { target := 259, numerator := 11130386062901327792439296 }, { target := 260, numerator := 199963142716261785512443904 }, { target := 261, numerator := 299369004450449506141470720 }, { target := 262, numerator := 10746579646939213040975872 }, { target := 263, numerator := 299752810866411620892934144 }, { target := 264, numerator := 299752810866411620892934144 }, { target := 265, numerator := 214547786522822146068054016 }, { target := 266, numerator := 11130386062901327792439296 }, { target := 353, numerator := 1884849105508799332898308096 }, { target := 354, numerator := 37696982110175986657966161920 }, { target := 355, numerator := 1952165144991256451930390528 }, { target := 356, numerator := 35071656570360159015714947072 }, { target := 357, numerator := 52506510796316552845024296960 }, { target := 358, numerator := 1884849105508799332898308096 }, { target := 359, numerator := 52573826835799009964056379392 }, { target := 360, numerator := 52573826835799009964056379392 }, { target := 361, numerator := 37629666070693529538934079488 }, { target := 362, numerator := 1952165144991256451930390528 }, { target := 695, numerator := 1884849331481414235840315392 }, { target := 696, numerator := 37696986629628284716806307840 }, { target := 697, numerator := 1952165379034321887120326656 }, { target := 698, numerator := 35071660775064886316885868544 }, { target := 699, numerator := 52506517091267967998408785920 }, { target := 700, numerator := 1884849331481414235840315392 }, { target := 701, numerator := 52573833138820875649688797184 }, { target := 702, numerator := 52573833138820875649688797184 }, { target := 703, numerator := 37629670582075377065526296576 }, { target := 704, numerator := 1952165379034321887120326656 }, { target := 982, numerator := 10746353674324310098968576 }, { target := 983, numerator := 214927073486486201979371520 }, { target := 984, numerator := 11130152019835892602503168 }, { target := 985, numerator := 199958938011534484341522432 }, { target := 986, numerator := 299362709499034352756981760 }, { target := 987, numerator := 10746353674324310098968576 }, { target := 988, numerator := 299746507844545935260516352 }, { target := 989, numerator := 299746507844545935260516352 }, { target := 990, numerator := 214543275140974619475836928 }, { target := 991, numerator := 11130152019835892602503168 }]

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
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 15794685949339354337541881856 }, { target := 207, numerator := 17988392331192042439978254336 }, { target := 208, numerator := 14039720843857203855592783872 }, { target := 209, numerator := 188220007562960639189040758784 }, { target := 210, numerator := 16672168502080429578516430848 }, { target := 211, numerator := 14039720843857203855592783872 }, { target := 212, numerator := 16672168502080429578516430848 }, { target := 213, numerator := 16233427225709891958029156352 }, { target := 214, numerator := 613360304366011593441209745408 }, { target := 215, numerator := 16233427225709891958029156352 }, { target := 216, numerator := 188220007562960639189040758784 }, { target := 217, numerator := 613360304366011593441209745408 }, { target := 218, numerator := 15794685949339354337541881856 }, { target := 219, numerator := 16233427225709891958029156352 }, { target := 220, numerator := 16233427225709891958029156352 }, { target := 221, numerator := 17988392331192042439978254336 }, { target := 302, numerator := 149888421199573567079360495616 }, { target := 303, numerator := 170706257477292118062605008896 }, { target := 304, numerator := 133234152177398726292764884992 }, { target := 305, numerator := 1786170352628251674362379239424 }, { target := 306, numerator := 158215555710660987472658300928 }, { target := 307, numerator := 133234152177398726292764884992 }, { target := 308, numerator := 158215555710660987472658300928 }, { target := 309, numerator := 154051988455117277276009398272 }, { target := 310, numerator := 5820667023250106854915165913088 }, { target := 311, numerator := 154051988455117277276009398272 }, { target := 312, numerator := 1786170352628251674362379239424 }, { target := 313, numerator := 5820667023250106854915165913088 }, { target := 314, numerator := 149888421199573567079360495616 }, { target := 315, numerator := 154051988455117277276009398272 }, { target := 316, numerator := 154051988455117277276009398272 }, { target := 317, numerator := 170706257477292118062605008896 }, { target := 679, numerator := 15794696782189811623476068352 }, { target := 680, numerator := 17988404668605063237847744512 }, { target := 681, numerator := 14039730473057610331978727424 }, { target := 682, numerator := 188220136654428588513089814528 }, { target := 683, numerator := 16672179936755912269224738816 }, { target := 684, numerator := 14039730473057610331978727424 }, { target := 685, numerator := 16672179936755912269224738816 }, { target := 686, numerator := 16233438359472861946350403584 }, { target := 687, numerator := 613360725041704351378320654336 }, { target := 688, numerator := 16233438359472861946350403584 }, { target := 689, numerator := 188220136654428588513089814528 }, { target := 690, numerator := 613360725041704351378320654336 }, { target := 691, numerator := 15794696782189811623476068352 }, { target := 692, numerator := 16233438359472861946350403584 }, { target := 693, numerator := 16233438359472861946350403584 }, { target := 694, numerator := 17988404668605063237847744512 }, { target := 966, numerator := 133634043241079284124614656 }, { target := 967, numerator := 152194327024562518030811136 }, { target := 968, numerator := 118785816214292696999657472 }, { target := 969, numerator := 1592472348622861469151657984 }, { target := 970, numerator := 141058156754472577687093248 }, { target := 971, numerator := 118785816214292696999657472 }, { target := 972, numerator := 141058156754472577687093248 }, { target := 973, numerator := 137346099997775930905853952 }, { target := 974, numerator := 5189455345861912200172535808 }, { target := 975, numerator := 137346099997775930905853952 }, { target := 976, numerator := 1592472348622861469151657984 }, { target := 977, numerator := 5189455345861912200172535808 }, { target := 978, numerator := 133634043241079284124614656 }, { target := 979, numerator := 137346099997775930905853952 }, { target := 980, numerator := 137346099997775930905853952 }, { target := 981, numerator := 152194327024562518030811136 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 8377011216624756872926199808 }, { target := 260, numerator := 30597186891768125046600499200 }, { target := 262, numerator := 8377008394272913595364802560 }, { target := 353, numerator := 6282758412468567654694649856 }, { target := 356, numerator := 22947890168826093784950374400 }, { target := 358, numerator := 6282756295704685196523601920 }, { target := 379, numerator := 6631800546494599191066574848 }, { target := 382, numerator := 24222772955983098995225395200 }, { target := 384, numerator := 6631798312132723262997135360 }, { target := 524, numerator := 8551532283637772641112162304 }, { target := 527, numerator := 31234628285346627651738009600 }, { target := 529, numerator := 8551529402486932628601569280 }, { target := 620, numerator := 114485819960538343929991397376 }, { target := 623, numerator := 418161554187497708970206822400 }, { target := 625, numerator := 114485781388396485803318968320 }, { target := 646, numerator := 200175663863929086109298982912 }, { target := 649, numerator := 731145278434542488092724428800 }, { target := 651, numerator := 200175596421479831122571427840 }, { target := 695, numerator := 6108237345455551886508687360 }, { target := 698, numerator := 22310448775247591179812864000 }, { target := 700, numerator := 6108235287490666163286835200 }, { target := 721, numerator := 114485819960538343929991397376 }, { target := 724, numerator := 418161554187497708970206822400 }, { target := 726, numerator := 114485781388396485803318968320 }, { target := 735, numerator := 6457279479481583422880612352 }, { target := 738, numerator := 23585331562404596390087884800 }, { target := 740, numerator := 6457277303918704229760368640 }, { target := 836, numerator := 6631800546494599191066574848 }, { target := 839, numerator := 24222772955983098995225395200 }, { target := 841, numerator := 6631798312132723262997135360 }, { target := 862, numerator := 6631800546494599191066574848 }, { target := 865, numerator := 24222772955983098995225395200 }, { target := 867, numerator := 6631798312132723262997135360 }, { target := 911, numerator := 6457279479481583422880612352 }, { target := 914, numerator := 23585331562404596390087884800 }, { target := 916, numerator := 6457277303918704229760368640 }, { target := 937, numerator := 200175663863929086109298982912 }, { target := 940, numerator := 731145278434542488092724428800 }, { target := 942, numerator := 200175596421479831122571427840 }, { target := 951, numerator := 6457279479481583422880612352 }, { target := 954, numerator := 23585331562404596390087884800 }, { target := 956, numerator := 6457277303918704229760368640 }, { target := 982, numerator := 8377011216624756872926199808 }, { target := 985, numerator := 30597186891768125046600499200 }, { target := 987, numerator := 8377008394272913595364802560 }, { target := 996, numerator := 8551532283637772641112162304 }, { target := 999, numerator := 31234628285346627651738009600 }, { target := 1001, numerator := 8551529402486932628601569280 }]

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
    Slot7.Left2.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 805036329616531419782184960 }, { target := 57, numerator := 12075544944247971296732774400 }, { target := 58, numerator := 21199290013235327387597537280 }, { target := 59, numerator := 805036329616531419782184960 }, { target := 60, numerator := 13417272160275523663036416000 }, { target := 61, numerator := 805036329616531419782184960 }, { target := 62, numerator := 21199290013235327387597537280 }, { target := 63, numerator := 21065117291632572150967173120 }, { target := 64, numerator := 13417272160275523663036416000 }, { target := 65, numerator := 325100504443475938355372359680 }, { target := 66, numerator := 20796771848427061677706444800 }, { target := 67, numerator := 12075544944247971296732774400 }, { target := 68, numerator := 21199290013235327387597537280 }, { target := 69, numerator := 805036329616531419782184960 }, { target := 70, numerator := 20796771848427061677706444800 }, { target := 71, numerator := 805036329616531419782184960 }, { target := 72, numerator := 21199290013235327387597537280 }, { target := 73, numerator := 21199290013235327387597537280 }, { target := 74, numerator := 805036329616531419782184960 }, { target := 152, numerator := 31400751344145800135190773760 }, { target := 153, numerator := 471011270162187002027861606400 }, { target := 154, numerator := 826886452062506070226690375680 }, { target := 155, numerator := 31400751344145800135190773760 }, { target := 156, numerator := 523345855735763335586512896000 }, { target := 157, numerator := 31400751344145800135190773760 }, { target := 158, numerator := 826886452062506070226690375680 }, { target := 159, numerator := 821652993505148436870825246720 }, { target := 160, numerator := 523345855735763335586512896000 }, { target := 161, numerator := 12680670084477545621261207470080 }, { target := 162, numerator := 811186076390433170159094988800 }, { target := 163, numerator := 471011270162187002027861606400 }, { target := 164, numerator := 826886452062506070226690375680 }, { target := 165, numerator := 31400751344145800135190773760 }, { target := 166, numerator := 811186076390433170159094988800 }, { target := 167, numerator := 31400751344145800135190773760 }, { target := 168, numerator := 826886452062506070226690375680 }, { target := 169, numerator := 826886452062506070226690375680 }, { target := 170, numerator := 31400751344145800135190773760 }, { target := 283, numerator := 31400739826459969112789483520 }, { target := 284, numerator := 471011097396899536691842252800 }, { target := 285, numerator := 826886148763445853303456399360 }, { target := 286, numerator := 31400739826459969112789483520 }, { target := 287, numerator := 523345663774332818546491392000 }, { target := 288, numerator := 31400739826459969112789483520 }, { target := 289, numerator := 826886148763445853303456399360 }, { target := 290, numerator := 821652692125702525117991485440 }, { target := 291, numerator := 523345663774332818546491392000 }, { target := 292, numerator := 12680665433252084193381486428160 }, { target := 293, numerator := 811185778850215868747061657600 }, { target := 294, numerator := 471011097396899536691842252800 }, { target := 295, numerator := 826886148763445853303456399360 }, { target := 296, numerator := 31400739826459969112789483520 }, { target := 297, numerator := 811185778850215868747061657600 }, { target := 298, numerator := 31400739826459969112789483520 }, { target := 299, numerator := 826886148763445853303456399360 }, { target := 300, numerator := 826886148763445853303456399360 }, { target := 301, numerator := 31400739826459969112789483520 }]

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
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 797783750070436542126489600 }, { target := 112, numerator := 31117861692396738872711577600 }, { target := 115, numerator := 31117850278473843264926515200 }, { target := 122, numerator := 797787554711401744721510400 }, { target := 206, numerator := 11966756251056548131897344000 }, { target := 208, numerator := 466767925385951083090673664000 }, { target := 211, numerator := 466767754177107648973897728000 }, { target := 218, numerator := 11966813320671026170822656000 }, { target := 241, numerator := 21008305418521495609330892800 }, { target := 243, numerator := 819437024566447456981404876800 }, { target := 246, numerator := 819436723999811205976398233600 }, { target := 253, numerator := 21008405607400245944333107200 }, { target := 302, numerator := 797783750070436542126489600 }, { target := 304, numerator := 31117861692396738872711577600 }, { target := 307, numerator := 31117850278473843264926515200 }, { target := 314, numerator := 797787554711401744721510400 }, { target := 337, numerator := 13296395834507275702108160000 }, { target := 339, numerator := 518631028206612314545192960000 }, { target := 342, numerator := 518630837974564054415441920000 }, { target := 349, numerator := 13296459245190029078691840000 }, { target := 363, numerator := 797783750070436542126489600 }, { target := 365, numerator := 31117861692396738872711577600 }, { target := 368, numerator := 31117850278473843264926515200 }, { target := 375, numerator := 797787554711401744721510400 }, { target := 473, numerator := 21008305418521495609330892800 }, { target := 475, numerator := 819437024566447456981404876800 }, { target := 478, numerator := 819436723999811205976398233600 }, { target := 485, numerator := 21008405607400245944333107200 }, { target := 508, numerator := 20875341460176422852309811200 }, { target := 510, numerator := 814250714284381333835952947200 }, { target := 513, numerator := 814250415620065565432243814400 }, { target := 520, numerator := 20875441014948345653546188800 }, { target := 569, numerator := 13296395834507275702108160000 }, { target := 571, numerator := 518631028206612314545192960000 }, { target := 574, numerator := 518630837974564054415441920000 }, { target := 581, numerator := 13296459245190029078691840000 }, { target := 604, numerator := 322171671070111290262080716800 }, { target := 606, numerator := 12566429813446216381430025420800 }, { target := 609, numerator := 12566425204123687038486157721600 }, { target := 616, numerator := 322173207510954404576703283200 }, { target := 630, numerator := 20609413543486277338267648000 }, { target := 632, numerator := 803878093720249087545049088000 }, { target := 635, numerator := 803877798860574284343934976000 }, { target := 642, numerator := 20609511830044545071972352000 }, { target := 660, numerator := 805040168845141760582615040 }, { target := 661, numerator := 12075602532677126408739225600 }, { target := 662, numerator := 21199391112922066362008862720 }, { target := 663, numerator := 805040168845141760582615040 }, { target := 664, numerator := 13417336147419029343043584000 }, { target := 665, numerator := 805040168845141760582615040 }, { target := 666, numerator := 21199391112922066362008862720 }, { target := 667, numerator := 21065217751447876068578426880 }, { target := 668, numerator := 13417336147419029343043584000 }, { target := 669, numerator := 325102054851963080981946040320 }, { target := 670, numerator := 20796871028499495481717555200 }, { target := 671, numerator := 12075602532677126408739225600 }, { target := 672, numerator := 21199391112922066362008862720 }, { target := 673, numerator := 805040168845141760582615040 }, { target := 674, numerator := 20796871028499495481717555200 }, { target := 675, numerator := 805040168845141760582615040 }, { target := 676, numerator := 21199391112922066362008862720 }, { target := 677, numerator := 21199391112922066362008862720 }, { target := 678, numerator := 805040168845141760582615040 }]

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
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected,
    Slot8.Left17.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 8048500972835550721046740992 }, { target := 15, numerator := 6036375729626663040785055744 }, { target := 16, numerator := 6371729936828144320828669952 }, { target := 17, numerator := 8216178076436291361068548096 }, { target := 18, numerator := 109996179962085859854305460224 }, { target := 19, numerator := 192325637830049514105012748288 }, { target := 20, numerator := 5868698626025922400763248640 }, { target := 21, numerator := 109996179962085859854305460224 }, { target := 22, numerator := 6204052833227403680806862848 }, { target := 23, numerator := 6371729936828144320828669952 }, { target := 24, numerator := 6371729936828144320828669952 }, { target := 25, numerator := 6204052833227403680806862848 }, { target := 26, numerator := 192325637830049514105012748288 }, { target := 27, numerator := 6204052833227403680806862848 }, { target := 28, numerator := 8048500972835550721046740992 }, { target := 29, numerator := 8216178076436291361068548096 }, { target := 136, numerator := 29397297209738002495753420800 }, { target := 137, numerator := 22047972907303501871815065600 }, { target := 138, numerator := 23272860291042585309138124800 }, { target := 139, numerator := 30009740901607544214414950400 }, { target := 140, numerator := 401763061866419367441963417600 }, { target := 141, numerator := 702472914574364351304774451200 }, { target := 142, numerator := 21435529215433960153153536000 }, { target := 143, numerator := 401763061866419367441963417600 }, { target := 144, numerator := 22660416599173043590476595200 }, { target := 145, numerator := 23272860291042585309138124800 }, { target := 146, numerator := 23272860291042585309138124800 }, { target := 147, numerator := 22660416599173043590476595200 }, { target := 148, numerator := 702472914574364351304774451200 }, { target := 149, numerator := 22660416599173043590476595200 }, { target := 150, numerator := 29397297209738002495753420800 }, { target := 151, numerator := 30009740901607544214414950400 }, { target := 679, numerator := 11966756251056548131897344000 }, { target := 681, numerator := 466767925385951083090673664000 }, { target := 684, numerator := 466767754177107648973897728000 }, { target := 691, numerator := 11966813320671026170822656000 }, { target := 705, numerator := 21008305418521495609330892800 }, { target := 707, numerator := 819437024566447456981404876800 }, { target := 710, numerator := 819436723999811205976398233600 }, { target := 717, numerator := 21008405607400245944333107200 }, { target := 785, numerator := 797783750070436542126489600 }, { target := 787, numerator := 31117861692396738872711577600 }, { target := 790, numerator := 31117850278473843264926515200 }, { target := 797, numerator := 797787554711401744721510400 }, { target := 820, numerator := 20609413543486277338267648000 }, { target := 822, numerator := 803878093720249087545049088000 }, { target := 825, numerator := 803877798860574284343934976000 }, { target := 832, numerator := 20609511830044545071972352000 }, { target := 846, numerator := 797783750070436542126489600 }, { target := 848, numerator := 31117861692396738872711577600 }, { target := 851, numerator := 31117850278473843264926515200 }, { target := 858, numerator := 797787554711401744721510400 }, { target := 895, numerator := 21008305418521495609330892800 }, { target := 897, numerator := 819437024566447456981404876800 }, { target := 900, numerator := 819436723999811205976398233600 }, { target := 907, numerator := 21008405607400245944333107200 }, { target := 921, numerator := 21008305418521495609330892800 }, { target := 923, numerator := 819437024566447456981404876800 }, { target := 926, numerator := 819436723999811205976398233600 }, { target := 933, numerator := 21008405607400245944333107200 }, { target := 966, numerator := 797783750070436542126489600 }, { target := 968, numerator := 31117861692396738872711577600 }, { target := 971, numerator := 31117850278473843264926515200 }, { target := 978, numerator := 797787554711401744721510400 }]

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 137218098040648460327190528 }, { target := 57, numerator := 16218298216179873419391664128 }, { target := 59, numerator := 153908417170443356234745643008 }, { target := 67, numerator := 16218309339566549866251288576 }, { target := 74, numerator := 137218098040648460327190528 }, { target := 91, numerator := 156276167212960746483744768 }, { target := 92, numerator := 18470839635093744727640506368 }, { target := 94, numerator := 175284586221893822378460315648 }, { target := 102, numerator := 18470852303395237347675078656 }, { target := 109, numerator := 156276167212960746483744768 }, { target := 152, numerator := 121971642702798631401947136 }, { target := 153, numerator := 14416265081048776372792590336 }, { target := 155, numerator := 136807481929282983319773904896 }, { target := 163, numerator := 14416274968503599881112256512 }, { target := 170, numerator := 121971642702798631401947136 }, { target := 187, numerator := 1635182334984394152232353792 }, { target := 188, numerator := 193268053742810158247750664192 }, { target := 190, numerator := 1834075304614449995130718912512 }, { target := 198, numerator := 193268186296501385906161188864 }, { target := 205, numerator := 1635182334984394152232353792 }, { target := 222, numerator := 144841325709573374789812224 }, { target := 223, numerator := 17119314783745421942691201024 }, { target := 225, numerator := 162458884791023542692231512064 }, { target := 233, numerator := 17119326525098024858820804608 }, { target := 240, numerator := 144841325709573374789812224 }, { target := 267, numerator := 8048498261164171885742653440 }, { target := 268, numerator := 6036373695873128914306990080 }, { target := 269, numerator := 6371727790088302742879600640 }, { target := 270, numerator := 8216175308271758800028958720 }, { target := 271, numerator := 109996142902577015771816263680 }, { target := 272, numerator := 192325573032402190686392156160 }, { target := 273, numerator := 5868696648765542000020684800 }, { target := 274, numerator := 109996142902577015771816263680 }, { target := 275, numerator := 6204050742980715828593295360 }, { target := 276, numerator := 6371727790088302742879600640 }, { target := 277, numerator := 6371727790088302742879600640 }, { target := 278, numerator := 6204050742980715828593295360 }, { target := 279, numerator := 192325573032402190686392156160 }, { target := 280, numerator := 6204050742980715828593295360 }, { target := 281, numerator := 8048498261164171885742653440 }, { target := 282, numerator := 8216175308271758800028958720 }, { target := 283, numerator := 121971642702798631401947136 }, { target := 284, numerator := 14416265081048776372792590336 }, { target := 286, numerator := 136807481929282983319773904896 }, { target := 294, numerator := 14416274968503599881112256512 }, { target := 301, numerator := 121971642702798631401947136 }, { target := 318, numerator := 144841325709573374789812224 }, { target := 319, numerator := 17119314783745421942691201024 }, { target := 321, numerator := 162458884791023542692231512064 }, { target := 329, numerator := 17119326525098024858820804608 }, { target := 336, numerator := 144841325709573374789812224 }, { target := 419, numerator := 141029711875110917558501376 }, { target := 420, numerator := 16668806499962647681041432576 }, { target := 422, numerator := 158183650980733449463488577536 }, { target := 430, numerator := 16668817932332287362536046592 }, { target := 437, numerator := 141029711875110917558501376 }, { target := 454, numerator := 5328636140578515209372565504 }, { target := 455, numerator := 629810580728318417786376290304 }, { target := 457, numerator := 5976776866785550333782622470144 }, { target := 465, numerator := 629811012686501019806091706368 }, { target := 472, numerator := 5328636140578515209372565504 }]

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
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 299813603264428035327131648 }, { target := 5, numerator := 7263226324244692081634705408 }, { target := 6, numerator := 5503030330885792003262513152 }, { target := 7, numerator := 6131671757085399174109724672 }, { target := 8, numerator := 299813603264428035327131648 }, { target := 9, numerator := 6131671757085399174109724672 }, { target := 10, numerator := 6122000350528482140712075264 }, { target := 11, numerator := 299813603264428035327131648 }, { target := 12, numerator := 7263226324244692081634705408 }, { target := 13, numerator := 299813603264428035327131648 }, { target := 14, numerator := 10746579646939213040975872 }, { target := 15, numerator := 1884849105508799332898308096 }, { target := 20, numerator := 1884849331481414235840315392 }, { target := 28, numerator := 10746353674324310098968576 }, { target := 40, numerator := 214931592938784260819517440 }, { target := 41, numerator := 37696982110175986657966161920 }, { target := 46, numerator := 37696986629628284716806307840 }, { target := 54, numerator := 214927073486486201979371520 }, { target := 126, numerator := 299813603264428035327131648 }, { target := 127, numerator := 7263226324244692081634705408 }, { target := 128, numerator := 5503030330885792003262513152 }, { target := 129, numerator := 6131671757085399174109724672 }, { target := 130, numerator := 299813603264428035327131648 }, { target := 131, numerator := 6131671757085399174109724672 }, { target := 132, numerator := 6122000350528482140712075264 }, { target := 133, numerator := 299813603264428035327131648 }, { target := 134, numerator := 7263226324244692081634705408 }, { target := 135, numerator := 299813603264428035327131648 }, { target := 489, numerator := 141029711875110917558501376 }, { target := 490, numerator := 16668806499962647681041432576 }, { target := 492, numerator := 158183650980733449463488577536 }, { target := 500, numerator := 16668817932332287362536046592 }, { target := 507, numerator := 141029711875110917558501376 }, { target := 550, numerator := 1635182334984394152232353792 }, { target := 551, numerator := 193268053742810158247750664192 }, { target := 553, numerator := 1834075304614449995130718912512 }, { target := 561, numerator := 193268186296501385906161188864 }, { target := 568, numerator := 1635182334984394152232353792 }, { target := 585, numerator := 5328636140578515209372565504 }, { target := 586, numerator := 629810580728318417786376290304 }, { target := 588, numerator := 5976776866785550333782622470144 }, { target := 596, numerator := 629811012686501019806091706368 }, { target := 603, numerator := 5328636140578515209372565504 }, { target := 660, numerator := 137218098040648460327190528 }, { target := 661, numerator := 16218298216179873419391664128 }, { target := 663, numerator := 153908417170443356234745643008 }, { target := 671, numerator := 16218309339566549866251288576 }, { target := 678, numerator := 137218098040648460327190528 }, { target := 766, numerator := 141029711875110917558501376 }, { target := 767, numerator := 16668806499962647681041432576 }, { target := 769, numerator := 158183650980733449463488577536 }, { target := 777, numerator := 16668817932332287362536046592 }, { target := 784, numerator := 141029711875110917558501376 }, { target := 801, numerator := 141029711875110917558501376 }, { target := 802, numerator := 16668806499962647681041432576 }, { target := 804, numerator := 158183650980733449463488577536 }, { target := 812, numerator := 16668817932332287362536046592 }, { target := 819, numerator := 141029711875110917558501376 }, { target := 876, numerator := 156276167212960746483744768 }, { target := 877, numerator := 18470839635093744727640506368 }, { target := 879, numerator := 175284586221893822378460315648 }, { target := 887, numerator := 18470852303395237347675078656 }, { target := 894, numerator := 156276167212960746483744768 }]

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
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 75, numerator := 11130386062901327792439296 }, { target := 76, numerator := 1952165144991256451930390528 }, { target := 81, numerator := 1952165379034321887120326656 }, { target := 89, numerator := 11130152019835892602503168 }, { target := 136, numerator := 199963142716261785512443904 }, { target := 137, numerator := 35071656570360159015714947072 }, { target := 142, numerator := 35071660775064886316885868544 }, { target := 150, numerator := 199958938011534484341522432 }, { target := 171, numerator := 299369004450449506141470720 }, { target := 172, numerator := 52506510796316552845024296960 }, { target := 177, numerator := 52506517091267967998408785920 }, { target := 185, numerator := 299362709499034352756981760 }, { target := 267, numerator := 10746579646939213040975872 }, { target := 268, numerator := 1884849105508799332898308096 }, { target := 273, numerator := 1884849331481414235840315392 }, { target := 281, numerator := 10746353674324310098968576 }, { target := 403, numerator := 299752810866411620892934144 }, { target := 404, numerator := 52573826835799009964056379392 }, { target := 409, numerator := 52573833138820875649688797184 }, { target := 417, numerator := 299746507844545935260516352 }, { target := 438, numerator := 299752810866411620892934144 }, { target := 439, numerator := 52573826835799009964056379392 }, { target := 444, numerator := 52573833138820875649688797184 }, { target := 452, numerator := 299746507844545935260516352 }, { target := 534, numerator := 214547786522822146068054016 }, { target := 535, numerator := 37629666070693529538934079488 }, { target := 540, numerator := 37629670582075377065526296576 }, { target := 548, numerator := 214543275140974619475836928 }, { target := 750, numerator := 11130386062901327792439296 }, { target := 751, numerator := 1952165144991256451930390528 }, { target := 756, numerator := 1952165379034321887120326656 }, { target := 764, numerator := 11130152019835892602503168 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent1
