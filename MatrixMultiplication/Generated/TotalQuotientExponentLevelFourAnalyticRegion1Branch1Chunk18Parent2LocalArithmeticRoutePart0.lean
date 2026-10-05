import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 110536247797089048421466112 }, { target := 201, numerator := 125888504435573638480003072 }, { target := 202, numerator := 98254442486301376374636544 }, { target := 203, numerator := 1317223619581977827022471168 }, { target := 204, numerator := 116677150452482884444880896 }, { target := 205, numerator := 98254442486301376374636544 }, { target := 206, numerator := 116677150452482884444880896 }, { target := 207, numerator := 113606699124785966433173504 }, { target := 208, numerator := 4292490956120291380366934016 }, { target := 209, numerator := 113606699124785966433173504 }, { target := 210, numerator := 1317223619581977827022471168 }, { target := 211, numerator := 4292490956120291380366934016 }, { target := 212, numerator := 110536247797089048421466112 }, { target := 213, numerator := 113606699124785966433173504 }, { target := 214, numerator := 113606699124785966433173504 }, { target := 215, numerator := 125888504435573638480003072 }, { target := 296, numerator := 19387019370947650281239740416 }, { target := 297, numerator := 22079660950245935042523037696 }, { target := 298, numerator := 17232906107509022472213102592 }, { target := 299, numerator := 231028647503792832518106906624 }, { target := 300, numerator := 20464076002666964185753059328 }, { target := 301, numerator := 17232906107509022472213102592 }, { target := 302, numerator := 20464076002666964185753059328 }, { target := 303, numerator := 19925547686807307233496399872 }, { target := 304, numerator := 752862585571800419254809919488 }, { target := 305, numerator := 19925547686807307233496399872 }, { target := 306, numerator := 231028647503792832518106906624 }, { target := 307, numerator := 752862585571800419254809919488 }, { target := 308, numerator := 19387019370947650281239740416 }, { target := 309, numerator := 19925547686807307233496399872 }, { target := 310, numerator := 19925547686807307233496399872 }, { target := 311, numerator := 22079660950245935042523037696 }, { target := 659, numerator := 19387021695237403568643244032 }, { target := 660, numerator := 22079663597353709619843694592 }, { target := 661, numerator := 17232908173544358727682883584 }, { target := 662, numerator := 231028675201579059192998658048 }, { target := 663, numerator := 20464078456083925989123424256 }, { target := 664, numerator := 17232908173544358727682883584 }, { target := 665, numerator := 20464078456083925989123424256 }, { target := 666, numerator := 19925550075660664778883334144 }, { target := 667, numerator := 752862675831719171915645976576 }, { target := 668, numerator := 19925550075660664778883334144 }, { target := 669, numerator := 231028675201579059192998658048 }, { target := 670, numerator := 752862675831719171915645976576 }, { target := 671, numerator := 19387021695237403568643244032 }, { target := 672, numerator := 19925550075660664778883334144 }, { target := 673, numerator := 19925550075660664778883334144 }, { target := 674, numerator := 22079663597353709619843694592 }, { target := 1036, numerator := 110533923507335761017962496 }, { target := 1037, numerator := 125885857327799061159346176 }, { target := 1038, numerator := 98252376450965120904855552 }, { target := 1039, numerator := 1317195921795751152130719744 }, { target := 1040, numerator := 116674697035521081074515968 }, { target := 1041, numerator := 98252376450965120904855552 }, { target := 1042, numerator := 116674697035521081074515968 }, { target := 1043, numerator := 113604310271428421046239232 }, { target := 1044, numerator := 4292400696201538719530876928 }, { target := 1045, numerator := 113604310271428421046239232 }, { target := 1046, numerator := 1317195921795751152130719744 }, { target := 1047, numerator := 4292400696201538719530876928 }, { target := 1048, numerator := 110533923507335761017962496 }, { target := 1049, numerator := 113604310271428421046239232 }, { target := 1050, numerator := 113604310271428421046239232 }, { target := 1051, numerator := 125885857327799061159346176 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 47958066603758976805896192 }, { target := 72, numerator := 719370999056384652088442880 }, { target := 73, numerator := 1262895753898986389221933056 }, { target := 74, numerator := 47958066603758976805896192 }, { target := 75, numerator := 799301110062649613431603200 }, { target := 76, numerator := 47958066603758976805896192 }, { target := 77, numerator := 1262895753898986389221933056 }, { target := 78, numerator := 1254902742798359893087617024 }, { target := 79, numerator := 799301110062649613431603200 }, { target := 80, numerator := 19367065896818000133447745536 }, { target := 81, numerator := 1238916720597106900818984960 }, { target := 82, numerator := 719370999056384652088442880 }, { target := 83, numerator := 1262895753898986389221933056 }, { target := 84, numerator := 47958066603758976805896192 }, { target := 85, numerator := 1238916720597106900818984960 }, { target := 86, numerator := 47958066603758976805896192 }, { target := 87, numerator := 1262895753898986389221933056 }, { target := 88, numerator := 1262895753898986389221933056 }, { target := 89, numerator := 47958066603758976805896192 }, { target := 347, numerator := 742570030231851405810860032 }, { target := 350, numerator := 2712250635422256182643916800 }, { target := 352, numerator := 742569780047884906125066240 }, { target := 614, numerator := 17989357829165174379482447872 }, { target := 617, numerator := 65706458942003690102115532800 }, { target := 619, numerator := 17989351768256824661287895040 }, { target := 710, numerator := 13629753135545917738915463168 }, { target := 713, numerator := 49782922953395605416915763200 }, { target := 715, numerator := 13629748543459564889843957760 }, { target := 736, numerator := 15186754811838509396260814848 }, { target := 739, numerator := 55469900092184207090201395200 }, { target := 741, numerator := 15186749695172871951073935360 }, { target := 881, numerator := 742570030231851405810860032 }, { target := 884, numerator := 2712250635422256182643916800 }, { target := 886, numerator := 742569780047884906125066240 }, { target := 977, numerator := 15186754811838509396260814848 }, { target := 980, numerator := 55469900092184207090201395200 }, { target := 982, numerator := 15186749695172871951073935360 }, { target := 1003, numerator := 15162800939895546447686270976 }, { target := 1006, numerator := 55382408136202843987535462400 }, { target := 1008, numerator := 15162795831300359534747320320 }, { target := 1052, numerator := 742570030231851405810860032 }, { target := 1055, numerator := 2712250635422256182643916800 }, { target := 1057, numerator := 742569780047884906125066240 }, { target := 1078, numerator := 17989357829165174379482447872 }, { target := 1081, numerator := 65706458942003690102115532800 }, { target := 1083, numerator := 17989351768256824661287895040 }, { target := 1092, numerator := 742570030231851405810860032 }, { target := 1095, numerator := 2712250635422256182643916800 }, { target := 1097, numerator := 742569780047884906125066240 }]

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
    Slot6.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 5668335570580279142847086592 }, { target := 147, numerator := 85025033558704187142706298880 }, { target := 148, numerator := 149266170025280684094973280256 }, { target := 149, numerator := 5668335570580279142847086592 }, { target := 150, numerator := 94472259509671319047451443200 }, { target := 151, numerator := 5668335570580279142847086592 }, { target := 152, numerator := 149266170025280684094973280256 }, { target := 153, numerator := 148321447430183970904498765824 }, { target := 154, numerator := 94472259509671319047451443200 }, { target := 155, numerator := 2289062847919336060519748468736 }, { target := 156, numerator := 146432002239990544523549736960 }, { target := 157, numerator := 85025033558704187142706298880 }, { target := 158, numerator := 149266170025280684094973280256 }, { target := 159, numerator := 5668335570580279142847086592 }, { target := 160, numerator := 146432002239990544523549736960 }, { target := 161, numerator := 5668335570580279142847086592 }, { target := 162, numerator := 149266170025280684094973280256 }, { target := 163, numerator := 149266170025280684094973280256 }, { target := 164, numerator := 5668335570580279142847086592 }, { target := 242, numerator := 53791374657829083460153638912 }, { target := 243, numerator := 806870619867436251902304583680 }, { target := 244, numerator := 1416506199322832531117379158016 }, { target := 245, numerator := 53791374657829083460153638912 }, { target := 246, numerator := 896522910963818057669227315200 }, { target := 247, numerator := 53791374657829083460153638912 }, { target := 248, numerator := 1416506199322832531117379158016 }, { target := 249, numerator := 1407540970213194350540686884864 }, { target := 250, numerator := 896522910963818057669227315200 }, { target := 251, numerator := 21722750132653311537325377847296 }, { target := 252, numerator := 1389610511993917989387302338560 }, { target := 253, numerator := 806870619867436251902304583680 }, { target := 254, numerator := 1416506199322832531117379158016 }, { target := 255, numerator := 53791374657829083460153638912 }, { target := 256, numerator := 1389610511993917989387302338560 }, { target := 257, numerator := 53791374657829083460153638912 }, { target := 258, numerator := 1416506199322832531117379158016 }, { target := 259, numerator := 1416506199322832531117379158016 }, { target := 260, numerator := 53791374657829083460153638912 }, { target := 640, numerator := 5668339458231592677135089664 }, { target := 641, numerator := 85025091873473890157026344960 }, { target := 642, numerator := 149266272400098607164557361152 }, { target := 643, numerator := 5668339458231592677135089664 }, { target := 644, numerator := 94472324303859877952251494400 }, { target := 645, numerator := 5668339458231592677135089664 }, { target := 646, numerator := 149266272400098607164557361152 }, { target := 647, numerator := 148321549157060008385034846208 }, { target := 648, numerator := 94472324303859877952251494400 }, { target := 649, numerator := 2289064417882524842783053709312 }, { target := 650, numerator := 146432102670982810825989816320 }, { target := 651, numerator := 85025091873473890157026344960 }, { target := 652, numerator := 149266272400098607164557361152 }, { target := 653, numerator := 5668339458231592677135089664 }, { target := 654, numerator := 146432102670982810825989816320 }, { target := 655, numerator := 5668339458231592677135089664 }, { target := 656, numerator := 149266272400098607164557361152 }, { target := 657, numerator := 149266272400098607164557361152 }, { target := 658, numerator := 5668339458231592677135089664 }]

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
    Slot6.Left18.expected,
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
    Slot7.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 2541303872951645130555654144 }, { target := 202, numerator := 99124533972871066372710334464 }, { target := 205, numerator := 99124497614338497091184099328 }, { target := 212, numerator := 2541315992462501557731065856 }, { target := 296, numerator := 1905977904713733847916740608 }, { target := 298, numerator := 74343400479653299779532750848 }, { target := 301, numerator := 74343373210753872818388074496 }, { target := 308, numerator := 1905986994346876168298299392 }, { target := 331, numerator := 2011865566086719061689892864 }, { target := 333, numerator := 78473589395189594211729014784 }, { target := 336, numerator := 78473560611351310197187411968 }, { target := 343, numerator := 2011875160699480399870427136 }, { target := 467, numerator := 2594247703638137737442230272 }, { target := 469, numerator := 101189628430639213588808466432 }, { target := 472, numerator := 101189591314637215780583768064 }, { target := 479, numerator := 2594260075638803673517129728 }, { target := 563, numerator := 34731152930339150117593939968 }, { target := 565, numerator := 1354701964295904573760374571008 }, { target := 568, numerator := 1354701467395959460246182690816 }, { target := 575, numerator := 34731318563654187955657900032 }, { target := 598, numerator := 60726573797407020098902818816 }, { target := 600, numerator := 2368663343060064856864557367296 }, { target := 603, numerator := 2368662474242630336741420040192 }, { target := 610, numerator := 60726863403218526806615261184 }, { target := 659, numerator := 1853034074027241241030164480 }, { target := 661, numerator := 72278306021885152563434618880 }, { target := 664, numerator := 72278279510455154128988405760 }, { target := 671, numerator := 1853042911170574052512235520 }, { target := 694, numerator := 34731152930339150117593939968 }, { target := 696, numerator := 1354701964295904573760374571008 }, { target := 699, numerator := 1354701467395959460246182690816 }, { target := 706, numerator := 34731318563654187955657900032 }, { target := 720, numerator := 1958921735400226454803316736 }, { target := 722, numerator := 76408494937421446995630882816 }, { target := 725, numerator := 76408466911052591507787743232 }, { target := 732, numerator := 1958931077523178284084363264 }, { target := 830, numerator := 2011865566086719061689892864 }, { target := 832, numerator := 78473589395189594211729014784 }, { target := 835, numerator := 78473560611351310197187411968 }, { target := 842, numerator := 2011875160699480399870427136 }, { target := 865, numerator := 2011865566086719061689892864 }, { target := 867, numerator := 78473589395189594211729014784 }, { target := 870, numerator := 78473560611351310197187411968 }, { target := 877, numerator := 2011875160699480399870427136 }, { target := 1017, numerator := 47958066603758976805896192 }, { target := 1018, numerator := 719370999056384652088442880 }, { target := 1019, numerator := 1262895753898986389221933056 }, { target := 1020, numerator := 47958066603758976805896192 }, { target := 1021, numerator := 799301110062649613431603200 }, { target := 1022, numerator := 47958066603758976805896192 }, { target := 1023, numerator := 1262895753898986389221933056 }, { target := 1024, numerator := 1254902742798359893087617024 }, { target := 1025, numerator := 799301110062649613431603200 }, { target := 1026, numerator := 19367065896818000133447745536 }, { target := 1027, numerator := 1238916720597106900818984960 }, { target := 1028, numerator := 719370999056384652088442880 }, { target := 1029, numerator := 1262895753898986389221933056 }, { target := 1030, numerator := 47958066603758976805896192 }, { target := 1031, numerator := 1238916720597106900818984960 }, { target := 1032, numerator := 47958066603758976805896192 }, { target := 1033, numerator := 1262895753898986389221933056 }, { target := 1034, numerator := 1262895753898986389221933056 }, { target := 1035, numerator := 47958066603758976805896192 }]

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
    Slot7.Left11.expected,
    Slot7.Left12.expected,
    Slot7.Left13.expected,
    Slot7.Left14.expected,
    Slot7.Left15.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2552908000225396934804766720 }, { target := 30, numerator := 1914681000169047701103575040 }, { target := 31, numerator := 2021052166845105906720440320 }, { target := 32, numerator := 2606093583563426037613199360 }, { target := 33, numerator := 34889742669747091442331811840 }, { target := 34, numerator := 61003864088719380921272238080 }, { target := 35, numerator := 1861495416831018598295142400 }, { target := 36, numerator := 34889742669747091442331811840 }, { target := 37, numerator := 1967866583507076803912007680 }, { target := 38, numerator := 2021052166845105906720440320 }, { target := 39, numerator := 2021052166845105906720440320 }, { target := 40, numerator := 1967866583507076803912007680 }, { target := 41, numerator := 61003864088719380921272238080 }, { target := 42, numerator := 1967866583507076803912007680 }, { target := 43, numerator := 2552908000225396934804766720 }, { target := 44, numerator := 2606093583563426037613199360 }, { target := 104, numerator := 99577157415669564392677048320 }, { target := 105, numerator := 74682868061752173294507786240 }, { target := 106, numerator := 78831916287405071810869329920 }, { target := 107, numerator := 101651681528496013650857820160 }, { target := 108, numerator := 1360887818014150713366586327040 }, { target := 109, numerator := 2379479157411937299133345300480 }, { target := 110, numerator := 72608343948925724036327014400 }, { target := 111, numerator := 1360887818014150713366586327040 }, { target := 112, numerator := 76757392174578622552688558080 }, { target := 113, numerator := 78831916287405071810869329920 }, { target := 114, numerator := 78831916287405071810869329920 }, { target := 115, numerator := 76757392174578622552688558080 }, { target := 116, numerator := 2379479157411937299133345300480 }, { target := 117, numerator := 76757392174578622552688558080 }, { target := 118, numerator := 99577157415669564392677048320 }, { target := 119, numerator := 101651681528496013650857820160 }, { target := 926, numerator := 1958921735400226454803316736 }, { target := 928, numerator := 76408494937421446995630882816 }, { target := 931, numerator := 76408466911052591507787743232 }, { target := 938, numerator := 1958931077523178284084363264 }, { target := 961, numerator := 60726573797407020098902818816 }, { target := 963, numerator := 2368663343060064856864557367296 }, { target := 966, numerator := 2368662474242630336741420040192 }, { target := 973, numerator := 60726863403218526806615261184 }, { target := 987, numerator := 1958921735400226454803316736 }, { target := 989, numerator := 76408494937421446995630882816 }, { target := 992, numerator := 76408466911052591507787743232 }, { target := 999, numerator := 1958931077523178284084363264 }, { target := 1036, numerator := 2541303872951645130555654144 }, { target := 1038, numerator := 99124533972871066372710334464 }, { target := 1041, numerator := 99124497614338497091184099328 }, { target := 1048, numerator := 2541315992462501557731065856 }, { target := 1062, numerator := 2594247703638137737442230272 }, { target := 1064, numerator := 101189628430639213588808466432 }, { target := 1067, numerator := 101189591314637215780583768064 }, { target := 1074, numerator := 2594260075638803673517129728 }]

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
    Slot9.Left4.expected,
    Slot9.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 47872731965673996420120576 }, { target := 72, numerator := 5658249564226933450422091776 }, { target := 74, numerator := 53695660468046469432644468736 }, { target := 82, numerator := 5658253444960717957069012992 }, { target := 89, numerator := 47872731965673996420120576 }, { target := 146, numerator := 718090979485109946301808640 }, { target := 147, numerator := 84873743463404001756331376640 }, { target := 149, numerator := 805434907020697041489667031040 }, { target := 157, numerator := 84873801674410769356035194880 }, { target := 164, numerator := 718090979485109946301808640 }, { target := 181, numerator := 1260648608429415239063175168 }, { target := 182, numerator := 149000571857975914194448416768 }, { target := 184, numerator := 1413985725658557028392971010048 }, { target := 192, numerator := 149000674050632239536150675456 }, { target := 199, numerator := 1260648608429415239063175168 }, { target := 226, numerator := 99577120891116298447764848640 }, { target := 227, numerator := 74682840668337223835823636480 }, { target := 228, numerator := 78831887372133736271147171840 }, { target := 229, numerator := 101651644243014554665426616320 }, { target := 230, numerator := 1360887318845256078786119598080 }, { target := 231, numerator := 2379478284627299881658047528960 }, { target := 232, numerator := 72608317316438967618161868800 }, { target := 233, numerator := 1360887318845256078786119598080 }, { target := 234, numerator := 76757364020235480053485404160 }, { target := 235, numerator := 78831887372133736271147171840 }, { target := 236, numerator := 78831887372133736271147171840 }, { target := 237, numerator := 76757364020235480053485404160 }, { target := 238, numerator := 2379478284627299881658047528960 }, { target := 239, numerator := 76757364020235480053485404160 }, { target := 240, numerator := 99577120891116298447764848640 }, { target := 241, numerator := 101651644243014554665426616320 }, { target := 242, numerator := 47872731965673996420120576 }, { target := 243, numerator := 5658249564226933450422091776 }, { target := 245, numerator := 53695660468046469432644468736 }, { target := 253, numerator := 5658253444960717957069012992 }, { target := 260, numerator := 47872731965673996420120576 }, { target := 277, numerator := 797878866094566607002009600 }, { target := 278, numerator := 94304159403782224173701529600 }, { target := 280, numerator := 894927674467441157210741145600 }, { target := 288, numerator := 94304224082678632617816883200 }, { target := 295, numerator := 797878866094566607002009600 }, { target := 312, numerator := 47872731965673996420120576 }, { target := 313, numerator := 5658249564226933450422091776 }, { target := 315, numerator := 53695660468046469432644468736 }, { target := 323, numerator := 5658253444960717957069012992 }, { target := 330, numerator := 47872731965673996420120576 }, { target := 624, numerator := 2552920175076485583108833280 }, { target := 625, numerator := 1914690131307364187331624960 }, { target := 626, numerator := 2021061805268884419961159680 }, { target := 627, numerator := 2606106012057245699423600640 }, { target := 628, numerator := 34889909059378636302487388160 }, { target := 629, numerator := 61004155016931853413038161920 }, { target := 630, numerator := 1861504294326604071016857600 }, { target := 631, numerator := 34889909059378636302487388160 }, { target := 632, numerator := 1967875968288124303646392320 }, { target := 633, numerator := 2021061805268884419961159680 }, { target := 634, numerator := 2021061805268884419961159680 }, { target := 635, numerator := 1967875968288124303646392320 }, { target := 636, numerator := 61004155016931853413038161920 }, { target := 637, numerator := 1967875968288124303646392320 }, { target := 638, numerator := 2552920175076485583108833280 }, { target := 639, numerator := 2606106012057245699423600640 }]

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
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot9.Left16.expected,
    Slot9.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 1260648608429415239063175168 }, { target := 414, numerator := 149000571857975914194448416768 }, { target := 416, numerator := 1413985725658557028392971010048 }, { target := 424, numerator := 149000674050632239536150675456 }, { target := 431, numerator := 1260648608429415239063175168 }, { target := 448, numerator := 1252669819768469572993155072 }, { target := 449, numerator := 148057530263938091952711401472 }, { target := 451, numerator := 1405036448913882616820863598592 }, { target := 459, numerator := 148057631809805453209972506624 }, { target := 466, numerator := 1252669819768469572993155072 }, { target := 509, numerator := 797878866094566607002009600 }, { target := 510, numerator := 94304159403782224173701529600 }, { target := 512, numerator := 894927674467441157210741145600 }, { target := 520, numerator := 94304224082678632617816883200 }, { target := 527, numerator := 797878866094566607002009600 }, { target := 544, numerator := 19332604925471348887658692608 }, { target := 545, numerator := 2284989782353643291728788062208 }, { target := 547, numerator := 21684097552346099239216257957888 }, { target := 555, numerator := 2284991349523303268329703079936 }, { target := 562, numerator := 19332604925471348887658692608 }, { target := 579, numerator := 1236712242446578240853114880 }, { target := 580, numerator := 146171447075862447469237370880 }, { target := 582, numerator := 1387137895424533793676648775680 }, { target := 590, numerator := 146171547328151880557616168960 }, { target := 597, numerator := 1236712242446578240853114880 }, { target := 640, numerator := 718090979485109946301808640 }, { target := 641, numerator := 84873743463404001756331376640 }, { target := 643, numerator := 805434907020697041489667031040 }, { target := 651, numerator := 84873801674410769356035194880 }, { target := 658, numerator := 718090979485109946301808640 }, { target := 675, numerator := 1260648608429415239063175168 }, { target := 676, numerator := 149000571857975914194448416768 }, { target := 678, numerator := 1413985725658557028392971010048 }, { target := 686, numerator := 149000674050632239536150675456 }, { target := 693, numerator := 1260648608429415239063175168 }, { target := 776, numerator := 47872731965673996420120576 }, { target := 777, numerator := 5658249564226933450422091776 }, { target := 779, numerator := 53695660468046469432644468736 }, { target := 787, numerator := 5658253444960717957069012992 }, { target := 794, numerator := 47872731965673996420120576 }, { target := 811, numerator := 1236712242446578240853114880 }, { target := 812, numerator := 146171447075862447469237370880 }, { target := 814, numerator := 1387137895424533793676648775680 }, { target := 822, numerator := 146171547328151880557616168960 }, { target := 829, numerator := 1236712242446578240853114880 }, { target := 846, numerator := 47872731965673996420120576 }, { target := 847, numerator := 5658249564226933450422091776 }, { target := 849, numerator := 53695660468046469432644468736 }, { target := 857, numerator := 5658253444960717957069012992 }, { target := 864, numerator := 47872731965673996420120576 }, { target := 907, numerator := 1260648608429415239063175168 }, { target := 908, numerator := 149000571857975914194448416768 }, { target := 910, numerator := 1413985725658557028392971010048 }, { target := 918, numerator := 149000674050632239536150675456 }, { target := 925, numerator := 1260648608429415239063175168 }, { target := 942, numerator := 1260648608429415239063175168 }, { target := 943, numerator := 149000571857975914194448416768 }, { target := 945, numerator := 1413985725658557028392971010048 }, { target := 953, numerator := 149000674050632239536150675456 }, { target := 960, numerator := 1260648608429415239063175168 }]

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
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
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
  [{ target := 5, numerator := 742570030231851405810860032 }, { target := 6, numerator := 17989357829165174379482447872 }, { target := 7, numerator := 13629753135545917738915463168 }, { target := 8, numerator := 15186754811838509396260814848 }, { target := 9, numerator := 742570030231851405810860032 }, { target := 10, numerator := 15186754811838509396260814848 }, { target := 11, numerator := 15162800939895546447686270976 }, { target := 12, numerator := 742570030231851405810860032 }, { target := 13, numerator := 17989357829165174379482447872 }, { target := 14, numerator := 742570030231851405810860032 }, { target := 29, numerator := 102640801525868402105647104 }, { target := 30, numerator := 18002232273022818118294044672 }, { target := 35, numerator := 18002234431291874742311583744 }, { target := 43, numerator := 102638643256811778088108032 }, { target := 55, numerator := 116896468404461235731431424 }, { target := 56, numerator := 20502542310942653968057106432 }, { target := 61, numerator := 20502544768971301789854859264 }, { target := 69, numerator := 116894010375813413933678592 }, { target := 94, numerator := 2712250635422256182643916800 }, { target := 95, numerator := 65706458942003690102115532800 }, { target := 96, numerator := 49782922953395605416915763200 }, { target := 97, numerator := 55469900092184207090201395200 }, { target := 98, numerator := 2712250635422256182643916800 }, { target := 99, numerator := 55469900092184207090201395200 }, { target := 100, numerator := 55382408136202843987535462400 }, { target := 101, numerator := 2712250635422256182643916800 }, { target := 102, numerator := 65706458942003690102115532800 }, { target := 103, numerator := 2712250635422256182643916800 }, { target := 104, numerator := 91236268022994135205019648 }, { target := 105, numerator := 16001984242686949438483595264 }, { target := 110, numerator := 16001986161148333104276963328 }, { target := 118, numerator := 91234349561610469411651584 }, { target := 130, numerator := 1223136218183265125092294656 }, { target := 131, numerator := 214526601253521915909670699008 }, { target := 136, numerator := 214526626972894840679213039616 }, { target := 144, numerator := 1223110498810340355549954048 }, { target := 165, numerator := 108343068277305535555960832 }, { target := 166, numerator := 19002356288190752458199269376 }, { target := 171, numerator := 19002358566363645561328893952 }, { target := 179, numerator := 108340790104412432426336256 }, { target := 216, numerator := 742569780047884906125066240 }, { target := 217, numerator := 17989351768256824661287895040 }, { target := 218, numerator := 13629748543459564889843957760 }, { target := 219, numerator := 15186749695172871951073935360 }, { target := 220, numerator := 742569780047884906125066240 }, { target := 221, numerator := 15186749695172871951073935360 }, { target := 222, numerator := 15162795831300359534747320320 }, { target := 223, numerator := 742569780047884906125066240 }, { target := 224, numerator := 17989351768256824661287895040 }, { target := 225, numerator := 742569780047884906125066240 }, { target := 226, numerator := 91236268022994135205019648 }, { target := 227, numerator := 16001984242686949438483595264 }, { target := 232, numerator := 16001986161148333104276963328 }, { target := 240, numerator := 91234349561610469411651584 }, { target := 261, numerator := 108343068277305535555960832 }, { target := 262, numerator := 19002356288190752458199269376 }, { target := 267, numerator := 19002358566363645561328893952 }, { target := 275, numerator := 108340790104412432426336256 }, { target := 1017, numerator := 47872731965673996420120576 }, { target := 1018, numerator := 5658249564226933450422091776 }, { target := 1020, numerator := 53695660468046469432644468736 }, { target := 1028, numerator := 5658253444960717957069012992 }, { target := 1035, numerator := 47872731965673996420120576 }]

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
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 11473694958092622437023744 }, { target := 7, numerator := 518590138692529928110342144 }, { target := 12, numerator := 11534933536731319721000960 }, { target := 19, numerator := 229473899161852448740474880 }, { target := 21, numerator := 10371802773850598562206842880 }, { target := 26, numerator := 230698670734626394420019200 }, { target := 45, numerator := 11883469778024501809774592 }, { target := 47, numerator := 537111215074405996971425792 }, { target := 52, numerator := 11946895448757438282465280 }, { target := 94, numerator := 213492681184509153203191808 }, { target := 96, numerator := 9649480794957431876624580608 }, { target := 101, numerator := 214632156165607770522910720 }, { target := 120, numerator := 319624359546865910745661440 }, { target := 122, numerator := 14446439577863333711645245440 }, { target := 127, numerator := 321330291380372477942169600 }, { target := 216, numerator := 11473694958092622437023744 }, { target := 218, numerator := 518590138692529928110342144 }, { target := 223, numerator := 11534933536731319721000960 }, { target := 361, numerator := 320034134366797790118412288 }, { target := 363, numerator := 14464960654245209780506329088 }, { target := 368, numerator := 321742253292398596503633920 }, { target := 371, numerator := 105491934901586968830803968 }, { target := 372, numerator := 18502294280606785288246657024 }, { target := 377, numerator := 18502296498827760151820238848 }, { target := 385, numerator := 105489716680612105257222144 }, { target := 387, numerator := 320034134366797790118412288 }, { target := 389, numerator := 14464960654245209780506329088 }, { target := 394, numerator := 321742253292398596503633920 }, { target := 397, numerator := 3985884459254556281769295872 }, { target := 398, numerator := 699086686602386103593752068096 }, { target := 403, numerator := 699086770415167802493099835392 }, { target := 411, numerator := 3985800646472857382421528576 }, { target := 432, numerator := 105491934901586968830803968 }, { target := 433, numerator := 18502294280606785288246657024 }, { target := 438, numerator := 18502296498827760151820238848 }, { target := 446, numerator := 105489716680612105257222144 }, { target := 483, numerator := 229064124341920569367724032 }, { target := 485, numerator := 10353281697468722493345759232 }, { target := 490, numerator := 230286708822600275858554880 }, { target := 493, numerator := 1223136218183265125092294656 }, { target := 494, numerator := 214526601253521915909670699008 }, { target := 499, numerator := 214526626972894840679213039616 }, { target := 507, numerator := 1223110498810340355549954048 }, { target := 528, numerator := 3985884459254556281769295872 }, { target := 529, numerator := 699086686602386103593752068096 }, { target := 534, numerator := 699086770415167802493099835392 }, { target := 542, numerator := 3985800646472857382421528576 }, { target := 624, numerator := 102640801525868402105647104 }, { target := 625, numerator := 18002232273022818118294044672 }, { target := 630, numerator := 18002234431291874742311583744 }, { target := 638, numerator := 102638643256811778088108032 }, { target := 760, numerator := 105491934901586968830803968 }, { target := 761, numerator := 18502294280606785288246657024 }, { target := 766, numerator := 18502296498827760151820238848 }, { target := 774, numerator := 105489716680612105257222144 }, { target := 795, numerator := 105491934901586968830803968 }, { target := 796, numerator := 18502294280606785288246657024 }, { target := 801, numerator := 18502296498827760151820238848 }, { target := 809, numerator := 105489716680612105257222144 }, { target := 891, numerator := 116896468404461235731431424 }, { target := 892, numerator := 20502542310942653968057106432 }, { target := 897, numerator := 20502544768971301789854859264 }, { target := 905, numerator := 116894010375813413933678592 }]

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
    Slot13.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 750, numerator := 11883469778024501809774592 }, { target := 752, numerator := 537111215074405996971425792 }, { target := 757, numerator := 11946895448757438282465280 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
