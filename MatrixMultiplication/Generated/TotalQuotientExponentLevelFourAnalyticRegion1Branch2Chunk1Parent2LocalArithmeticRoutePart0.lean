import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 930131236675309999642116096 }, { target := 112, numerator := 32552274271957210674115903488 }, { target := 115, numerator := 32552290237614206469732827136 }, { target := 122, numerator := 930123253846812101833654272 }, { target := 206, numerator := 24803499644674933323789762560 }, { target := 208, numerator := 868060647252192284643090759680 }, { target := 211, numerator := 868061073003045505859542056960 }, { target := 218, numerator := 24803286769248322715564113920 }, { target := 241, numerator := 23718346535220404990873960448 }, { target := 243, numerator := 830082993934908872189955538944 }, { target := 246, numerator := 830083401059162264978187091968 }, { target := 253, numerator := 23718142973093708596758183936 }, { target := 257, numerator := 6496305927752757414146867200 }, { target := 260, numerator := 22211310109989625123611607040 }, { target := 262, numerator := 6496303829435619029685370880 }, { target := 302, numerator := 775109363896091666368430080 }, { target := 304, numerator := 27126895226631008895096586240 }, { target := 307, numerator := 27126908531345172058110689280 }, { target := 314, numerator := 775102711539010084861378560 }, { target := 353, numerator := 6681914668545693340265349120 }, { target := 356, numerator := 22845918970275042984286224384 }, { target := 358, numerator := 6681912510276636716247810048 }, { target := 379, numerator := 6496305927752757414146867200 }, { target := 382, numerator := 22211310109989625123611607040 }, { target := 384, numerator := 6496303829435619029685370880 }, { target := 524, numerator := 5753870964581013709672939520 }, { target := 527, numerator := 19672874668847953680913137664 }, { target := 529, numerator := 5753869106071548283435614208 }, { target := 620, numerator := 269318282890550028797917265920 }, { target := 623, numerator := 920817456274141315838869766144 }, { target := 625, numerator := 269318195900316663202099232768 }, { target := 646, numerator := 73315452613209690816800358400 }, { target := 649, numerator := 250670499812740054966473850880 }, { target := 651, numerator := 73315428932201986192163471360 }, { target := 695, numerator := 6681914668545693340265349120 }, { target := 698, numerator := 22845918970275042984286224384 }, { target := 700, numerator := 6681912510276636716247810048 }, { target := 721, numerator := 269318282890550028797917265920 }, { target := 724, numerator := 920817456274141315838869766144 }, { target := 726, numerator := 269318195900316663202099232768 }, { target := 735, numerator := 6496305927752757414146867200 }, { target := 738, numerator := 22211310109989625123611607040 }, { target := 740, numerator := 6496303829435619029685370880 }, { target := 836, numerator := 6496305927752757414146867200 }, { target := 839, numerator := 22211310109989625123611607040 }, { target := 841, numerator := 6496303829435619029685370880 }, { target := 862, numerator := 5568262223788077783554457600 }, { target := 865, numerator := 19038265808562535820238520320 }, { target := 867, numerator := 5568260425230530596873175040 }, { target := 911, numerator := 6496305927752757414146867200 }, { target := 914, numerator := 22211310109989625123611607040 }, { target := 916, numerator := 6496303829435619029685370880 }, { target := 937, numerator := 73315452613209690816800358400 }, { target := 940, numerator := 250670499812740054966473850880 }, { target := 942, numerator := 73315428932201986192163471360 }, { target := 951, numerator := 5568262223788077783554457600 }, { target := 954, numerator := 19038265808562535820238520320 }, { target := 956, numerator := 5568260425230530596873175040 }, { target := 982, numerator := 6496305927752757414146867200 }, { target := 985, numerator := 22211310109989625123611607040 }, { target := 987, numerator := 6496303829435619029685370880 }, { target := 996, numerator := 5753870964581013709672939520 }, { target := 999, numerator := 19672874668847953680913137664 }, { target := 1001, numerator := 5753869106071548283435614208 }]

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
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 24338434026337278323968704512 }, { target := 339, numerator := 851784510116213679306032807936 }, { target := 342, numerator := 851784927884238402624675643392 }, { target := 349, numerator := 24338225142324916664647286784 }, { target := 363, numerator := 775109363896091666368430080 }, { target := 365, numerator := 27126895226631008895096586240 }, { target := 368, numerator := 27126908531345172058110689280 }, { target := 375, numerator := 775102711539010084861378560 }, { target := 473, numerator := 23718346535220404990873960448 }, { target := 475, numerator := 830082993934908872189955538944 }, { target := 478, numerator := 830083401059162264978187091968 }, { target := 485, numerator := 23718142973093708596758183936 }, { target := 508, numerator := 13486902931791994994810683392 }, { target := 510, numerator := 472007976943379554774680600576 }, { target := 513, numerator := 472008208445405993811125993472 }, { target := 520, numerator := 13486787180778775476587986944 }, { target := 569, numerator := 24338434026337278323968704512 }, { target := 571, numerator := 851784510116213679306032807936 }, { target := 574, numerator := 851784927884238402624675643392 }, { target := 581, numerator := 24338225142324916664647286784 }, { target := 604, numerator := 379958610181864134853804425216 }, { target := 606, numerator := 13297604040094520560376346574848 }, { target := 609, numerator := 13297610562065403342885859885056 }, { target := 616, numerator := 379955349196422743599047770112 }, { target := 630, numerator := 14882099786804959994273857536 }, { target := 632, numerator := 520836388351315370785854455808 }, { target := 635, numerator := 520836643801827303515725234176 }, { target := 642, numerator := 14881972061548993629338468352 }, { target := 679, numerator := 24803499644674933323789762560 }, { target := 681, numerator := 868060647252192284643090759680 }, { target := 684, numerator := 868061073003045505859542056960 }, { target := 691, numerator := 24803286769248322715564113920 }, { target := 705, numerator := 23718346535220404990873960448 }, { target := 707, numerator := 830082993934908872189955538944 }, { target := 710, numerator := 830083401059162264978187091968 }, { target := 717, numerator := 23718142973093708596758183936 }, { target := 785, numerator := 775109363896091666368430080 }, { target := 787, numerator := 27126895226631008895096586240 }, { target := 790, numerator := 27126908531345172058110689280 }, { target := 797, numerator := 775102711539010084861378560 }, { target := 820, numerator := 14882099786804959994273857536 }, { target := 822, numerator := 520836388351315370785854455808 }, { target := 825, numerator := 520836643801827303515725234176 }, { target := 832, numerator := 14881972061548993629338468352 }, { target := 846, numerator := 775109363896091666368430080 }, { target := 848, numerator := 27126895226631008895096586240 }, { target := 851, numerator := 27126908531345172058110689280 }, { target := 858, numerator := 775102711539010084861378560 }, { target := 895, numerator := 23873368407999623324147646464 }, { target := 897, numerator := 835508372980235073968974856192 }, { target := 900, numerator := 835508782765431299389809229824 }, { target := 907, numerator := 23873163515401510613730459648 }, { target := 921, numerator := 13486902931791994994810683392 }, { target := 923, numerator := 472007976943379554774680600576 }, { target := 926, numerator := 472008208445405993811125993472 }, { target := 933, numerator := 13486787180778775476587986944 }, { target := 966, numerator := 930131236675309999642116096 }, { target := 968, numerator := 32552274271957210674115903488 }, { target := 971, numerator := 32552290237614206469732827136 }, { target := 978, numerator := 930123253846812101833654272 }]

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
    Slot4.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 152914082084830517315764224 }, { target := 57, numerator := 16032765715780194134850011136 }, { target := 59, numerator := 172817189685630410390765568000 }, { target := 67, numerator := 16032777945971515004282732544 }, { target := 74, numerator := 152914082084830517315764224 }, { target := 91, numerator := 149728372041396548205019136 }, { target := 92, numerator := 15698749763368106757040635904 }, { target := 94, numerator := 169216831567179776840957952000 }, { target := 102, numerator := 15698761738763775108360175616 }, { target := 109, numerator := 149728372041396548205019136 }, { target := 152, numerator := 117871271607056857097568256 }, { target := 153, numerator := 12358590239247232978946883584 }, { target := 155, numerator := 133213250382673441342881792000 }, { target := 163, numerator := 12358599666686376149134606336 }, { target := 170, numerator := 117871271607056857097568256 }, { target := 187, numerator := 3704980780513706075796537344 }, { target := 188, numerator := 388460552655257620392303394816 }, { target := 190, numerator := 4187216491758086818426257408000 }, { target := 198, numerator := 388460848982601498957933707264 }, { target := 205, numerator := 3704980780513706075796537344 }, { target := 222, numerator := 117871271607056857097568256 }, { target := 223, numerator := 12358590239247232978946883584 }, { target := 225, numerator := 133213250382673441342881792000 }, { target := 233, numerator := 12358599666686376149134606336 }, { target := 240, numerator := 117871271607056857097568256 }, { target := 283, numerator := 117871271607056857097568256 }, { target := 284, numerator := 12358590239247232978946883584 }, { target := 286, numerator := 133213250382673441342881792000 }, { target := 294, numerator := 12358599666686376149134606336 }, { target := 301, numerator := 117871271607056857097568256 }, { target := 318, numerator := 121056981650490826208313344 }, { target := 319, numerator := 12692606191659320356756258816 }, { target := 321, numerator := 136813608501124074892689408000 }, { target := 329, numerator := 12692615873894116045057163264 }, { target := 336, numerator := 121056981650490826208313344 }, { target := 419, numerator := 121056981650490826208313344 }, { target := 420, numerator := 12692606191659320356756258816 }, { target := 422, numerator := 136813608501124074892689408000 }, { target := 430, numerator := 12692615873894116045057163264 }, { target := 437, numerator := 121056981650490826208313344 }, { target := 454, numerator := 2048411557928042138209091584 }, { target := 455, numerator := 214772257400972183931428274176 }, { target := 457, numerator := 2315030270163757372526297088000 }, { target := 465, numerator := 214772421234576753078204104704 }, { target := 472, numerator := 2048411557928042138209091584 }, { target := 489, numerator := 111499851520188918876078080 }, { target := 490, numerator := 11690558334423058223328133120 }, { target := 492, numerator := 126012534145772174243266560000 }, { target := 500, numerator := 11690567252270896357289492480 }, { target := 507, numerator := 111499851520188918876078080 }, { target := 550, numerator := 3704980780513706075796537344 }, { target := 551, numerator := 388460552655257620392303394816 }, { target := 553, numerator := 4187216491758086818426257408000 }, { target := 561, numerator := 388460848982601498957933707264 }, { target := 568, numerator := 3704980780513706075796537344 }, { target := 585, numerator := 2048411557928042138209091584 }, { target := 586, numerator := 214772257400972183931428274176 }, { target := 588, numerator := 2315030270163757372526297088000 }, { target := 596, numerator := 214772421234576753078204104704 }, { target := 603, numerator := 2048411557928042138209091584 }]

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
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 21230968802829764583751680 }, { target := 15, numerator := 1777650650783738447379038208 }, { target := 20, numerator := 1777651294113938017999650816 }, { target := 28, numerator := 21230325472630193963139072 }, { target := 40, numerator := 520501170650020034956492800 }, { target := 41, numerator := 43581112728891652258324807680 }, { target := 46, numerator := 43581128500857835279991439360 }, { target := 54, numerator := 520485398683837013289861120 }, { target := 75, numerator := 21230968802829764583751680 }, { target := 76, numerator := 1777650650783738447379038208 }, { target := 81, numerator := 1777651294113938017999650816 }, { target := 89, numerator := 21230325472630193963139072 }, { target := 136, numerator := 436262165400082581930639360 }, { target := 137, numerator := 36527853695136819063885398016 }, { target := 142, numerator := 36527866914534790885992824832 }, { target := 150, numerator := 436248946002110759823212544 }, { target := 171, numerator := 428728595824884923529953280 }, { target := 172, numerator := 35897074431955492518041223168 }, { target := 177, numerator := 35897087423075006427992948736 }, { target := 185, numerator := 428715604705371013578227712 }, { target := 267, numerator := 21230968802829764583751680 }, { target := 268, numerator := 1777650650783738447379038208 }, { target := 273, numerator := 1777651294113938017999650816 }, { target := 281, numerator := 21230325472630193963139072 }, { target := 403, numerator := 429413465786266528839106560 }, { target := 404, numerator := 35954418001335613113117966336 }, { target := 409, numerator := 35954431013207714105992937472 }, { target := 417, numerator := 429400453914165535964135424 }, { target := 438, numerator := 384896918296462183744143360 }, { target := 439, numerator := 32227085991627774433129660416 }, { target := 444, numerator := 32227097654581715035993669632 }, { target := 452, numerator := 384885255342521580880134144 }, { target := 534, numerator := 520501170650020034956492800 }, { target := 535, numerator := 43581112728891652258324807680 }, { target := 540, numerator := 43581128500857835279991439360 }, { target := 548, numerator := 520485398683837013289861120 }, { target := 660, numerator := 152914082084830517315764224 }, { target := 661, numerator := 16032765715780194134850011136 }, { target := 663, numerator := 172817189685630410390765568000 }, { target := 671, numerator := 16032777945971515004282732544 }, { target := 678, numerator := 152914082084830517315764224 }, { target := 750, numerator := 21230968802829764583751680 }, { target := 751, numerator := 1777650650783738447379038208 }, { target := 756, numerator := 1777651294113938017999650816 }, { target := 764, numerator := 21230325472630193963139072 }, { target := 766, numerator := 117871271607056857097568256 }, { target := 767, numerator := 12358590239247232978946883584 }, { target := 769, numerator := 133213250382673441342881792000 }, { target := 777, numerator := 12358599666686376149134606336 }, { target := 784, numerator := 117871271607056857097568256 }, { target := 801, numerator := 111499851520188918876078080 }, { target := 802, numerator := 11690558334423058223328133120 }, { target := 804, numerator := 126012534145772174243266560000 }, { target := 812, numerator := 11690567252270896357289492480 }, { target := 819, numerator := 111499851520188918876078080 }, { target := 876, numerator := 149728372041396548205019136 }, { target := 877, numerator := 15698749763368106757040635904 }, { target := 879, numerator := 169216831567179776840957952000 }, { target := 887, numerator := 15698761738763775108360175616 }, { target := 894, numerator := 149728372041396548205019136 }]

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 153606001008291288887328768 }, { target := 111, numerator := 150405875987285220368842752 }, { target := 112, numerator := 118404625777224535183982592 }, { target := 113, numerator := 3721745399430057686999236608 }, { target := 114, numerator := 118404625777224535183982592 }, { target := 115, numerator := 118404625777224535183982592 }, { target := 116, numerator := 121604750798230603702468608 }, { target := 117, numerator := 121604750798230603702468608 }, { target := 118, numerator := 2057680388506902057386508288 }, { target := 119, numerator := 112004375735212398147010560 }, { target := 120, numerator := 3721745399430057686999236608 }, { target := 121, numerator := 2057680388506902057386508288 }, { target := 122, numerator := 153606001008291288887328768 }, { target := 123, numerator := 118404625777224535183982592 }, { target := 124, numerator := 112004375735212398147010560 }, { target := 125, numerator := 150405875987285220368842752 }, { target := 257, numerator := 21230968802829764583751680 }, { target := 258, numerator := 520501170650020034956492800 }, { target := 259, numerator := 21230968802829764583751680 }, { target := 260, numerator := 436262165400082581930639360 }, { target := 261, numerator := 428728595824884923529953280 }, { target := 262, numerator := 21230968802829764583751680 }, { target := 263, numerator := 429413465786266528839106560 }, { target := 264, numerator := 384896918296462183744143360 }, { target := 265, numerator := 520501170650020034956492800 }, { target := 266, numerator := 21230968802829764583751680 }, { target := 353, numerator := 1777650650783738447379038208 }, { target := 354, numerator := 43581112728891652258324807680 }, { target := 355, numerator := 1777650650783738447379038208 }, { target := 356, numerator := 36527853695136819063885398016 }, { target := 357, numerator := 35897074431955492518041223168 }, { target := 358, numerator := 1777650650783738447379038208 }, { target := 359, numerator := 35954418001335613113117966336 }, { target := 360, numerator := 32227085991627774433129660416 }, { target := 361, numerator := 43581112728891652258324807680 }, { target := 362, numerator := 1777650650783738447379038208 }, { target := 695, numerator := 1777651294113938017999650816 }, { target := 696, numerator := 43581128500857835279991439360 }, { target := 697, numerator := 1777651294113938017999650816 }, { target := 698, numerator := 36527866914534790885992824832 }, { target := 699, numerator := 35897087423075006427992948736 }, { target := 700, numerator := 1777651294113938017999650816 }, { target := 701, numerator := 35954431013207714105992937472 }, { target := 702, numerator := 32227097654581715035993669632 }, { target := 703, numerator := 43581128500857835279991439360 }, { target := 704, numerator := 1777651294113938017999650816 }, { target := 982, numerator := 21230325472630193963139072 }, { target := 983, numerator := 520485398683837013289861120 }, { target := 984, numerator := 21230325472630193963139072 }, { target := 985, numerator := 436248946002110759823212544 }, { target := 986, numerator := 428715604705371013578227712 }, { target := 987, numerator := 21230325472630193963139072 }, { target := 988, numerator := 429400453914165535964135424 }, { target := 989, numerator := 384885255342521580880134144 }, { target := 990, numerator := 520485398683837013289861120 }, { target := 991, numerator := 21230325472630193963139072 }]

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
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 16105312166982819447677386752 }, { target := 207, numerator := 15769784830170677375850774528 }, { target := 208, numerator := 12414511462049256657584652288 }, { target := 209, numerator := 390218292712521229534350016512 }, { target := 210, numerator := 12414511462049256657584652288 }, { target := 211, numerator := 12414511462049256657584652288 }, { target := 212, numerator := 12750038798861398729411264512 }, { target := 213, numerator := 12750038798861398729411264512 }, { target := 214, numerator := 215744077570207352184511660032 }, { target := 215, numerator := 11743456788424972513931427840 }, { target := 216, numerator := 390218292712521229534350016512 }, { target := 217, numerator := 215744077570207352184511660032 }, { target := 218, numerator := 16105312166982819447677386752 }, { target := 219, numerator := 12414511462049256657584652288 }, { target := 220, numerator := 11743456788424972513931427840 }, { target := 221, numerator := 15769784830170677375850774528 }, { target := 302, numerator := 173599167919502041207013376000 }, { target := 303, numerator := 169982518587845748681867264000 }, { target := 304, numerator := 133816025271282823430406144000 }, { target := 305, numerator := 4206163172716268206744928256000 }, { target := 306, numerator := 133816025271282823430406144000 }, { target := 307, numerator := 133816025271282823430406144000 }, { target := 308, numerator := 137432674602939115955552256000 }, { target := 309, numerator := 137432674602939115955552256000 }, { target := 310, numerator := 2325505520254996093668950016000 }, { target := 311, numerator := 126582726607970238380113920000 }, { target := 312, numerator := 4206163172716268206744928256000 }, { target := 313, numerator := 2325505520254996093668950016000 }, { target := 314, numerator := 173599167919502041207013376000 }, { target := 315, numerator := 133816025271282823430406144000 }, { target := 316, numerator := 126582726607970238380113920000 }, { target := 317, numerator := 169982518587845748681867264000 }, { target := 679, numerator := 16105324452514372538238763008 }, { target := 680, numerator := 15769796859753656443692122112 }, { target := 681, numerator := 12414520932146495498225713152 }, { target := 682, numerator := 390218590380712817957743362048 }, { target := 683, numerator := 12414520932146495498225713152 }, { target := 684, numerator := 12414520932146495498225713152 }, { target := 685, numerator := 12750048524907211592772354048 }, { target := 686, numerator := 12750048524907211592772354048 }, { target := 687, numerator := 215744242145140448793490096128 }, { target := 688, numerator := 11743465746625063309132431360 }, { target := 689, numerator := 390218590380712817957743362048 }, { target := 690, numerator := 215744242145140448793490096128 }, { target := 691, numerator := 16105324452514372538238763008 }, { target := 692, numerator := 12414520932146495498225713152 }, { target := 693, numerator := 11743465746625063309132431360 }, { target := 694, numerator := 15769796859753656443692122112 }, { target := 966, numerator := 153606001008291288887328768 }, { target := 967, numerator := 150405875987285220368842752 }, { target := 968, numerator := 118404625777224535183982592 }, { target := 969, numerator := 3721745399430057686999236608 }, { target := 970, numerator := 118404625777224535183982592 }, { target := 971, numerator := 118404625777224535183982592 }, { target := 972, numerator := 121604750798230603702468608 }, { target := 973, numerator := 121604750798230603702468608 }, { target := 974, numerator := 2057680388506902057386508288 }, { target := 975, numerator := 112004375735212398147010560 }, { target := 976, numerator := 3721745399430057686999236608 }, { target := 977, numerator := 2057680388506902057386508288 }, { target := 978, numerator := 153606001008291288887328768 }, { target := 979, numerator := 118404625777224535183982592 }, { target := 980, numerator := 112004375735212398147010560 }, { target := 981, numerator := 150405875987285220368842752 }]

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
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 925295199049615146957668352 }, { target := 57, numerator := 24674538641323070585537822720 }, { target := 58, numerator := 23595027575765186247420542976 }, { target := 59, numerator := 771079332541345955798056960 }, { target := 60, numerator := 24211891041798263012058988544 }, { target := 61, numerator := 771079332541345955798056960 }, { target := 62, numerator := 23595027575765186247420542976 }, { target := 63, numerator := 13416780386219419630886191104 }, { target := 64, numerator := 24211891041798263012058988544 }, { target := 65, numerator := 377983088811767787532207521792 }, { target := 66, numerator := 14804723184793842351322693632 }, { target := 67, numerator := 24674538641323070585537822720 }, { target := 68, numerator := 23595027575765186247420542976 }, { target := 69, numerator := 771079332541345955798056960 }, { target := 70, numerator := 14804723184793842351322693632 }, { target := 71, numerator := 771079332541345955798056960 }, { target := 72, numerator := 23749243442273455438580154368 }, { target := 73, numerator := 13416780386219419630886191104 }, { target := 74, numerator := 925295199049615146957668352 }, { target := 152, numerator := 32383025012310986008565907456 }, { target := 153, numerator := 863547333661626293561757532160 }, { target := 154, numerator := 825767137813930143218430640128 }, { target := 155, numerator := 26985854176925821673804922880 }, { target := 156, numerator := 847355821155470800557474578432 }, { target := 157, numerator := 26985854176925821673804922880 }, { target := 158, numerator := 825767137813930143218430640128 }, { target := 159, numerator := 469553862678509297124205658112 }, { target := 160, numerator := 847355821155470800557474578432 }, { target := 161, numerator := 13228465717529037784499173195776 }, { target := 162, numerator := 518128400196975776137054519296 }, { target := 163, numerator := 863547333661626293561757532160 }, { target := 164, numerator := 825767137813930143218430640128 }, { target := 165, numerator := 26985854176925821673804922880 }, { target := 166, numerator := 518128400196975776137054519296 }, { target := 167, numerator := 26985854176925821673804922880 }, { target := 168, numerator := 831164308649315307553191624704 }, { target := 169, numerator := 469553862678509297124205658112 }, { target := 170, numerator := 32383025012310986008565907456 }, { target := 283, numerator := 32383040894957633472489848832 }, { target := 284, numerator := 863547757198870225933062635520 }, { target := 285, numerator := 825767542821419653548491145216 }, { target := 286, numerator := 26985867412464694560408207360 }, { target := 287, numerator := 847356236751391409196817711104 }, { target := 288, numerator := 26985867412464694560408207360 }, { target := 289, numerator := 825767542821419653548491145216 }, { target := 290, numerator := 469554092976885685351102808064 }, { target := 291, numerator := 847356236751391409196817711104 }, { target := 292, numerator := 13228472205590193273512103247872 }, { target := 293, numerator := 518128654319322135559837581312 }, { target := 294, numerator := 863547757198870225933062635520 }, { target := 295, numerator := 825767542821419653548491145216 }, { target := 296, numerator := 26985867412464694560408207360 }, { target := 297, numerator := 518128654319322135559837581312 }, { target := 298, numerator := 26985867412464694560408207360 }, { target := 299, numerator := 831164716303912592460572786688 }, { target := 300, numerator := 469554092976885685351102808064 }, { target := 301, numerator := 32383040894957633472489848832 }]

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
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 6496305927752757414146867200 }, { target := 15, numerator := 6681914668545693340265349120 }, { target := 16, numerator := 6496305927752757414146867200 }, { target := 17, numerator := 5753870964581013709672939520 }, { target := 18, numerator := 269318282890550028797917265920 }, { target := 19, numerator := 73315452613209690816800358400 }, { target := 20, numerator := 6681914668545693340265349120 }, { target := 21, numerator := 269318282890550028797917265920 }, { target := 22, numerator := 6496305927752757414146867200 }, { target := 23, numerator := 6496305927752757414146867200 }, { target := 24, numerator := 5568262223788077783554457600 }, { target := 25, numerator := 6496305927752757414146867200 }, { target := 26, numerator := 73315452613209690816800358400 }, { target := 27, numerator := 5568262223788077783554457600 }, { target := 28, numerator := 6496305927752757414146867200 }, { target := 29, numerator := 5753870964581013709672939520 }, { target := 136, numerator := 22211310109989625123611607040 }, { target := 137, numerator := 22845918970275042984286224384 }, { target := 138, numerator := 22211310109989625123611607040 }, { target := 139, numerator := 19672874668847953680913137664 }, { target := 140, numerator := 920817456274141315838869766144 }, { target := 141, numerator := 250670499812740054966473850880 }, { target := 142, numerator := 22845918970275042984286224384 }, { target := 143, numerator := 920817456274141315838869766144 }, { target := 144, numerator := 22211310109989625123611607040 }, { target := 145, numerator := 22211310109989625123611607040 }, { target := 146, numerator := 19038265808562535820238520320 }, { target := 147, numerator := 22211310109989625123611607040 }, { target := 148, numerator := 250670499812740054966473850880 }, { target := 149, numerator := 19038265808562535820238520320 }, { target := 150, numerator := 22211310109989625123611607040 }, { target := 151, numerator := 19672874668847953680913137664 }, { target := 660, numerator := 925287257726291414995697664 }, { target := 661, numerator := 24674326872701104399885271040 }, { target := 662, numerator := 23594825072020431082390290432 }, { target := 663, numerator := 771072714771909512496414720 }, { target := 664, numerator := 24211683243837958692387422208 }, { target := 665, numerator := 771072714771909512496414720 }, { target := 666, numerator := 23594825072020431082390290432 }, { target := 667, numerator := 13416665237031225517437616128 }, { target := 668, numerator := 24211683243837958692387422208 }, { target := 669, numerator := 377979844781190043025742495744 }, { target := 670, numerator := 14804596123620662639931162624 }, { target := 671, numerator := 24674326872701104399885271040 }, { target := 672, numerator := 23594825072020431082390290432 }, { target := 673, numerator := 771072714771909512496414720 }, { target := 674, numerator := 14804596123620662639931162624 }, { target := 675, numerator := 771072714771909512496414720 }, { target := 676, numerator := 23749039614974812984889573376 }, { target := 677, numerator := 13416665237031225517437616128 }, { target := 678, numerator := 925287257726291414995697664 }]

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
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 267, numerator := 6496303829435619029685370880 }, { target := 268, numerator := 6681912510276636716247810048 }, { target := 269, numerator := 6496303829435619029685370880 }, { target := 270, numerator := 5753869106071548283435614208 }, { target := 271, numerator := 269318195900316663202099232768 }, { target := 272, numerator := 73315428932201986192163471360 }, { target := 273, numerator := 6681912510276636716247810048 }, { target := 274, numerator := 269318195900316663202099232768 }, { target := 275, numerator := 6496303829435619029685370880 }, { target := 276, numerator := 6496303829435619029685370880 }, { target := 277, numerator := 5568260425230530596873175040 }, { target := 278, numerator := 6496303829435619029685370880 }, { target := 279, numerator := 73315428932201986192163471360 }, { target := 280, numerator := 5568260425230530596873175040 }, { target := 281, numerator := 6496303829435619029685370880 }, { target := 282, numerator := 5753869106071548283435614208 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2
