import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 5822207481404392954920960 }, { target := 15, numerator := 1154746579348639614763008000 }, { target := 20, numerator := 1154746579348639614763008000 }, { target := 28, numerator := 5822207481404392954920960 }, { target := 40, numerator := 121538581174316702933975040 }, { target := 41, numerator := 24105334843902851958177792000 }, { target := 46, numerator := 24105334843902851958177792000 }, { target := 54, numerator := 121538581174316702933975040 }, { target := 56, numerator := 73430638233723349841739776 }, { target := 57, numerator := 12033867373729540943768453120 }, { target := 59, numerator := 123893323988700920864382648320 }, { target := 67, numerator := 12033867373729540943768453120 }, { target := 74, numerator := 73430638233723349841739776 }, { target := 75, numerator := 6307391438188092367831040 }, { target := 76, numerator := 1250975460961026249326592000 }, { target := 81, numerator := 1250975460961026249326592000 }, { target := 89, numerator := 6307391438188092367831040 }, { target := 91, numerator := 82905559296139265950351360 }, { target := 92, numerator := 13586624454210772033286963200 }, { target := 94, numerator := 139879559342081684846883635200 }, { target := 102, numerator := 13586624454210772033286963200 }, { target := 109, numerator := 82905559296139265950351360 }, { target := 136, numerator := 130757076353206991779266560 }, { target := 137, numerator := 25933683594538198014885888000 }, { target := 142, numerator := 25933683594538198014885888000 }, { target := 150, numerator := 130757076353206991779266560 }, { target := 152, numerator := 71061907968119370814586880 }, { target := 153, numerator := 11645678103609233171388825600 }, { target := 155, numerator := 119896765150355729868757401600 }, { target := 163, numerator := 11645678103609233171388825600 }, { target := 170, numerator := 71061907968119370814586880 }, { target := 171, numerator := 195771726562222713109217280 }, { target := 172, numerator := 38828353730598007046406144000 }, { target := 177, numerator := 38828353730598007046406144000 }, { target := 185, numerator := 195771726562222713109217280 }, { target := 187, numerator := 935648454913571715725393920 }, { target := 188, numerator := 153334761697521570089952870400 }, { target := 190, numerator := 1578640741146350443271972454400 }, { target := 198, numerator := 153334761697521570089952870400 }, { target := 205, numerator := 935648454913571715725393920 }, { target := 267, numerator := 6064799459796242661376000 }, { target := 268, numerator := 1202861020154832932044800000 }, { target := 273, numerator := 1202861020154832932044800000 }, { target := 281, numerator := 6064799459796242661376000 }, { target := 403, numerator := 195771726562222713109217280 }, { target := 404, numerator := 38828353730598007046406144000 }, { target := 409, numerator := 38828353730598007046406144000 }, { target := 417, numerator := 195771726562222713109217280 }, { target := 438, numerator := 204019853827545603128688640 }, { target := 439, numerator := 40464244718008579833987072000 }, { target := 444, numerator := 40464244718008579833987072000 }, { target := 452, numerator := 204019853827545603128688640 }, { target := 534, numerator := 121538581174316702933975040 }, { target := 535, numerator := 24105334843902851958177792000 }, { target := 540, numerator := 24105334843902851958177792000 }, { target := 548, numerator := 121538581174316702933975040 }, { target := 750, numerator := 6064799459796242661376000 }, { target := 751, numerator := 1202861020154832932044800000 }, { target := 756, numerator := 1202861020154832932044800000 }, { target := 764, numerator := 6064799459796242661376000 }]

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
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 785893935765372188837806080 }, { target := 112, numerator := 31419893737996959366135152640 }, { target := 115, numerator := 31419886059539738684534292480 }, { target := 122, numerator := 785893935765372188837806080 }, { target := 222, numerator := 82905559296139265950351360 }, { target := 223, numerator := 13586624454210772033286963200 }, { target := 225, numerator := 139879559342081684846883635200 }, { target := 233, numerator := 13586624454210772033286963200 }, { target := 240, numerator := 82905559296139265950351360 }, { target := 283, numerator := 71061907968119370814586880 }, { target := 284, numerator := 11645678103609233171388825600 }, { target := 286, numerator := 119896765150355729868757401600 }, { target := 294, numerator := 11645678103609233171388825600 }, { target := 301, numerator := 71061907968119370814586880 }, { target := 318, numerator := 82905559296139265950351360 }, { target := 319, numerator := 13586624454210772033286963200 }, { target := 321, numerator := 139879559342081684846883635200 }, { target := 329, numerator := 13586624454210772033286963200 }, { target := 336, numerator := 82905559296139265950351360 }, { target := 419, numerator := 82905559296139265950351360 }, { target := 420, numerator := 13586624454210772033286963200 }, { target := 422, numerator := 139879559342081684846883635200 }, { target := 430, numerator := 13586624454210772033286963200 }, { target := 437, numerator := 82905559296139265950351360 }, { target := 454, numerator := 3437027615391373568398852096 }, { target := 455, numerator := 563262630944566577722839531520 }, { target := 457, numerator := 5799006874438872134652232990720 }, { target := 465, numerator := 563262630944566577722839531520 }, { target := 472, numerator := 3437027615391373568398852096 }, { target := 489, numerator := 85274289561743244977504256 }, { target := 490, numerator := 13974813724331079805666590720 }, { target := 492, numerator := 143876118180426875842508881920 }, { target := 500, numerator := 13974813724331079805666590720 }, { target := 507, numerator := 85274289561743244977504256 }, { target := 550, numerator := 935648454913571715725393920 }, { target := 551, numerator := 153334761697521570089952870400 }, { target := 553, numerator := 1578640741146350443271972454400 }, { target := 561, numerator := 153334761697521570089952870400 }, { target := 568, numerator := 935648454913571715725393920 }, { target := 585, numerator := 3437027615391373568398852096 }, { target := 586, numerator := 563262630944566577722839531520 }, { target := 588, numerator := 5799006874438872134652232990720 }, { target := 596, numerator := 563262630944566577722839531520 }, { target := 603, numerator := 3437027615391373568398852096 }, { target := 660, numerator := 73430638233723349841739776 }, { target := 661, numerator := 12033867373729540943768453120 }, { target := 663, numerator := 123893323988700920864382648320 }, { target := 671, numerator := 12033867373729540943768453120 }, { target := 678, numerator := 73430638233723349841739776 }, { target := 766, numerator := 82905559296139265950351360 }, { target := 767, numerator := 13586624454210772033286963200 }, { target := 769, numerator := 139879559342081684846883635200 }, { target := 777, numerator := 13586624454210772033286963200 }, { target := 784, numerator := 82905559296139265950351360 }, { target := 801, numerator := 85274289561743244977504256 }, { target := 802, numerator := 13974813724331079805666590720 }, { target := 804, numerator := 143876118180426875842508881920 }, { target := 812, numerator := 13974813724331079805666590720 }, { target := 819, numerator := 85274289561743244977504256 }, { target := 876, numerator := 82905559296139265950351360 }, { target := 877, numerator := 13586624454210772033286963200 }, { target := 879, numerator := 139879559342081684846883635200 }, { target := 887, numerator := 13586624454210772033286963200 }, { target := 894, numerator := 82905559296139265950351360 }]

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
    Slot4.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 11395462068597896738148188160 }, { target := 208, numerator := 455588459200955910808959713280 }, { target := 211, numerator := 455588347863326210925747240960 }, { target := 218, numerator := 11395462068597896738148188160 }, { target := 241, numerator := 20171277684644552846837022720 }, { target := 243, numerator := 806443939275255290397468917760 }, { target := 246, numerator := 806443742194853292903046840320 }, { target := 253, numerator := 20171277684644552846837022720 }, { target := 302, numerator := 654911613137810157364838400 }, { target := 304, numerator := 26183244781664132805112627200 }, { target := 307, numerator := 26183238382949782237111910400 }, { target := 314, numerator := 654911613137810157364838400 }, { target := 337, numerator := 12574302972245955021404897280 }, { target := 339, numerator := 502718299807951349858162442240 }, { target := 342, numerator := 502718176952635818952548679680 }, { target := 349, numerator := 12574302972245955021404897280 }, { target := 363, numerator := 654911613137810157364838400 }, { target := 365, numerator := 26183244781664132805112627200 }, { target := 368, numerator := 26183238382949782237111910400 }, { target := 375, numerator := 654911613137810157364838400 }, { target := 473, numerator := 20040295362016990815364055040 }, { target := 475, numerator := 801207290318922463836446392320 }, { target := 478, numerator := 801207094518263336455624458240 }, { target := 485, numerator := 20040295362016990815364055040 }, { target := 508, numerator := 20957171620409925035674828800 }, { target := 510, numerator := 837863833013252249763604070400 }, { target := 513, numerator := 837863628254393031587581132800 }, { target := 520, numerator := 20957171620409925035674828800 }, { target := 569, numerator := 12574302972245955021404897280 }, { target := 571, numerator := 502718299807951349858162442240 }, { target := 574, numerator := 502718176952635818952548679680 }, { target := 581, numerator := 12574302972245955021404897280 }, { target := 604, numerator := 321037672760154539140243783680 }, { target := 606, numerator := 12835026591971757901066209853440 }, { target := 609, numerator := 12835023455321983252632258478080 }, { target := 616, numerator := 321037672760154539140243783680 }, { target := 630, numerator := 20564224652527238941255925760 }, { target := 632, numerator := 822153886144253770080536494080 }, { target := 635, numerator := 822153685224623162245313986560 }, { target := 642, numerator := 20564224652527238941255925760 }, { target := 679, numerator := 11395462068597896738148188160 }, { target := 681, numerator := 455588459200955910808959713280 }, { target := 684, numerator := 455588347863326210925747240960 }, { target := 691, numerator := 11395462068597896738148188160 }, { target := 705, numerator := 20040295362016990815364055040 }, { target := 707, numerator := 801207290318922463836446392320 }, { target := 710, numerator := 801207094518263336455624458240 }, { target := 717, numerator := 20040295362016990815364055040 }, { target := 785, numerator := 654911613137810157364838400 }, { target := 787, numerator := 26183244781664132805112627200 }, { target := 790, numerator := 26183238382949782237111910400 }, { target := 797, numerator := 654911613137810157364838400 }, { target := 820, numerator := 20564224652527238941255925760 }, { target := 822, numerator := 822153886144253770080536494080 }, { target := 825, numerator := 822153685224623162245313986560 }, { target := 832, numerator := 20564224652527238941255925760 }, { target := 846, numerator := 654911613137810157364838400 }, { target := 848, numerator := 26183244781664132805112627200 }, { target := 851, numerator := 26183238382949782237111910400 }, { target := 858, numerator := 654911613137810157364838400 }, { target := 895, numerator := 20040295362016990815364055040 }, { target := 897, numerator := 801207290318922463836446392320 }, { target := 900, numerator := 801207094518263336455624458240 }, { target := 907, numerator := 20040295362016990815364055040 }]

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
    Slot4.Left17.expected,
    Slot4.Left18.expected,
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
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 8055561473353135088782540800 }, { target := 260, numerator := 29344482452072715139206348800 }, { target := 262, numerator := 8055566892084206740963328000 }, { target := 353, numerator := 5998822373773611236327424000 }, { target := 356, numerator := 21852274166437128295153664000 }, { target := 358, numerator := 5998826408998877360291840000 }, { target := 379, numerator := 6341612223703531878403276800 }, { target := 382, numerator := 23100975547376392769162444800 }, { target := 384, numerator := 6341616489513098923737088000 }, { target := 524, numerator := 8226956398318095409820467200 }, { target := 527, numerator := 29968833142542347376210739200 }, { target := 529, numerator := 8226961932341317522685952000 }, { target := 620, numerator := 110206936752469486427386675200 }, { target := 623, numerator := 401457493971973528393823027200 }, { target := 625, numerator := 110207010885322232647647232000 }, { target := 646, numerator := 199332297734248853367108403200 }, { target := 649, numerator := 726119853016182291636106035200 }, { target := 651, numerator := 199332431819019839143411712000 }, { target := 695, numerator := 5998822373773611236327424000 }, { target := 698, numerator := 21852274166437128295153664000 }, { target := 700, numerator := 5998826408998877360291840000 }, { target := 721, numerator := 110206936752469486427386675200 }, { target := 724, numerator := 401457493971973528393823027200 }, { target := 726, numerator := 110207010885322232647647232000 }, { target := 735, numerator := 6513007148668492199441203200 }, { target := 738, numerator := 23725326237846025006166835200 }, { target := 740, numerator := 6513011529770209705459712000 }, { target := 836, numerator := 6513007148668492199441203200 }, { target := 839, numerator := 23725326237846025006166835200 }, { target := 841, numerator := 6513011529770209705459712000 }, { target := 862, numerator := 6341612223703531878403276800 }, { target := 865, numerator := 23100975547376392769162444800 }, { target := 867, numerator := 6341616489513098923737088000 }, { target := 911, numerator := 6341612223703531878403276800 }, { target := 914, numerator := 23100975547376392769162444800 }, { target := 916, numerator := 6341616489513098923737088000 }, { target := 921, numerator := 20957171620409925035674828800 }, { target := 923, numerator := 837863833013252249763604070400 }, { target := 926, numerator := 837863628254393031587581132800 }, { target := 933, numerator := 20957171620409925035674828800 }, { target := 937, numerator := 199332297734248853367108403200 }, { target := 940, numerator := 726119853016182291636106035200 }, { target := 942, numerator := 199332431819019839143411712000 }, { target := 951, numerator := 6341612223703531878403276800 }, { target := 954, numerator := 23100975547376392769162444800 }, { target := 956, numerator := 6341616489513098923737088000 }, { target := 966, numerator := 785893935765372188837806080 }, { target := 968, numerator := 31419893737996959366135152640 }, { target := 971, numerator := 31419886059539738684534292480 }, { target := 978, numerator := 785893935765372188837806080 }, { target := 982, numerator := 8055561473353135088782540800 }, { target := 985, numerator := 29344482452072715139206348800 }, { target := 987, numerator := 8055566892084206740963328000 }, { target := 996, numerator := 8226956398318095409820467200 }, { target := 999, numerator := 29968833142542347376210739200 }, { target := 1001, numerator := 8226961932341317522685952000 }]

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
    Slot10.Left3.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 7733339014419009685231239168 }, { target := 15, numerator := 5758869478822666786874327040 }, { target := 16, numerator := 6087947734755390603267145728 }, { target := 17, numerator := 7897878142385371593427648512 }, { target := 18, numerator := 105798659282370706970291208192 }, { target := 19, numerator := 191359005824878899232424067072 }, { target := 20, numerator := 5758869478822666786874327040 }, { target := 21, numerator := 105798659282370706970291208192 }, { target := 22, numerator := 6252486862721752511463555072 }, { target := 23, numerator := 6252486862721752511463555072 }, { target := 24, numerator := 6087947734755390603267145728 }, { target := 25, numerator := 6087947734755390603267145728 }, { target := 26, numerator := 191359005824878899232424067072 }, { target := 27, numerator := 6087947734755390603267145728 }, { target := 28, numerator := 7733339014419009685231239168 }, { target := 29, numerator := 7897878142385371593427648512 }, { target := 136, numerator := 28170703153989806533638094848 }, { target := 137, numerator := 20978183199779643163347517440 }, { target := 138, numerator := 22176936525481337058395947008 }, { target := 139, numerator := 28770079816840653481162309632 }, { target := 140, numerator := 385399194213094587258070106112 }, { target := 141, numerator := 697075058895534999970661793792 }, { target := 142, numerator := 20978183199779643163347517440 }, { target := 143, numerator := 385399194213094587258070106112 }, { target := 144, numerator := 22776313188332184005920161792 }, { target := 145, numerator := 22776313188332184005920161792 }, { target := 146, numerator := 22176936525481337058395947008 }, { target := 147, numerator := 22176936525481337058395947008 }, { target := 148, numerator := 697075058895534999970661793792 }, { target := 149, numerator := 22176936525481337058395947008 }, { target := 150, numerator := 28170703153989806533638094848 }, { target := 151, numerator := 28770079816840653481162309632 }, { target := 267, numerator := 7733344216400838471324794880 }, { target := 268, numerator := 5758873352638922265880166400 }, { target := 269, numerator := 6087951829932574966787604480 }, { target := 270, numerator := 7897883455047664821778513920 }, { target := 271, numerator := 105798730449909343341741342720 }, { target := 272, numerator := 191359134546259045577675243520 }, { target := 273, numerator := 5758873352638922265880166400 }, { target := 274, numerator := 105798730449909343341741342720 }, { target := 275, numerator := 6252491068579401317241323520 }, { target := 276, numerator := 6252491068579401317241323520 }, { target := 277, numerator := 6087951829932574966787604480 }, { target := 278, numerator := 6087951829932574966787604480 }, { target := 279, numerator := 191359134546259045577675243520 }, { target := 280, numerator := 6087951829932574966787604480 }, { target := 281, numerator := 7733344216400838471324794880 }, { target := 282, numerator := 7897883455047664821778513920 }]

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
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 804302262188705231098871808 }, { target := 57, numerator := 11662382801736225850933641216 }, { target := 58, numerator := 20643758062843434264871043072 }, { target := 59, numerator := 670251885157254359249059840 }, { target := 60, numerator := 12868836195019283697581948928 }, { target := 61, numerator := 670251885157254359249059840 }, { target := 62, numerator := 20509707685811983393021231104 }, { target := 63, numerator := 21448060325032139495969914880 }, { target := 64, numerator := 12868836195019283697581948928 }, { target := 65, numerator := 328557474104086086903889133568 }, { target := 66, numerator := 21045909193937786880420478976 }, { target := 67, numerator := 11662382801736225850933641216 }, { target := 68, numerator := 20509707685811983393021231104 }, { target := 69, numerator := 670251885157254359249059840 }, { target := 70, numerator := 21045909193937786880420478976 }, { target := 71, numerator := 670251885157254359249059840 }, { target := 72, numerator := 20509707685811983393021231104 }, { target := 73, numerator := 21448060325032139495969914880 }, { target := 74, numerator := 804302262188705231098871808 }, { target := 152, numerator := 32155855212941032288224804864 }, { target := 153, numerator := 466259900587644968179259670528 }, { target := 154, numerator := 825333617132153162064436658176 }, { target := 155, numerator := 26796546010784193573520670720 }, { target := 156, numerator := 514493683407056516611596877824 }, { target := 157, numerator := 26796546010784193573520670720 }, { target := 158, numerator := 819974307929996323349732524032 }, { target := 159, numerator := 857489472345094194352661463040 }, { target := 160, numerator := 514493683407056516611596877824 }, { target := 161, numerator := 13135666854486411689739832786944 }, { target := 162, numerator := 841411544738623678208549060608 }, { target := 163, numerator := 466259900587644968179259670528 }, { target := 164, numerator := 819974307929996323349732524032 }, { target := 165, numerator := 26796546010784193573520670720 }, { target := 166, numerator := 841411544738623678208549060608 }, { target := 167, numerator := 26796546010784193573520670720 }, { target := 168, numerator := 819974307929996323349732524032 }, { target := 169, numerator := 857489472345094194352661463040 }, { target := 170, numerator := 32155855212941032288224804864 }, { target := 283, numerator := 32155847354628056887955816448 }, { target := 284, numerator := 466259786642106824875359338496 }, { target := 285, numerator := 825333415435453460124199288832 }, { target := 286, numerator := 26796539462190047406629847040 }, { target := 287, numerator := 514493557674048910207293063168 }, { target := 288, numerator := 26796539462190047406629847040 }, { target := 289, numerator := 819974107543015450642873319424 }, { target := 290, numerator := 857489262790081517012155105280 }, { target := 291, numerator := 514493557674048910207293063168 }, { target := 292, numerator := 13135663644365561238729951019008 }, { target := 293, numerator := 841411339112767488568177197056 }, { target := 294, numerator := 466259786642106824875359338496 }, { target := 295, numerator := 819974107543015450642873319424 }, { target := 296, numerator := 26796539462190047406629847040 }, { target := 297, numerator := 841411339112767488568177197056 }, { target := 298, numerator := 26796539462190047406629847040 }, { target := 299, numerator := 819974107543015450642873319424 }, { target := 300, numerator := 857489262790081517012155105280 }, { target := 301, numerator := 32155847354628056887955816448 }]

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
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 72538768133718612799127552 }, { target := 111, numerator := 81898609183230691869982720 }, { target := 112, numerator := 70198807871340593031413760 }, { target := 113, numerator := 924284303639317808246947840 }, { target := 114, numerator := 81898609183230691869982720 }, { target := 115, numerator := 70198807871340593031413760 }, { target := 116, numerator := 81898609183230691869982720 }, { target := 117, numerator := 81898609183230691869982720 }, { target := 118, numerator := 3395282340710506682952712192 }, { target := 119, numerator := 84238569445608711637696512 }, { target := 120, numerator := 924284303639317808246947840 }, { target := 121, numerator := 3395282340710506682952712192 }, { target := 122, numerator := 72538768133718612799127552 }, { target := 123, numerator := 81898609183230691869982720 }, { target := 124, numerator := 84238569445608711637696512 }, { target := 125, numerator := 81898609183230691869982720 }, { target := 206, numerator := 11887707041255093078054666240 }, { target := 207, numerator := 13421604723997685733287526400 }, { target := 208, numerator := 11504232620569444914246451200 }, { target := 209, numerator := 151472396170831024704244940800 }, { target := 210, numerator := 13421604723997685733287526400 }, { target := 211, numerator := 11504232620569444914246451200 }, { target := 212, numerator := 13421604723997685733287526400 }, { target := 213, numerator := 13421604723997685733287526400 }, { target := 214, numerator := 556421384414875485685720023040 }, { target := 215, numerator := 13805079144683333897095741440 }, { target := 216, numerator := 151472396170831024704244940800 }, { target := 217, numerator := 556421384414875485685720023040 }, { target := 218, numerator := 11887707041255093078054666240 }, { target := 219, numerator := 13421604723997685733287526400 }, { target := 220, numerator := 13805079144683333897095741440 }, { target := 221, numerator := 13421604723997685733287526400 }, { target := 660, numerator := 804302262188705231098871808 }, { target := 661, numerator := 11662382801736225850933641216 }, { target := 662, numerator := 20643758062843434264871043072 }, { target := 663, numerator := 670251885157254359249059840 }, { target := 664, numerator := 12868836195019283697581948928 }, { target := 665, numerator := 670251885157254359249059840 }, { target := 666, numerator := 20509707685811983393021231104 }, { target := 667, numerator := 21448060325032139495969914880 }, { target := 668, numerator := 12868836195019283697581948928 }, { target := 669, numerator := 328557474104086086903889133568 }, { target := 670, numerator := 21045909193937786880420478976 }, { target := 671, numerator := 11662382801736225850933641216 }, { target := 672, numerator := 20509707685811983393021231104 }, { target := 673, numerator := 670251885157254359249059840 }, { target := 674, numerator := 21045909193937786880420478976 }, { target := 675, numerator := 670251885157254359249059840 }, { target := 676, numerator := 20509707685811983393021231104 }, { target := 677, numerator := 21448060325032139495969914880 }, { target := 678, numerator := 804302262188705231098871808 }]

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
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 8151090473966150136889344 }, { target := 258, numerator := 170154013644043384107565056 }, { target := 259, numerator := 8830348013463329314963456 }, { target := 260, numerator := 183059906894489788490973184 }, { target := 261, numerator := 274080417187111798352904192 }, { target := 262, numerator := 8490719243714739725926400 }, { target := 263, numerator := 274080417187111798352904192 }, { target := 264, numerator := 285627795358563844380164096 }, { target := 265, numerator := 170154013644043384107565056 }, { target := 266, numerator := 8490719243714739725926400 }, { target := 302, numerator := 122388546774263257857932656640 }, { target := 303, numerator := 138180617325781097581536870400 }, { target := 304, numerator := 118440529136383797927031603200 }, { target := 305, numerator := 1559466966962386672705916108800 }, { target := 306, numerator := 138180617325781097581536870400 }, { target := 307, numerator := 118440529136383797927031603200 }, { target := 308, numerator := 138180617325781097581536870400 }, { target := 309, numerator := 138180617325781097581536870400 }, { target := 310, numerator := 5728573592563096359737428541440 }, { target := 311, numerator := 142128634963660557512437923840 }, { target := 312, numerator := 1559466966962386672705916108800 }, { target := 313, numerator := 5728573592563096359737428541440 }, { target := 314, numerator := 122388546774263257857932656640 }, { target := 315, numerator := 138180617325781097581536870400 }, { target := 316, numerator := 142128634963660557512437923840 }, { target := 317, numerator := 138180617325781097581536870400 }, { target := 679, numerator := 11887707041255093078054666240 }, { target := 680, numerator := 13421604723997685733287526400 }, { target := 681, numerator := 11504232620569444914246451200 }, { target := 682, numerator := 151472396170831024704244940800 }, { target := 683, numerator := 13421604723997685733287526400 }, { target := 684, numerator := 11504232620569444914246451200 }, { target := 685, numerator := 13421604723997685733287526400 }, { target := 686, numerator := 13421604723997685733287526400 }, { target := 687, numerator := 556421384414875485685720023040 }, { target := 688, numerator := 13805079144683333897095741440 }, { target := 689, numerator := 151472396170831024704244940800 }, { target := 690, numerator := 556421384414875485685720023040 }, { target := 691, numerator := 11887707041255093078054666240 }, { target := 692, numerator := 13421604723997685733287526400 }, { target := 693, numerator := 13805079144683333897095741440 }, { target := 694, numerator := 13421604723997685733287526400 }, { target := 966, numerator := 72538768133718612799127552 }, { target := 967, numerator := 81898609183230691869982720 }, { target := 968, numerator := 70198807871340593031413760 }, { target := 969, numerator := 924284303639317808246947840 }, { target := 970, numerator := 81898609183230691869982720 }, { target := 971, numerator := 70198807871340593031413760 }, { target := 972, numerator := 81898609183230691869982720 }, { target := 973, numerator := 81898609183230691869982720 }, { target := 974, numerator := 3395282340710506682952712192 }, { target := 975, numerator := 84238569445608711637696512 }, { target := 976, numerator := 924284303639317808246947840 }, { target := 977, numerator := 3395282340710506682952712192 }, { target := 978, numerator := 72538768133718612799127552 }, { target := 979, numerator := 81898609183230691869982720 }, { target := 980, numerator := 84238569445608711637696512 }, { target := 981, numerator := 81898609183230691869982720 }]

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
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 353, numerator := 1616645211088095460668211200 }, { target := 354, numerator := 33747468781463992741448908800 }, { target := 355, numerator := 1751365645345436749057228800 }, { target := 356, numerator := 36307157032353477220840243200 }, { target := 357, numerator := 54359695222837209864968601600 }, { target := 358, numerator := 1684005428216766104862720000 }, { target := 359, numerator := 54359695222837209864968601600 }, { target := 360, numerator := 56649942605212011767581900800 }, { target := 361, numerator := 33747468781463992741448908800 }, { target := 362, numerator := 1684005428216766104862720000 }, { target := 695, numerator := 1616645211088095460668211200 }, { target := 696, numerator := 33747468781463992741448908800 }, { target := 697, numerator := 1751365645345436749057228800 }, { target := 698, numerator := 36307157032353477220840243200 }, { target := 699, numerator := 54359695222837209864968601600 }, { target := 700, numerator := 1684005428216766104862720000 }, { target := 701, numerator := 54359695222837209864968601600 }, { target := 702, numerator := 56649942605212011767581900800 }, { target := 703, numerator := 33747468781463992741448908800 }, { target := 704, numerator := 1684005428216766104862720000 }, { target := 982, numerator := 8151090473966150136889344 }, { target := 983, numerator := 170154013644043384107565056 }, { target := 984, numerator := 8830348013463329314963456 }, { target := 985, numerator := 183059906894489788490973184 }, { target := 986, numerator := 274080417187111798352904192 }, { target := 987, numerator := 8490719243714739725926400 }, { target := 988, numerator := 274080417187111798352904192 }, { target := 989, numerator := 285627795358563844380164096 }, { target := 990, numerator := 170154013644043384107565056 }, { target := 991, numerator := 8490719243714739725926400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1
