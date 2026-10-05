import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3

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
  [{ target := 14, numerator := 16320498564797493858533376 }, { target := 15, numerator := 12240373923598120393900032 }, { target := 16, numerator := 12920394697131349304672256 }, { target := 17, numerator := 16660508951564108313919488 }, { target := 18, numerator := 223046813718899082733289472 }, { target := 19, numerator := 389991913621306780327870464 }, { target := 20, numerator := 11900363536831505938513920 }, { target := 21, numerator := 223046813718899082733289472 }, { target := 22, numerator := 12580384310364734849286144 }, { target := 23, numerator := 12920394697131349304672256 }, { target := 24, numerator := 12920394697131349304672256 }, { target := 25, numerator := 12580384310364734849286144 }, { target := 26, numerator := 389991913621306780327870464 }, { target := 27, numerator := 12580384310364734849286144 }, { target := 28, numerator := 16320498564797493858533376 }, { target := 29, numerator := 16660508951564108313919488 }, { target := 40, numerator := 340690407540147684296884224 }, { target := 41, numerator := 255517805655110763222663168 }, { target := 42, numerator := 269713239302616916735033344 }, { target := 43, numerator := 347788124363900761053069312 }, { target := 44, numerator := 4656102236382018352057417728 }, { target := 45, numerator := 8141081196844779039344295936 }, { target := 46, numerator := 248420088831357686466478080 }, { target := 47, numerator := 4656102236382018352057417728 }, { target := 48, numerator := 262615522478863839978848256 }, { target := 49, numerator := 269713239302616916735033344 }, { target := 50, numerator := 269713239302616916735033344 }, { target := 51, numerator := 262615522478863839978848256 }, { target := 52, numerator := 8141081196844779039344295936 }, { target := 53, numerator := 262615522478863839978848256 }, { target := 54, numerator := 340690407540147684296884224 }, { target := 55, numerator := 347788124363900761053069312 }, { target := 75, numerator := 17680540111863951680077824 }, { target := 76, numerator := 13260405083897963760058368 }, { target := 77, numerator := 13997094255225628413394944 }, { target := 78, numerator := 18048884697527784006746112 }, { target := 79, numerator := 241634048195474006294396928 }, { target := 80, numerator := 422491239756415678688526336 }, { target := 81, numerator := 12892060498234131433390080 }, { target := 82, numerator := 241634048195474006294396928 }, { target := 83, numerator := 13628749669561796086726656 }, { target := 84, numerator := 13997094255225628413394944 }, { target := 85, numerator := 13997094255225628413394944 }, { target := 86, numerator := 13628749669561796086726656 }, { target := 87, numerator := 422491239756415678688526336 }, { target := 88, numerator := 13628749669561796086726656 }, { target := 89, numerator := 17680540111863951680077824 }, { target := 90, numerator := 18048884697527784006746112 }, { target := 136, numerator := 366531196934410382906228736 }, { target := 137, numerator := 274898397700807787179671552 }, { target := 138, numerator := 290170530906408219800764416 }, { target := 139, numerator := 374167263537210599216775168 }, { target := 140, numerator := 5009259691436941899718459392 }, { target := 141, numerator := 8758568393411848108196757504 }, { target := 142, numerator := 267262331098007570869125120 }, { target := 143, numerator := 5009259691436941899718459392 }, { target := 144, numerator := 282534464303608003490217984 }, { target := 145, numerator := 290170530906408219800764416 }, { target := 146, numerator := 290170530906408219800764416 }, { target := 147, numerator := 282534464303608003490217984 }, { target := 148, numerator := 8758568393411848108196757504 }, { target := 149, numerator := 282534464303608003490217984 }, { target := 150, numerator := 366531196934410382906228736 }, { target := 151, numerator := 374167263537210599216775168 }]

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
  [{ target := 171, numerator := 548776764241315730993184768 }, { target := 172, numerator := 411582573180986798244888576 }, { target := 173, numerator := 434448271691041620369604608 }, { target := 174, numerator := 560209613496343142055542784 }, { target := 175, numerator := 7499949111297981656906858496 }, { target := 176, numerator := 13113478095516440488524644352 }, { target := 177, numerator := 400149723925959387182530560 }, { target := 178, numerator := 7499949111297981656906858496 }, { target := 179, numerator := 423015422436014209307246592 }, { target := 180, numerator := 434448271691041620369604608 }, { target := 181, numerator := 434448271691041620369604608 }, { target := 182, numerator := 423015422436014209307246592 }, { target := 183, numerator := 13113478095516440488524644352 }, { target := 184, numerator := 423015422436014209307246592 }, { target := 185, numerator := 548776764241315730993184768 }, { target := 186, numerator := 560209613496343142055542784 }, { target := 267, numerator := 17000519338330722769305600 }, { target := 268, numerator := 12750389503748042076979200 }, { target := 269, numerator := 13458744476178488859033600 }, { target := 270, numerator := 17354696824545946160332800 }, { target := 271, numerator := 232340430957186544513843200 }, { target := 272, numerator := 406241576688861229508198400 }, { target := 273, numerator := 12396212017532818685952000 }, { target := 274, numerator := 232340430957186544513843200 }, { target := 275, numerator := 13104566989963265468006400 }, { target := 276, numerator := 13458744476178488859033600 }, { target := 277, numerator := 13458744476178488859033600 }, { target := 278, numerator := 13104566989963265468006400 }, { target := 279, numerator := 406241576688861229508198400 }, { target := 280, numerator := 13104566989963265468006400 }, { target := 281, numerator := 17000519338330722769305600 }, { target := 282, numerator := 17354696824545946160332800 }, { target := 403, numerator := 548776764241315730993184768 }, { target := 404, numerator := 411582573180986798244888576 }, { target := 405, numerator := 434448271691041620369604608 }, { target := 406, numerator := 560209613496343142055542784 }, { target := 407, numerator := 7499949111297981656906858496 }, { target := 408, numerator := 13113478095516440488524644352 }, { target := 409, numerator := 400149723925959387182530560 }, { target := 410, numerator := 7499949111297981656906858496 }, { target := 411, numerator := 423015422436014209307246592 }, { target := 412, numerator := 434448271691041620369604608 }, { target := 413, numerator := 434448271691041620369604608 }, { target := 414, numerator := 423015422436014209307246592 }, { target := 415, numerator := 13113478095516440488524644352 }, { target := 416, numerator := 423015422436014209307246592 }, { target := 417, numerator := 548776764241315730993184768 }, { target := 418, numerator := 560209613496343142055542784 }, { target := 438, numerator := 571897470541445513959440384 }, { target := 439, numerator := 428923102906084135469580288 }, { target := 440, numerator := 452752164178644365217890304 }, { target := 441, numerator := 583812001177725628833595392 }, { target := 442, numerator := 7815932097399755357445685248 }, { target := 443, numerator := 13665966639813291760655794176 }, { target := 444, numerator := 417008572269804020595425280 }, { target := 445, numerator := 7815932097399755357445685248 }, { target := 446, numerator := 440837633542364250343735296 }, { target := 447, numerator := 452752164178644365217890304 }, { target := 448, numerator := 452752164178644365217890304 }, { target := 449, numerator := 440837633542364250343735296 }, { target := 450, numerator := 13665966639813291760655794176 }, { target := 451, numerator := 440837633542364250343735296 }, { target := 452, numerator := 571897470541445513959440384 }, { target := 453, numerator := 583812001177725628833595392 }]

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
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 139763914743517041836163072 }, { target := 57, numerator := 16519197405721353243404009472 }, { target := 59, numerator := 156763890498958008055435886592 }, { target := 67, numerator := 16519208735480979014889242624 }, { target := 74, numerator := 139763914743517041836163072 }, { target := 91, numerator := 157797968258809563363409920 }, { target := 92, numerator := 18650706748395076242552913920 }, { target := 94, numerator := 176991489273017105869040517120 }, { target := 102, numerator := 18650719540059169855520112640 }, { target := 109, numerator := 157797968258809563363409920 }, { target := 152, numerator := 135255401364693911454351360 }, { target := 153, numerator := 15986320070052922493616783360 }, { target := 155, numerator := 151706990805443233602034728960 }, { target := 163, numerator := 15986331034336431304731525120 }, { target := 170, numerator := 135255401364693911454351360 }, { target := 187, numerator := 1780862784635136500815626240 }, { target := 188, numerator := 210486547589030146165954314240 }, { target := 190, numerator := 1997475378938335909093457264640 }, { target := 198, numerator := 210486691952096345512298414080 }, { target := 205, numerator := 1780862784635136500815626240 }, { target := 222, numerator := 157797968258809563363409920 }, { target := 223, numerator := 18650706748395076242552913920 }, { target := 225, numerator := 176991489273017105869040517120 }, { target := 233, numerator := 18650719540059169855520112640 }, { target := 240, numerator := 157797968258809563363409920 }, { target := 283, numerator := 135255401364693911454351360 }, { target := 284, numerator := 15986320070052922493616783360 }, { target := 286, numerator := 151706990805443233602034728960 }, { target := 294, numerator := 15986331034336431304731525120 }, { target := 301, numerator := 135255401364693911454351360 }, { target := 534, numerator := 340690407540147684296884224 }, { target := 535, numerator := 255517805655110763222663168 }, { target := 536, numerator := 269713239302616916735033344 }, { target := 537, numerator := 347788124363900761053069312 }, { target := 538, numerator := 4656102236382018352057417728 }, { target := 539, numerator := 8141081196844779039344295936 }, { target := 540, numerator := 248420088831357686466478080 }, { target := 541, numerator := 4656102236382018352057417728 }, { target := 542, numerator := 262615522478863839978848256 }, { target := 543, numerator := 269713239302616916735033344 }, { target := 544, numerator := 269713239302616916735033344 }, { target := 545, numerator := 262615522478863839978848256 }, { target := 546, numerator := 8141081196844779039344295936 }, { target := 547, numerator := 262615522478863839978848256 }, { target := 548, numerator := 340690407540147684296884224 }, { target := 549, numerator := 347788124363900761053069312 }, { target := 750, numerator := 17000519338330722769305600 }, { target := 751, numerator := 12750389503748042076979200 }, { target := 752, numerator := 13458744476178488859033600 }, { target := 753, numerator := 17354696824545946160332800 }, { target := 754, numerator := 232340430957186544513843200 }, { target := 755, numerator := 406241576688861229508198400 }, { target := 756, numerator := 12396212017532818685952000 }, { target := 757, numerator := 232340430957186544513843200 }, { target := 758, numerator := 13104566989963265468006400 }, { target := 759, numerator := 13458744476178488859033600 }, { target := 760, numerator := 13458744476178488859033600 }, { target := 761, numerator := 13104566989963265468006400 }, { target := 762, numerator := 406241576688861229508198400 }, { target := 763, numerator := 13104566989963265468006400 }, { target := 764, numerator := 17000519338330722769305600 }, { target := 765, numerator := 17354696824545946160332800 }]

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
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 3300836150139560330243604480 }, { target := 112, numerator := 129178090866509963150757986304 }, { target := 115, numerator := 129178090866509963150757986304 }, { target := 122, numerator := 3300836150139560330243604480 }, { target := 206, numerator := 47862124177023624788532264960 }, { target := 208, numerator := 1873082317564394465685990801408 }, { target := 211, numerator := 1873082317564394465685990801408 }, { target := 218, numerator := 47862124177023624788532264960 }, { target := 241, numerator := 84721461186915381809585848320 }, { target := 243, numerator := 3315570998907089054202788315136 }, { target := 246, numerator := 3315570998907089054202788315136 }, { target := 253, numerator := 84721461186915381809585848320 }, { target := 318, numerator := 157797968258809563363409920 }, { target := 319, numerator := 18650706748395076242552913920 }, { target := 321, numerator := 176991489273017105869040517120 }, { target := 329, numerator := 18650719540059169855520112640 }, { target := 336, numerator := 157797968258809563363409920 }, { target := 419, numerator := 157797968258809563363409920 }, { target := 420, numerator := 18650706748395076242552913920 }, { target := 422, numerator := 176991489273017105869040517120 }, { target := 430, numerator := 18650719540059169855520112640 }, { target := 437, numerator := 157797968258809563363409920 }, { target := 454, numerator := 6541852912672362184008794112 }, { target := 455, numerator := 773205014054893017941265088512 }, { target := 457, numerator := 7337561455289937731885079724032 }, { target := 465, numerator := 773205544360738727438848098304 }, { target := 472, numerator := 6541852912672362184008794112 }, { target := 489, numerator := 162306481637632693745221632 }, { target := 490, numerator := 19183584084063506992340140032 }, { target := 492, numerator := 182048388966531880322441674752 }, { target := 500, numerator := 19183597241203717565677830144 }, { target := 507, numerator := 162306481637632693745221632 }, { target := 550, numerator := 1780862784635136500815626240 }, { target := 551, numerator := 210486547589030146165954314240 }, { target := 553, numerator := 1997475378938335909093457264640 }, { target := 561, numerator := 210486691952096345512298414080 }, { target := 568, numerator := 1780862784635136500815626240 }, { target := 585, numerator := 6541852912672362184008794112 }, { target := 586, numerator := 773205014054893017941265088512 }, { target := 588, numerator := 7337561455289937731885079724032 }, { target := 596, numerator := 773205544360738727438848098304 }, { target := 603, numerator := 6541852912672362184008794112 }, { target := 660, numerator := 139763914743517041836163072 }, { target := 661, numerator := 16519197405721353243404009472 }, { target := 663, numerator := 156763890498958008055435886592 }, { target := 671, numerator := 16519208735480979014889242624 }, { target := 678, numerator := 139763914743517041836163072 }, { target := 766, numerator := 157797968258809563363409920 }, { target := 767, numerator := 18650706748395076242552913920 }, { target := 769, numerator := 176991489273017105869040517120 }, { target := 777, numerator := 18650719540059169855520112640 }, { target := 784, numerator := 157797968258809563363409920 }, { target := 801, numerator := 162306481637632693745221632 }, { target := 802, numerator := 19183584084063506992340140032 }, { target := 804, numerator := 182048388966531880322441674752 }, { target := 812, numerator := 19183597241203717565677830144 }, { target := 819, numerator := 162306481637632693745221632 }, { target := 876, numerator := 157797968258809563363409920 }, { target := 877, numerator := 18650706748395076242552913920 }, { target := 879, numerator := 176991489273017105869040517120 }, { target := 887, numerator := 18650719540059169855520112640 }, { target := 894, numerator := 157797968258809563363409920 }]

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
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 302, numerator := 2750696791782966941869670400 }, { target := 304, numerator := 107648409055424969292298321920 }, { target := 307, numerator := 107648409055424969292298321920 }, { target := 314, numerator := 2750696791782966941869670400 }, { target := 337, numerator := 52813378402232965283897671680 }, { target := 339, numerator := 2066849453864159410412127780864 }, { target := 342, numerator := 2066849453864159410412127780864 }, { target := 349, numerator := 52813378402232965283897671680 }, { target := 363, numerator := 2750696791782966941869670400 }, { target := 365, numerator := 107648409055424969292298321920 }, { target := 368, numerator := 107648409055424969292298321920 }, { target := 375, numerator := 2750696791782966941869670400 }, { target := 473, numerator := 84171321828558788421211914240 }, { target := 475, numerator := 3294041317096004060344328650752 }, { target := 478, numerator := 3294041317096004060344328650752 }, { target := 485, numerator := 84171321828558788421211914240 }, { target := 508, numerator := 88022297337054942139829452800 }, { target := 510, numerator := 3444749089773599017353546301440 }, { target := 513, numerator := 3444749089773599017353546301440 }, { target := 520, numerator := 88022297337054942139829452800 }, { target := 569, numerator := 52813378402232965283897671680 }, { target := 571, numerator := 2066849453864159410412127780864 }, { target := 574, numerator := 2066849453864159410412127780864 }, { target := 581, numerator := 52813378402232965283897671680 }, { target := 604, numerator := 1348391567332010394904512430080 }, { target := 606, numerator := 52769250118969319947084637405184 }, { target := 609, numerator := 52769250118969319947084637405184 }, { target := 616, numerator := 1348391567332010394904512430080 }, { target := 630, numerator := 86371879261985161974707650560 }, { target := 632, numerator := 3380160044340344035778167308288 }, { target := 635, numerator := 3380160044340344035778167308288 }, { target := 642, numerator := 86371879261985161974707650560 }, { target := 679, numerator := 47862124177023624788532264960 }, { target := 681, numerator := 1873082317564394465685990801408 }, { target := 684, numerator := 1873082317564394465685990801408 }, { target := 691, numerator := 47862124177023624788532264960 }, { target := 705, numerator := 84171321828558788421211914240 }, { target := 707, numerator := 3294041317096004060344328650752 }, { target := 710, numerator := 3294041317096004060344328650752 }, { target := 717, numerator := 84171321828558788421211914240 }, { target := 785, numerator := 2750696791782966941869670400 }, { target := 787, numerator := 107648409055424969292298321920 }, { target := 790, numerator := 107648409055424969292298321920 }, { target := 797, numerator := 2750696791782966941869670400 }, { target := 820, numerator := 86371879261985161974707650560 }, { target := 822, numerator := 3380160044340344035778167308288 }, { target := 825, numerator := 3380160044340344035778167308288 }, { target := 832, numerator := 86371879261985161974707650560 }, { target := 846, numerator := 2750696791782966941869670400 }, { target := 848, numerator := 107648409055424969292298321920 }, { target := 851, numerator := 107648409055424969292298321920 }, { target := 858, numerator := 2750696791782966941869670400 }, { target := 895, numerator := 84171321828558788421211914240 }, { target := 897, numerator := 3294041317096004060344328650752 }, { target := 900, numerator := 3294041317096004060344328650752 }, { target := 907, numerator := 84171321828558788421211914240 }, { target := 921, numerator := 88022297337054942139829452800 }, { target := 923, numerator := 3444749089773599017353546301440 }, { target := 926, numerator := 3444749089773599017353546301440 }, { target := 933, numerator := 88022297337054942139829452800 }, { target := 966, numerator := 3300836150139560330243604480 }, { target := 968, numerator := 129178090866509963150757986304 }, { target := 971, numerator := 129178090866509963150757986304 }, { target := 978, numerator := 3300836150139560330243604480 }]

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
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
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
  [{ target := 257, numerator := 96407055397592347873351041024 }, { target := 260, numerator := 358128185894399017866221322240 }, { target := 262, numerator := 96386761816230524724128514048 }, { target := 353, numerator := 71792488062036854799303966720 }, { target := 356, numerator := 266691202261786502666335027200 }, { target := 358, numerator := 71777375820597199262648893440 }, { target := 379, numerator := 75894915951296103644978479104 }, { target := 382, numerator := 281930699533888588532982743040 }, { target := 384, numerator := 75878940153202753506228830208 }, { target := 389, numerator := 8094966323144257597901635584 }, { target := 391, numerator := 8094968253134856309763473408 }, { target := 524, numerator := 98458269342221972296188297216 }, { target := 527, numerator := 365747934530450060799545180160 }, { target := 529, numerator := 98437543982533301845918482432 }, { target := 620, numerator := 1318930566396848503884355731456 }, { target := 623, numerator := 4899498372980820606127240642560 }, { target := 625, numerator := 1318652932932685689310949670912 }, { target := 646, numerator := 2385561817604253203759728951296 }, { target := 649, numerator := 8861767663727362931455646760960 }, { target := 651, numerator := 2385059659410129792641733230592 }, { target := 656, numerator := 198457238889988250787265904640 }, { target := 658, numerator := 198457286205886799852265799680 }, { target := 695, numerator := 71792488062036854799303966720 }, { target := 698, numerator := 266691202261786502666335027200 }, { target := 700, numerator := 71777375820597199262648893440 }, { target := 721, numerator := 1318930566396848503884355731456 }, { target := 724, numerator := 4899498372980820606127240642560 }, { target := 726, numerator := 1318652932932685689310949670912 }, { target := 731, numerator := 146753905600228153871636103168 }, { target := 733, numerator := 146753940589089975680228130816 }, { target := 735, numerator := 77946129895925728067815735296 }, { target := 738, numerator := 289550448169939631466306600960 }, { target := 740, numerator := 77929722319505530628018798592 }, { target := 745, numerator := 163727222084240306899494371328 }, { target := 747, numerator := 163727261119856609878119284736 }, { target := 836, numerator := 77946129895925728067815735296 }, { target := 839, numerator := 289550448169939631466306600960 }, { target := 841, numerator := 77929722319505530628018798592 }, { target := 862, numerator := 75894915951296103644978479104 }, { target := 865, numerator := 281930699533888588532982743040 }, { target := 867, numerator := 75878940153202753506228830208 }, { target := 872, numerator := 8094966323144257597901635584 }, { target := 874, numerator := 8094968253134856309763473408 }, { target := 911, numerator := 75894915951296103644978479104 }, { target := 914, numerator := 281930699533888588532982743040 }, { target := 916, numerator := 75878940153202753506228830208 }, { target := 937, numerator := 2385561817604253203759728951296 }, { target := 940, numerator := 8861767663727362931455646760960 }, { target := 942, numerator := 2385059659410129792641733230592 }, { target := 947, numerator := 163466094138332427622142705664 }, { target := 949, numerator := 163466133111690969351997882368 }, { target := 951, numerator := 75894915951296103644978479104 }, { target := 954, numerator := 281930699533888588532982743040 }, { target := 956, numerator := 75878940153202753506228830208 }, { target := 961, numerator := 166338501543319099673011027968 }, { target := 963, numerator := 166338541201513015139333308416 }, { target := 982, numerator := 96407055397592347873351041024 }, { target := 985, numerator := 358128185894399017866221322240 }, { target := 987, numerator := 96386761816230524724128514048 }, { target := 992, numerator := 8094966323144257597901635584 }, { target := 994, numerator := 8094968253134856309763473408 }, { target := 996, numerator := 98458269342221972296188297216 }, { target := 999, numerator := 365747934530450060799545180160 }, { target := 1001, numerator := 98437543982533301845918482432 }]

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
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 4218794020191472200613625856 }, { target := 15, numerator := 739936835395674651269013700608 }, { target := 20, numerator := 739936924105938549148867362816 }, { target := 28, numerator := 4218705309927574320759963648 }, { target := 56, numerator := 819697386743315113873244160 }, { target := 57, numerator := 264042036369544470928577003520 }, { target := 59, numerator := 2808198093953100944481982611456 }, { target := 67, numerator := 264042832192250046962668142592 }, { target := 74, numerator := 819697386743315113873244160 }, { target := 110, numerator := 2976672959231129610256121856 }, { target := 112, numerator := 116495364270539831731357220864 }, { target := 115, numerator := 116495406997085149971146080256 }, { target := 122, numerator := 2976715685776447850044981248 }, { target := 136, numerator := 15368056901300858551235772416 }, { target := 137, numerator := 2695412796952129602784946290688 }, { target := 142, numerator := 2695413120102389318512568958976 }, { target := 150, numerator := 15367733751041142823613104128 }, { target := 152, numerator := 32771349436239737504692961280 }, { target := 153, numerator := 10556351623983302240771411804160 }, { target := 155, numerator := 112271238766237265300871287144448 }, { target := 163, numerator := 10556383440827415094885494030336 }, { target := 170, numerator := 32771349436239737504692961280 }, { target := 206, numerator := 487819368971568482750268702720 }, { target := 208, numerator := 19091346568770026090757022023680 }, { target := 211, numerator := 19091353570827914526889575710720 }, { target := 218, numerator := 487826371029456918882822389760 }, { target := 257, numerator := 22596511094229100403422658560 }, { target := 260, numerator := 80994817727528836095562219520 }, { target := 262, numerator := 22603077601855146001275289600 }, { target := 267, numerator := 4218796858045831295491112960 }, { target := 268, numerator := 739937333128667476356528865280 }, { target := 273, numerator := 739937421838991046931445186560 }, { target := 281, numerator := 4218708147722260720574791680 }, { target := 283, numerator := 32771341427511038149876776960 }, { target := 284, numerator := 10556349044200727953938705285120 }, { target := 286, numerator := 112271211329164716040233141927936 }, { target := 294, numerator := 10556380861037065343296132349952 }, { target := 301, numerator := 32771341427511038149876776960 }, { target := 302, numerator := 5022289281656536792983058513920 }, { target := 304, numerator := 196552804877069769039927553556480 }, { target := 307, numerator := 196552876965966847419338373201920 }, { target := 314, numerator := 5022361370553615172393878159360 }, { target := 660, numerator := 819697386743315113873244160 }, { target := 661, numerator := 264042036369544470928577003520 }, { target := 663, numerator := 2808198093953100944481982611456 }, { target := 671, numerator := 264042832192250046962668142592 }, { target := 678, numerator := 819697386743315113873244160 }, { target := 679, numerator := 487819368971568482750268702720 }, { target := 681, numerator := 19091346568770026090757022023680 }, { target := 684, numerator := 19091353570827914526889575710720 }, { target := 691, numerator := 487826371029456918882822389760 }, { target := 749, numerator := 19884411881021420665567182848 }, { target := 965, numerator := 19826383441679918465181286400 }, { target := 966, numerator := 2976672959231129610256121856 }, { target := 968, numerator := 116495364270539831731357220864 }, { target := 971, numerator := 116495406997085149971146080256 }, { target := 978, numerator := 2976715685776447850044981248 }, { target := 1006, numerator := 198457238889988250787265904640 }, { target := 1008, numerator := 198457286205886799852265799680 }, { target := 1010, numerator := 19690983749883079997614194688 }, { target := 1011, numerator := 8094966323144257597901635584 }, { target := 1013, numerator := 8094968253134856309763473408 }, { target := 1015, numerator := 19826383441679918465181286400 }]

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
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left7.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 6713748248739576104794193920 }, { target := 6, numerator := 303449206918725587164903505920 }, { target := 11, numerator := 6749581552796598232992972800 }, { target := 14, numerator := 22347415696339960713936109568 }, { target := 15, numerator := 4432271078461466402059871846400 }, { target := 20, numerator := 4432271078461466402059871846400 }, { target := 28, numerator := 22347415696339960713936109568 }, { target := 56, numerator := 2969822158404360612303863808 }, { target := 57, numerator := 486696654658630465528749096960 }, { target := 59, numerator := 5010730503102666742826595778560 }, { target := 67, numerator := 486696654658630465528749096960 }, { target := 74, numerator := 2969822158404360612303863808 }, { target := 110, numerator := 818273064611702055465123840 }, { target := 112, numerator := 32714405301685020323972382720 }, { target := 115, numerator := 32714397306872443817731031040 }, { target := 122, numerator := 818273064611702055465123840 }, { target := 126, numerator := 6713753050788247181505593344 }, { target := 128, numerator := 303449423962589437275085471744 }, { target := 133, numerator := 6749586380475254789069864960 }, { target := 136, numerator := 80101961469115132390571769856 }, { target := 137, numerator := 15887009575149256953549343948800 }, { target := 142, numerator := 15887009575149256953549343948800 }, { target := 150, numerator := 80101961469115132390571769856 }, { target := 152, numerator := 116227250658870004730824753152 }, { target := 153, numerator := 19047407911534652037613737738240 }, { target := 155, numerator := 196100439388284798340180884848640 }, { target := 163, numerator := 19047407911534652037613737738240 }, { target := 170, numerator := 116227250658870004730824753152 }, { target := 206, numerator := 263583231788537443177180692480 }, { target := 208, numerator := 10538008701960742202125414563840 }, { target := 211, numerator := 10538006126660848322394068090880 }, { target := 218, numerator := 263583231788537443177180692480 }, { target := 267, numerator := 22353909817267766439056506880 }, { target := 268, numerator := 4433559088885555789220020224000 }, { target := 273, numerator := 4433559088885555789220020224000 }, { target := 281, numerator := 22353909817267766439056506880 }, { target := 283, numerator := 116227293287080351006885675008 }, { target := 284, numerator := 19047414897477332445124582440960 }, { target := 286, numerator := 196100511311269570440237479362560 }, { target := 294, numerator := 19047414897477332445124582440960 }, { target := 301, numerator := 116227293287080351006885675008 }, { target := 353, numerator := 4481675373922024148579647488000 }, { target := 356, numerator := 16064094076783086250802282496000 }, { target := 358, numerator := 4482977741150203704068014080000 }, { target := 389, numerator := 6713748248739576104794193920 }, { target := 391, numerator := 6713753050788247181505593344 }, { target := 660, numerator := 2969864786614706888364785664 }, { target := 661, numerator := 486703640601310873039593799680 }, { target := 663, numerator := 5010802426087438842883190292480 }, { target := 671, numerator := 486703640601310873039593799680 }, { target := 678, numerator := 2969864786614706888364785664 }, { target := 695, numerator := 4481675373922024148579647488000 }, { target := 698, numerator := 16064094076783086250802282496000 }, { target := 700, numerator := 4482977741150203704068014080000 }, { target := 731, numerator := 303449206918725587164903505920 }, { target := 733, numerator := 303449423962589437275085471744 }, { target := 982, numerator := 22596511094229100403422658560 }, { target := 985, numerator := 80994817727528836095562219520 }, { target := 987, numerator := 22603077601855146001275289600 }, { target := 992, numerator := 6749581552796598232992972800 }, { target := 994, numerator := 6749586380475254789069864960 }]

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
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left6.expected,
    Slot18.Left14.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19884411881021420665567182848 }, { target := 1, numerator := 19826383441679918465181286400 }, { target := 2, numerator := 19690983749883079997614194688 }, { target := 3, numerator := 19826383441679918465181286400 }, { target := 4, numerator := 7795152755620396205386760192 }, { target := 5, numerator := 191106970782951648906256056320 }, { target := 6, numerator := 141318575763182666691205136384 }, { target := 7, numerator := 157663250895935110347661246464 }, { target := 8, numerator := 7795152755620396205386760192 }, { target := 9, numerator := 157411794355431226599100383232 }, { target := 10, numerator := 160177816300973947833269878784 }, { target := 11, numerator := 7795152755620396205386760192 }, { target := 12, numerator := 191106970782951648906256056320 }, { target := 13, numerator := 7795152755620396205386760192 }, { target := 14, numerator := 95611617646787130481656725504 }, { target := 15, numerator := 71200140800798926954425221120 }, { target := 16, numerator := 75268720275130294208963805184 }, { target := 17, numerator := 97645907383952814108926017536 }, { target := 18, numerator := 1308048300997534572334154776576 }, { target := 19, numerator := 2365878964323690058514186633216 }, { target := 20, numerator := 71200140800798926954425221120 }, { target := 21, numerator := 1308048300997534572334154776576 }, { target := 22, numerator := 77303010012295977836233097216 }, { target := 23, numerator := 77303010012295977836233097216 }, { target := 24, numerator := 75268720275130294208963805184 }, { target := 25, numerator := 75268720275130294208963805184 }, { target := 26, numerator := 2365878964323690058514186633216 }, { target := 27, numerator := 75268720275130294208963805184 }, { target := 28, numerator := 95611617646787130481656725504 }, { target := 29, numerator := 97645907383952814108926017536 }, { target := 126, numerator := 7795154614129861631624085504 }, { target := 127, numerator := 191107016346409510968848547840 }, { target := 128, numerator := 141318609456160717321701163008 }, { target := 129, numerator := 157663288485787846549300051968 }, { target := 130, numerator := 7795154614129861631624085504 }, { target := 131, numerator := 157411831885332044561183145984 }, { target := 132, numerator := 160177854490345866430469111808 }, { target := 133, numerator := 7795154614129861631624085504 }, { target := 134, numerator := 191107016346409510968848547840 }, { target := 135, numerator := 7795154614129861631624085504 }, { target := 257, numerator := 4178994076604760198721044480 }, { target := 260, numerator := 15223075232420661772450529280 }, { target := 262, numerator := 4178996887686908358741196800 }, { target := 302, numerator := 2803318514293755851615810617344 }, { target := 304, numerator := 112076154076808529826847184125952 }, { target := 307, numerator := 112076126687411171789946029604864 }, { target := 314, numerator := 2803318514293755851615810617344 }, { target := 353, numerator := 732956299212696588521192816640 }, { target := 356, numerator := 2669984374339373663136031703040 }, { target := 358, numerator := 732956792250095141673920102400 }, { target := 679, numerator := 263584026228405998227719979008 }, { target := 681, numerator := 10538040463519287527387865022464 }, { target := 684, numerator := 10538037888211631693698745499648 }, { target := 691, numerator := 263584026228405998227719979008 }, { target := 695, numerator := 732956387086071204345576161280 }, { target := 698, numerator := 2669984694441046023054903214080 }, { target := 700, numerator := 732956880123528867243412684800 }, { target := 966, numerator := 818273064611702055465123840 }, { target := 968, numerator := 32714405301685020323972382720 }, { target := 971, numerator := 32714397306872443817731031040 }, { target := 978, numerator := 818273064611702055465123840 }, { target := 982, numerator := 4178906203230144374337699840 }, { target := 985, numerator := 15222755130748301853579018240 }, { target := 987, numerator := 4178909014253182789248614400 }]

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
    Slot22.Left3.expected,
    Slot22.Left5.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 3319631975786434742986997760 }, { target := 57, numerator := 48134663648903303773311467520 }, { target := 58, numerator := 85203887378518491736666275840 }, { target := 59, numerator := 2766359979822028952489164800 }, { target := 60, numerator := 53114111612582955887791964160 }, { target := 61, numerator := 2766359979822028952489164800 }, { target := 62, numerator := 84650615382554085946168442880 }, { target := 63, numerator := 88523519354304926479653273600 }, { target := 64, numerator := 53114111612582955887791964160 }, { target := 65, numerator := 1356069662108758592510188584960 }, { target := 66, numerator := 86863703366411709108159774720 }, { target := 67, numerator := 48134663648903303773311467520 }, { target := 68, numerator := 84650615382554085946168442880 }, { target := 69, numerator := 2766359979822028952489164800 }, { target := 70, numerator := 86863703366411709108159774720 }, { target := 71, numerator := 2766359979822028952489164800 }, { target := 72, numerator := 84650615382554085946168442880 }, { target := 73, numerator := 88523519354304926479653273600 }, { target := 74, numerator := 3319631975786434742986997760 }, { target := 136, numerator := 355173332875468332900328407040 }, { target := 137, numerator := 264490779800880673436414771200 }, { target := 138, numerator := 279604538646645283347067043840 }, { target := 139, numerator := 362730212298350637855654543360 }, { target := 140, numerator := 4859073468913322086274705653760 }, { target := 141, numerator := 8788650768812120663044296540160 }, { target := 142, numerator := 264490779800880673436414771200 }, { target := 143, numerator := 4859073468913322086274705653760 }, { target := 144, numerator := 287161418069527588302393180160 }, { target := 145, numerator := 287161418069527588302393180160 }, { target := 146, numerator := 279604538646645283347067043840 }, { target := 147, numerator := 279604538646645283347067043840 }, { target := 148, numerator := 8788650768812120663044296540160 }, { target := 149, numerator := 279604538646645283347067043840 }, { target := 150, numerator := 355173332875468332900328407040 }, { target := 151, numerator := 362730212298350637855654543360 }, { target := 267, numerator := 95591491504215421384820523008 }, { target := 268, numerator := 71185153247819994648270602240 }, { target := 269, numerator := 75252876290552565771028922368 }, { target := 270, numerator := 97625353025581706946199683072 }, { target := 271, numerator := 1307772958238521615966799921152 }, { target := 272, numerator := 2365380949348990107883963154432 }, { target := 273, numerator := 71185153247819994648270602240 }, { target := 274, numerator := 1307772958238521615966799921152 }, { target := 275, numerator := 77286737811918851332408082432 }, { target := 276, numerator := 77286737811918851332408082432 }, { target := 277, numerator := 75252876290552565771028922368 }, { target := 278, numerator := 75252876290552565771028922368 }, { target := 279, numerator := 2365380949348990107883963154432 }, { target := 280, numerator := 75252876290552565771028922368 }, { target := 281, numerator := 95591491504215421384820523008 }, { target := 282, numerator := 97625353025581706946199683072 }]

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
    Slot23.Left2.expected,
    Slot23.Left5.expected,
    Slot23.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 129913664752302617343031246848 }, { target := 153, numerator := 1883748138908387951473953079296 }, { target := 154, numerator := 3334450728642433845137802002432 }, { target := 155, numerator := 108261387293585514452526039040 }, { target := 156, numerator := 2078618636036841877488499949568 }, { target := 157, numerator := 108261387293585514452526039040 }, { target := 158, numerator := 3312798451183716742247296794624 }, { target := 159, numerator := 3464364393394736462480833249280 }, { target := 160, numerator := 2078618636036841877488499949568 }, { target := 161, numerator := 53069732051315619184628264337408 }, { target := 162, numerator := 3399407561018585153809317625856 }, { target := 163, numerator := 1883748138908387951473953079296 }, { target := 164, numerator := 3312798451183716742247296794624 }, { target := 165, numerator := 108261387293585514452526039040 }, { target := 166, numerator := 3399407561018585153809317625856 }, { target := 167, numerator := 108261387293585514452526039040 }, { target := 168, numerator := 3312798451183716742247296794624 }, { target := 169, numerator := 3464364393394736462480833249280 }, { target := 170, numerator := 129913664752302617343031246848 }, { target := 283, numerator := 129913664752302617343031246848 }, { target := 284, numerator := 1883748138908387951473953079296 }, { target := 285, numerator := 3334450728642433845137802002432 }, { target := 286, numerator := 108261387293585514452526039040 }, { target := 287, numerator := 2078618636036841877488499949568 }, { target := 288, numerator := 108261387293585514452526039040 }, { target := 289, numerator := 3312798451183716742247296794624 }, { target := 290, numerator := 3464364393394736462480833249280 }, { target := 291, numerator := 2078618636036841877488499949568 }, { target := 292, numerator := 53069732051315619184628264337408 }, { target := 293, numerator := 3399407561018585153809317625856 }, { target := 294, numerator := 1883748138908387951473953079296 }, { target := 295, numerator := 3312798451183716742247296794624 }, { target := 296, numerator := 108261387293585514452526039040 }, { target := 297, numerator := 3399407561018585153809317625856 }, { target := 298, numerator := 108261387293585514452526039040 }, { target := 299, numerator := 3312798451183716742247296794624 }, { target := 300, numerator := 3464364393394736462480833249280 }, { target := 301, numerator := 129913664752302617343031246848 }, { target := 660, numerator := 3319631975786434742986997760 }, { target := 661, numerator := 48134663648903303773311467520 }, { target := 662, numerator := 85203887378518491736666275840 }, { target := 663, numerator := 2766359979822028952489164800 }, { target := 664, numerator := 53114111612582955887791964160 }, { target := 665, numerator := 2766359979822028952489164800 }, { target := 666, numerator := 84650615382554085946168442880 }, { target := 667, numerator := 88523519354304926479653273600 }, { target := 668, numerator := 53114111612582955887791964160 }, { target := 669, numerator := 1356069662108758592510188584960 }, { target := 670, numerator := 86863703366411709108159774720 }, { target := 671, numerator := 48134663648903303773311467520 }, { target := 672, numerator := 84650615382554085946168442880 }, { target := 673, numerator := 2766359979822028952489164800 }, { target := 674, numerator := 86863703366411709108159774720 }, { target := 675, numerator := 2766359979822028952489164800 }, { target := 676, numerator := 84650615382554085946168442880 }, { target := 677, numerator := 88523519354304926479653273600 }, { target := 678, numerator := 3319631975786434742986997760 }]

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
    Slot24.Left0.expected,
    Slot24.Left1.expected,
    Slot24.Left3.expected,
    Slot24.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 141527497263939969808859136 }, { target := 111, numerator := 159789109814125772364840960 }, { target := 112, numerator := 136962094126393519169863680 }, { target := 113, numerator := 1803334239330848002403205120 }, { target := 114, numerator := 159789109814125772364840960 }, { target := 115, numerator := 136962094126393519169863680 }, { target := 116, numerator := 159789109814125772364840960 }, { target := 117, numerator := 159789109814125772364840960 }, { target := 118, numerator := 6624399952579899877182406656 }, { target := 119, numerator := 164354512951672223003836416 }, { target := 120, numerator := 1803334239330848002403205120 }, { target := 121, numerator := 6624399952579899877182406656 }, { target := 122, numerator := 141527497263939969808859136 }, { target := 123, numerator := 159789109814125772364840960 }, { target := 124, numerator := 164354512951672223003836416 }, { target := 125, numerator := 159789109814125772364840960 }, { target := 206, numerator := 16727641537023830886853902336 }, { target := 207, numerator := 18886046896639809065802792960 }, { target := 208, numerator := 16188040197119836342116679680 }, { target := 209, numerator := 213142529262077845171202949120 }, { target := 210, numerator := 18886046896639809065802792960 }, { target := 211, numerator := 16188040197119836342116679680 }, { target := 212, numerator := 18886046896639809065802792960 }, { target := 213, numerator := 18886046896639809065802792960 }, { target := 214, numerator := 782961544200696084413710073856 }, { target := 215, numerator := 19425648236543803610540015616 }, { target := 216, numerator := 213142529262077845171202949120 }, { target := 217, numerator := 782961544200696084413710073856 }, { target := 218, numerator := 16727641537023830886853902336 }, { target := 219, numerator := 18886046896639809065802792960 }, { target := 220, numerator := 19425648236543803610540015616 }, { target := 221, numerator := 18886046896639809065802792960 }, { target := 302, numerator := 158741983754465364623958736896 }, { target := 303, numerator := 179224820367944766510921154560 }, { target := 304, numerator := 153621274601095514152218132480 }, { target := 305, numerator := 2022680115581090936337538744320 }, { target := 306, numerator := 179224820367944766510921154560 }, { target := 307, numerator := 153621274601095514152218132480 }, { target := 308, numerator := 179224820367944766510921154560 }, { target := 309, numerator := 179224820367944766510921154560 }, { target := 310, numerator := 7430148981539653034495617007616 }, { target := 311, numerator := 184345529521314616982661758976 }, { target := 312, numerator := 2022680115581090936337538744320 }, { target := 313, numerator := 7430148981539653034495617007616 }, { target := 314, numerator := 158741983754465364623958736896 }, { target := 315, numerator := 179224820367944766510921154560 }, { target := 316, numerator := 184345529521314616982661758976 }, { target := 317, numerator := 179224820367944766510921154560 }, { target := 679, numerator := 16727653009745723229588160512 }, { target := 680, numerator := 18886059849712913323728568320 }, { target := 681, numerator := 16188051299753925706053058560 }, { target := 682, numerator := 213142675446760021796365271040 }, { target := 683, numerator := 18886059849712913323728568320 }, { target := 684, numerator := 16188051299753925706053058560 }, { target := 685, numerator := 18886059849712913323728568320 }, { target := 686, numerator := 18886059849712913323728568320 }, { target := 687, numerator := 782962081198098206649432932352 }, { target := 688, numerator := 19425661559704710847263670272 }, { target := 689, numerator := 213142675446760021796365271040 }, { target := 690, numerator := 782962081198098206649432932352 }, { target := 691, numerator := 16727653009745723229588160512 }, { target := 692, numerator := 18886059849712913323728568320 }, { target := 693, numerator := 19425661559704710847263670272 }, { target := 694, numerator := 18886059849712913323728568320 }]

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
    Slot24.Left18.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 16320498564797493858533376 }, { target := 258, numerator := 340690407540147684296884224 }, { target := 259, numerator := 17680540111863951680077824 }, { target := 260, numerator := 366531196934410382906228736 }, { target := 261, numerator := 548776764241315730993184768 }, { target := 262, numerator := 17000519338330722769305600 }, { target := 263, numerator := 548776764241315730993184768 }, { target := 264, numerator := 571897470541445513959440384 }, { target := 265, numerator := 340690407540147684296884224 }, { target := 266, numerator := 17000519338330722769305600 }, { target := 353, numerator := 12240373923598120393900032 }, { target := 354, numerator := 255517805655110763222663168 }, { target := 355, numerator := 13260405083897963760058368 }, { target := 356, numerator := 274898397700807787179671552 }, { target := 357, numerator := 411582573180986798244888576 }, { target := 358, numerator := 12750389503748042076979200 }, { target := 359, numerator := 411582573180986798244888576 }, { target := 360, numerator := 428923102906084135469580288 }, { target := 361, numerator := 255517805655110763222663168 }, { target := 362, numerator := 12750389503748042076979200 }, { target := 379, numerator := 12920394697131349304672256 }, { target := 380, numerator := 269713239302616916735033344 }, { target := 381, numerator := 13997094255225628413394944 }, { target := 382, numerator := 290170530906408219800764416 }, { target := 383, numerator := 434448271691041620369604608 }, { target := 384, numerator := 13458744476178488859033600 }, { target := 385, numerator := 434448271691041620369604608 }, { target := 386, numerator := 452752164178644365217890304 }, { target := 387, numerator := 269713239302616916735033344 }, { target := 388, numerator := 13458744476178488859033600 }, { target := 524, numerator := 16660508951564108313919488 }, { target := 525, numerator := 347788124363900761053069312 }, { target := 526, numerator := 18048884697527784006746112 }, { target := 527, numerator := 374167263537210599216775168 }, { target := 528, numerator := 560209613496343142055542784 }, { target := 529, numerator := 17354696824545946160332800 }, { target := 530, numerator := 560209613496343142055542784 }, { target := 531, numerator := 583812001177725628833595392 }, { target := 532, numerator := 347788124363900761053069312 }, { target := 533, numerator := 17354696824545946160332800 }, { target := 966, numerator := 141527497263939969808859136 }, { target := 967, numerator := 159789109814125772364840960 }, { target := 968, numerator := 136962094126393519169863680 }, { target := 969, numerator := 1803334239330848002403205120 }, { target := 970, numerator := 159789109814125772364840960 }, { target := 971, numerator := 136962094126393519169863680 }, { target := 972, numerator := 159789109814125772364840960 }, { target := 973, numerator := 159789109814125772364840960 }, { target := 974, numerator := 6624399952579899877182406656 }, { target := 975, numerator := 164354512951672223003836416 }, { target := 976, numerator := 1803334239330848002403205120 }, { target := 977, numerator := 6624399952579899877182406656 }, { target := 978, numerator := 141527497263939969808859136 }, { target := 979, numerator := 159789109814125772364840960 }, { target := 980, numerator := 164354512951672223003836416 }, { target := 981, numerator := 159789109814125772364840960 }]

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
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected,
    Slot25.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 620, numerator := 223046813718899082733289472 }, { target := 621, numerator := 4656102236382018352057417728 }, { target := 622, numerator := 241634048195474006294396928 }, { target := 623, numerator := 5009259691436941899718459392 }, { target := 624, numerator := 7499949111297981656906858496 }, { target := 625, numerator := 232340430957186544513843200 }, { target := 626, numerator := 7499949111297981656906858496 }, { target := 627, numerator := 7815932097399755357445685248 }, { target := 628, numerator := 4656102236382018352057417728 }, { target := 629, numerator := 232340430957186544513843200 }, { target := 646, numerator := 389991913621306780327870464 }, { target := 647, numerator := 8141081196844779039344295936 }, { target := 648, numerator := 422491239756415678688526336 }, { target := 649, numerator := 8758568393411848108196757504 }, { target := 650, numerator := 13113478095516440488524644352 }, { target := 651, numerator := 406241576688861229508198400 }, { target := 652, numerator := 13113478095516440488524644352 }, { target := 653, numerator := 13665966639813291760655794176 }, { target := 654, numerator := 8141081196844779039344295936 }, { target := 655, numerator := 406241576688861229508198400 }, { target := 695, numerator := 11900363536831505938513920 }, { target := 696, numerator := 248420088831357686466478080 }, { target := 697, numerator := 12892060498234131433390080 }, { target := 698, numerator := 267262331098007570869125120 }, { target := 699, numerator := 400149723925959387182530560 }, { target := 700, numerator := 12396212017532818685952000 }, { target := 701, numerator := 400149723925959387182530560 }, { target := 702, numerator := 417008572269804020595425280 }, { target := 703, numerator := 248420088831357686466478080 }, { target := 704, numerator := 12396212017532818685952000 }, { target := 721, numerator := 223046813718899082733289472 }, { target := 722, numerator := 4656102236382018352057417728 }, { target := 723, numerator := 241634048195474006294396928 }, { target := 724, numerator := 5009259691436941899718459392 }, { target := 725, numerator := 7499949111297981656906858496 }, { target := 726, numerator := 232340430957186544513843200 }, { target := 727, numerator := 7499949111297981656906858496 }, { target := 728, numerator := 7815932097399755357445685248 }, { target := 729, numerator := 4656102236382018352057417728 }, { target := 730, numerator := 232340430957186544513843200 }, { target := 735, numerator := 12580384310364734849286144 }, { target := 736, numerator := 262615522478863839978848256 }, { target := 737, numerator := 13628749669561796086726656 }, { target := 738, numerator := 282534464303608003490217984 }, { target := 739, numerator := 423015422436014209307246592 }, { target := 740, numerator := 13104566989963265468006400 }, { target := 741, numerator := 423015422436014209307246592 }, { target := 742, numerator := 440837633542364250343735296 }, { target := 743, numerator := 262615522478863839978848256 }, { target := 744, numerator := 13104566989963265468006400 }, { target := 836, numerator := 12920394697131349304672256 }, { target := 837, numerator := 269713239302616916735033344 }, { target := 838, numerator := 13997094255225628413394944 }, { target := 839, numerator := 290170530906408219800764416 }, { target := 840, numerator := 434448271691041620369604608 }, { target := 841, numerator := 13458744476178488859033600 }, { target := 842, numerator := 434448271691041620369604608 }, { target := 843, numerator := 452752164178644365217890304 }, { target := 844, numerator := 269713239302616916735033344 }, { target := 845, numerator := 13458744476178488859033600 }]

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
    Slot25.Left10.expected,
    Slot25.Left11.expected,
    Slot25.Left12.expected,
    Slot25.Left13.expected,
    Slot25.Left14.expected,
    Slot25.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 862, numerator := 12920394697131349304672256 }, { target := 863, numerator := 269713239302616916735033344 }, { target := 864, numerator := 13997094255225628413394944 }, { target := 865, numerator := 290170530906408219800764416 }, { target := 866, numerator := 434448271691041620369604608 }, { target := 867, numerator := 13458744476178488859033600 }, { target := 868, numerator := 434448271691041620369604608 }, { target := 869, numerator := 452752164178644365217890304 }, { target := 870, numerator := 269713239302616916735033344 }, { target := 871, numerator := 13458744476178488859033600 }, { target := 911, numerator := 12580384310364734849286144 }, { target := 912, numerator := 262615522478863839978848256 }, { target := 913, numerator := 13628749669561796086726656 }, { target := 914, numerator := 282534464303608003490217984 }, { target := 915, numerator := 423015422436014209307246592 }, { target := 916, numerator := 13104566989963265468006400 }, { target := 917, numerator := 423015422436014209307246592 }, { target := 918, numerator := 440837633542364250343735296 }, { target := 919, numerator := 262615522478863839978848256 }, { target := 920, numerator := 13104566989963265468006400 }, { target := 937, numerator := 389991913621306780327870464 }, { target := 938, numerator := 8141081196844779039344295936 }, { target := 939, numerator := 422491239756415678688526336 }, { target := 940, numerator := 8758568393411848108196757504 }, { target := 941, numerator := 13113478095516440488524644352 }, { target := 942, numerator := 406241576688861229508198400 }, { target := 943, numerator := 13113478095516440488524644352 }, { target := 944, numerator := 13665966639813291760655794176 }, { target := 945, numerator := 8141081196844779039344295936 }, { target := 946, numerator := 406241576688861229508198400 }, { target := 951, numerator := 12580384310364734849286144 }, { target := 952, numerator := 262615522478863839978848256 }, { target := 953, numerator := 13628749669561796086726656 }, { target := 954, numerator := 282534464303608003490217984 }, { target := 955, numerator := 423015422436014209307246592 }, { target := 956, numerator := 13104566989963265468006400 }, { target := 957, numerator := 423015422436014209307246592 }, { target := 958, numerator := 440837633542364250343735296 }, { target := 959, numerator := 262615522478863839978848256 }, { target := 960, numerator := 13104566989963265468006400 }, { target := 982, numerator := 16320498564797493858533376 }, { target := 983, numerator := 340690407540147684296884224 }, { target := 984, numerator := 17680540111863951680077824 }, { target := 985, numerator := 366531196934410382906228736 }, { target := 986, numerator := 548776764241315730993184768 }, { target := 987, numerator := 17000519338330722769305600 }, { target := 988, numerator := 548776764241315730993184768 }, { target := 989, numerator := 571897470541445513959440384 }, { target := 990, numerator := 340690407540147684296884224 }, { target := 991, numerator := 17000519338330722769305600 }, { target := 996, numerator := 16660508951564108313919488 }, { target := 997, numerator := 347788124363900761053069312 }, { target := 998, numerator := 18048884697527784006746112 }, { target := 999, numerator := 374167263537210599216775168 }, { target := 1000, numerator := 560209613496343142055542784 }, { target := 1001, numerator := 17354696824545946160332800 }, { target := 1002, numerator := 560209613496343142055542784 }, { target := 1003, numerator := 583812001177725628833595392 }, { target := 1004, numerator := 347788124363900761053069312 }, { target := 1005, numerator := 17354696824545946160332800 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3
