import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3

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
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 84985706391611123538329600 }, { target := 30, numerator := 14905694456829790642818252800 }, { target := 35, numerator := 14905696243858122783431065600 }, { target := 43, numerator := 84983919363278982925516800 }, { target := 55, numerator := 95951603990528687865856000 }, { target := 56, numerator := 16829009870614279758020608000 }, { target := 61, numerator := 16829011888226912820002816000 }, { target := 69, numerator := 95949586377895625883648000 }, { target := 104, numerator := 82244231991881732456448000 }, { target := 105, numerator := 14424865603383668364017664000 }, { target := 110, numerator := 14424867332765925274288128000 }, { target := 118, numerator := 82242502609624822185984000 }, { target := 130, numerator := 1082882387893109477343232000 }, { target := 131, numerator := 189927397111218300126232576000 }, { target := 136, numerator := 189927419881418016111460352000 }, { target := 144, numerator := 1082859617693393492115456000 }, { target := 165, numerator := 95951603990528687865856000 }, { target := 166, numerator := 16829009870614279758020608000 }, { target := 171, numerator := 16829011888226912820002816000 }, { target := 179, numerator := 95949586377895625883648000 }, { target := 226, numerator := 82244231991881732456448000 }, { target := 227, numerator := 14424865603383668364017664000 }, { target := 232, numerator := 14424867332765925274288128000 }, { target := 240, numerator := 82242502609624822185984000 }, { target := 261, numerator := 95951603990528687865856000 }, { target := 262, numerator := 16829009870614279758020608000 }, { target := 267, numerator := 16829011888226912820002816000 }, { target := 275, numerator := 95949586377895625883648000 }, { target := 371, numerator := 95951603990528687865856000 }, { target := 372, numerator := 16829009870614279758020608000 }, { target := 377, numerator := 16829011888226912820002816000 }, { target := 385, numerator := 95949586377895625883648000 }, { target := 397, numerator := 3977879354007346459810201600 }, { target := 398, numerator := 697682666350323426539654348800 }, { target := 403, numerator := 697682749994778585766402457600 }, { target := 411, numerator := 3977795709552187233062092800 }, { target := 432, numerator := 98693078390258078947737600 }, { target := 433, numerator := 17309838724060402036821196800 }, { target := 438, numerator := 17309840799319110329145753600 }, { target := 446, numerator := 98691003131549786623180800 }, { target := 493, numerator := 1082882387893109477343232000 }, { target := 494, numerator := 189927397111218300126232576000 }, { target := 499, numerator := 189927419881418016111460352000 }, { target := 507, numerator := 1082859617693393492115456000 }, { target := 528, numerator := 3977879354007346459810201600 }, { target := 529, numerator := 697682666350323426539654348800 }, { target := 534, numerator := 697682749994778585766402457600 }, { target := 542, numerator := 3977795709552187233062092800 }, { target := 624, numerator := 84985706391611123538329600 }, { target := 625, numerator := 14905694456829790642818252800 }, { target := 630, numerator := 14905696243858122783431065600 }, { target := 638, numerator := 84983919363278982925516800 }, { target := 760, numerator := 95951603990528687865856000 }, { target := 761, numerator := 16829009870614279758020608000 }, { target := 766, numerator := 16829011888226912820002816000 }, { target := 774, numerator := 95949586377895625883648000 }, { target := 795, numerator := 98693078390258078947737600 }, { target := 796, numerator := 17309838724060402036821196800 }, { target := 801, numerator := 17309840799319110329145753600 }, { target := 809, numerator := 98691003131549786623180800 }, { target := 891, numerator := 95951603990528687865856000 }, { target := 892, numerator := 16829009870614279758020608000 }, { target := 897, numerator := 16829011888226912820002816000 }, { target := 905, numerator := 95949586377895625883648000 }]

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
    Slot2.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 30409734306671301482250240 }, { target := 72, numerator := 9795624948484405594454753280 }, { target := 74, numerator := 104180590665169651859491651584 }, { target := 82, numerator := 9795654472498295566592114688 }, { target := 89, numerator := 30409734306671301482250240 }, { target := 146, numerator := 440941147446733871492628480 }, { target := 147, numerator := 142036561753023881119593922560 }, { target := 149, numerator := 1510618564644959951962628947968 }, { target := 157, numerator := 142036989851225285715585662976 }, { target := 164, numerator := 440941147446733871492628480 }, { target := 181, numerator := 780516513871230071377756160 }, { target := 182, numerator := 251421040344433076924338667520 }, { target := 184, numerator := 2673968493739354397726952390656 }, { target := 192, numerator := 251421798127456252875864276992 }, { target := 199, numerator := 780516513871230071377756160 }, { target := 242, numerator := 25341445255559417901875200 }, { target := 243, numerator := 8163020790403671328712294400 }, { target := 245, numerator := 86817158887641376549576376320 }, { target := 253, numerator := 8163045393748579638826762240 }, { target := 260, numerator := 25341445255559417901875200 }, { target := 277, numerator := 486555748906740823716003840 }, { target := 278, numerator := 156729999175750489511276052480 }, { target := 280, numerator := 1666889450642714429751866425344 }, { target := 288, numerator := 156730471559972729065473835008 }, { target := 295, numerator := 486555748906740823716003840 }, { target := 312, numerator := 25341445255559417901875200 }, { target := 313, numerator := 8163020790403671328712294400 }, { target := 315, numerator := 86817158887641376549576376320 }, { target := 323, numerator := 8163045393748579638826762240 }, { target := 330, numerator := 25341445255559417901875200 }, { target := 413, numerator := 775448224820118187797381120 }, { target := 414, numerator := 249788436186352342658596208640 }, { target := 416, numerator := 2656605061961826122417037115392 }, { target := 424, numerator := 249789189048706536948098924544 }, { target := 431, numerator := 775448224820118187797381120 }, { target := 448, numerator := 810926248177901372860006400 }, { target := 449, numerator := 261216665292917482518793420800 }, { target := 451, numerator := 2778149084404524049586444042240 }, { target := 459, numerator := 261217452599954548442456391680 }, { target := 466, numerator := 810926248177901372860006400 }, { target := 509, numerator := 486555748906740823716003840 }, { target := 510, numerator := 156729999175750489511276052480 }, { target := 512, numerator := 1666889450642714429751866425344 }, { target := 520, numerator := 156730471559972729065473835008 }, { target := 527, numerator := 486555748906740823716003840 }, { target := 544, numerator := 12422376464275226655499223040 }, { target := 545, numerator := 4001512791455879685334766714880 }, { target := 547, numerator := 42557771286721802784602339672064 }, { target := 555, numerator := 4001524852015553738952878850048 }, { target := 562, numerator := 12422376464275226655499223040 }, { target := 579, numerator := 795721381024565722118881280 }, { target := 580, numerator := 256318852818675279721566044160 }, { target := 582, numerator := 2726058789071939223656698216448 }, { target := 590, numerator := 256319625363705400659160334336 }, { target := 597, numerator := 795721381024565722118881280 }, { target := 640, numerator := 440941147446733871492628480 }, { target := 641, numerator := 142036561753023881119593922560 }, { target := 643, numerator := 1510618564644959951962628947968 }, { target := 651, numerator := 142036989851225285715585662976 }, { target := 658, numerator := 440941147446733871492628480 }]

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
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 6897147095598517674880008192 }, { target := 202, numerator := 269927423782821050180696014848 }, { target := 205, numerator := 269927522783037729266038996992 }, { target := 212, numerator := 6897246095815196760222990336 }, { target := 296, numerator := 5136173369062725928102133760 }, { target := 298, numerator := 201009783668058228857965117440 }, { target := 301, numerator := 201009857391623840942794997760 }, { target := 308, numerator := 5136247092628338012932014080 }, { target := 331, numerator := 5429668990152024552565112832 }, { target := 333, numerator := 212496057020518699078420267008 }, { target := 336, numerator := 212496134956859488996668997632 }, { target := 343, numerator := 5429746926492814470813843456 }, { target := 467, numerator := 7043894906143166987111497728 }, { target := 469, numerator := 275670560459051285290923589632 }, { target := 472, numerator := 275670661565655553292975996928 }, { target := 479, numerator := 7043996012747434989163905024 }, { target := 563, numerator := 94358842180209507764847771648 }, { target := 565, numerator := 3692836882816041175876330586112 }, { target := 568, numerator := 3692838237223260849320490958848 }, { target := 575, numerator := 94360196587429181209008144384 }, { target := 598, numerator := 170667703663427150125222330368 }, { target := 600, numerator := 6679267954455763433194669473792 }, { target := 603, numerator := 6679270404184529343327730925568 }, { target := 610, numerator := 170670153392193060258283782144 }, { target := 659, numerator := 5136173369062725928102133760 }, { target := 661, numerator := 201009783668058228857965117440 }, { target := 664, numerator := 201009857391623840942794997760 }, { target := 671, numerator := 5136247092628338012932014080 }, { target := 675, numerator := 775448224820118187797381120 }, { target := 676, numerator := 249788436186352342658596208640 }, { target := 678, numerator := 2656605061961826122417037115392 }, { target := 686, numerator := 249789189048706536948098924544 }, { target := 693, numerator := 775448224820118187797381120 }, { target := 776, numerator := 25341445255559417901875200 }, { target := 777, numerator := 8163020790403671328712294400 }, { target := 779, numerator := 86817158887641376549576376320 }, { target := 787, numerator := 8163045393748579638826762240 }, { target := 794, numerator := 25341445255559417901875200 }, { target := 811, numerator := 795721381024565722118881280 }, { target := 812, numerator := 256318852818675279721566044160 }, { target := 814, numerator := 2726058789071939223656698216448 }, { target := 822, numerator := 256319625363705400659160334336 }, { target := 829, numerator := 795721381024565722118881280 }, { target := 846, numerator := 25341445255559417901875200 }, { target := 847, numerator := 8163020790403671328712294400 }, { target := 849, numerator := 86817158887641376549576376320 }, { target := 857, numerator := 8163045393748579638826762240 }, { target := 864, numerator := 25341445255559417901875200 }, { target := 907, numerator := 775448224820118187797381120 }, { target := 908, numerator := 249788436186352342658596208640 }, { target := 910, numerator := 2656605061961826122417037115392 }, { target := 918, numerator := 249789189048706536948098924544 }, { target := 925, numerator := 775448224820118187797381120 }, { target := 942, numerator := 810926248177901372860006400 }, { target := 943, numerator := 261216665292917482518793420800 }, { target := 945, numerator := 2778149084404524049586444042240 }, { target := 953, numerator := 261217452599954548442456391680 }, { target := 960, numerator := 810926248177901372860006400 }, { target := 1017, numerator := 30409734306671301482250240 }, { target := 1018, numerator := 9795624948484405594454753280 }, { target := 1020, numerator := 104180590665169651859491651584 }, { target := 1028, numerator := 9795654472498295566592114688 }, { target := 1035, numerator := 30409734306671301482250240 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 4402166558390484958982438912 }, { target := 350, numerator := 15779103088800282799771746304 }, { target := 352, numerator := 4403445820492331138070609920 }, { target := 614, numerator := 107924083366992534478279147520 }, { target := 617, numerator := 386842527338329513800855715840 }, { target := 619, numerator := 107955445921747473062376243200 }, { target := 694, numerator := 94358842180209507764847771648 }, { target := 696, numerator := 3692836882816041175876330586112 }, { target := 699, numerator := 3692838237223260849320490958848 }, { target := 706, numerator := 94360196587429181209008144384 }, { target := 710, numerator := 79807019542433953127359053824 }, { target := 713, numerator := 286059868900185772047474884608 }, { target := 715, numerator := 79830211326344841922441379840 }, { target := 720, numerator := 5576416800696673864796602368 }, { target := 722, numerator := 218239193696748934188647841792 }, { target := 725, numerator := 218239273739477313023605997568 }, { target := 732, numerator := 5576496843425052699754758144 }, { target := 736, numerator := 89037368777768840944580296704 }, { target := 739, numerator := 319145085054121848885705965568 }, { target := 741, numerator := 89063242885441665276460400640 }, { target := 830, numerator := 5576416800696673864796602368 }, { target := 832, numerator := 218239193696748934188647841792 }, { target := 835, numerator := 218239273739477313023605997568 }, { target := 842, numerator := 5576496843425052699754758144 }, { target := 865, numerator := 5429668990152024552565112832 }, { target := 867, numerator := 212496057020518699078420267008 }, { target := 870, numerator := 212496134956859488996668997632 }, { target := 877, numerator := 5429746926492814470813843456 }, { target := 881, numerator := 4402166558390484958982438912 }, { target := 884, numerator := 15779103088800282799771746304 }, { target := 886, numerator := 4403445820492331138070609920 }, { target := 926, numerator := 5429668990152024552565112832 }, { target := 928, numerator := 212496057020518699078420267008 }, { target := 931, numerator := 212496134956859488996668997632 }, { target := 938, numerator := 5429746926492814470813843456 }, { target := 961, numerator := 170667703663427150125222330368 }, { target := 963, numerator := 6679267954455763433194669473792 }, { target := 966, numerator := 6679270404184529343327730925568 }, { target := 973, numerator := 170670153392193060258283782144 }, { target := 977, numerator := 88895363404917534978161508352 }, { target := 980, numerator := 318636081728676678472810102784 }, { target := 982, numerator := 88921196246070944917167800320 }, { target := 987, numerator := 5429668990152024552565112832 }, { target := 989, numerator := 212496057020518699078420267008 }, { target := 992, numerator := 212496134956859488996668997632 }, { target := 999, numerator := 5429746926492814470813843456 }, { target := 1003, numerator := 90457422506281900608768180224 }, { target := 1006, numerator := 324235118308573553014664593408 }, { target := 1008, numerator := 90483709279148868869386403840 }, { target := 1036, numerator := 6897147095598517674880008192 }, { target := 1038, numerator := 269927423782821050180696014848 }, { target := 1041, numerator := 269927522783037729266038996992 }, { target := 1048, numerator := 6897246095815196760222990336 }, { target := 1052, numerator := 4402166558390484958982438912 }, { target := 1055, numerator := 15779103088800282799771746304 }, { target := 1057, numerator := 4403445820492331138070609920 }, { target := 1062, numerator := 7043894906143166987111497728 }, { target := 1064, numerator := 275670560459051285290923589632 }, { target := 1067, numerator := 275670661565655553292975996928 }, { target := 1074, numerator := 7043996012747434989163905024 }, { target := 1078, numerator := 107924083366992534478279147520 }, { target := 1081, numerator := 386842527338329513800855715840 }, { target := 1083, numerator := 107955445921747473062376243200 }]

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
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 2379597594368011413447770112 }, { target := 7, numerator := 107553482204555899350980493312 }, { target := 12, numerator := 2392298226112485230987182080 }, { target := 29, numerator := 1166303354179101702737625088 }, { target := 30, numerator := 231318587154901666693015142400 }, { target := 35, numerator := 231318587154901666693015142400 }, { target := 43, numerator := 1166303354179101702737625088 }, { target := 71, numerator := 45649416563947937606926336 }, { target := 72, numerator := 7481060192752016185171640320 }, { target := 74, numerator := 77020411265538829386797547520 }, { target := 82, numerator := 7481060192752016185171640320 }, { target := 89, numerator := 45649416563947937606926336 }, { target := 94, numerator := 8668304510108910100500447232 }, { target := 96, numerator := 391791594124248609034634002432 }, { target := 101, numerator := 8714569871820663708062842880 }, { target := 104, numerator := 46628591705429792027630895104 }, { target := 105, numerator := 9248074195854915165349950259200 }, { target := 110, numerator := 9248074195854915165349950259200 }, { target := 118, numerator := 46628591705429792027630895104 }, { target := 146, numerator := 7481060192752016185171640320 }, { target := 147, numerator := 1226001684581851212187854438400 }, { target := 149, numerator := 12622162036635238118166259302400 }, { target := 157, numerator := 1226001684581851212187854438400 }, { target := 164, numerator := 7481060192752016185171640320 }, { target := 216, numerator := 2379599195050901772351569920 }, { target := 218, numerator := 107553554552510516054374481920 }, { target := 223, numerator := 2392299835338704083012812800 }, { target := 226, numerator := 46628580310240182019846832128 }, { target := 227, numerator := 9248071935791826515058386534400 }, { target := 232, numerator := 9248071935791826515058386534400 }, { target := 240, numerator := 46628580310240182019846832128 }, { target := 242, numerator := 77020411265538829386797547520 }, { target := 243, numerator := 12622162036635238118166259302400 }, { target := 245, numerator := 129950045324296822759071573606400 }, { target := 253, numerator := 12622162036635238118166259302400 }, { target := 260, numerator := 77020411265538829386797547520 }, { target := 624, numerator := 1166303354179101702737625088 }, { target := 625, numerator := 231318587154901666693015142400 }, { target := 630, numerator := 231318587154901666693015142400 }, { target := 638, numerator := 1166303354179101702737625088 }, { target := 640, numerator := 7481060192752016185171640320 }, { target := 641, numerator := 1226001684581851212187854438400 }, { target := 643, numerator := 12622162036635238118166259302400 }, { target := 651, numerator := 1226001684581851212187854438400 }, { target := 658, numerator := 7481060192752016185171640320 }, { target := 746, numerator := 9942202384900790125267517440 }, { target := 748, numerator := 9942209496120630540299665408 }, { target := 1013, numerator := 9913188175606332566536192000 }, { target := 1015, numerator := 9913195266073585898645094400 }, { target := 1017, numerator := 45649416563947937606926336 }, { target := 1018, numerator := 7481060192752016185171640320 }, { target := 1020, numerator := 77020411265538829386797547520 }, { target := 1028, numerator := 7481060192752016185171640320 }, { target := 1035, numerator := 45649416563947937606926336 }, { target := 1088, numerator := 9845488353919264929496432640 }, { target := 1090, numerator := 9845495395963815068117762048 }, { target := 1092, numerator := 4402166558390484958982438912 }, { target := 1095, numerator := 15779103088800282799771746304 }, { target := 1097, numerator := 4403445820492331138070609920 }, { target := 1102, numerator := 9913188175606332566536192000 }, { target := 1104, numerator := 9913195266073585898645094400 }]

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
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left7.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 9942202384900790125267517440 }, { target := 2, numerator := 9913188175606332566536192000 }, { target := 3, numerator := 9845488353919264929496432640 }, { target := 4, numerator := 9913188175606332566536192000 }, { target := 5, numerator := 4402166558390484958982438912 }, { target := 6, numerator := 107924083366992534478279147520 }, { target := 7, numerator := 79807019542433953127359053824 }, { target := 8, numerator := 89037368777768840944580296704 }, { target := 9, numerator := 4402166558390484958982438912 }, { target := 10, numerator := 88895363404917534978161508352 }, { target := 11, numerator := 90457422506281900608768180224 }, { target := 12, numerator := 4402166558390484958982438912 }, { target := 13, numerator := 107924083366992534478279147520 }, { target := 14, numerator := 4402166558390484958982438912 }, { target := 90, numerator := 9942209496120630540299665408 }, { target := 91, numerator := 9913195266073585898645094400 }, { target := 92, numerator := 9845495395963815068117762048 }, { target := 93, numerator := 9913195266073585898645094400 }, { target := 94, numerator := 15779103088800282799771746304 }, { target := 95, numerator := 386842527338329513800855715840 }, { target := 96, numerator := 286059868900185772047474884608 }, { target := 97, numerator := 319145085054121848885705965568 }, { target := 98, numerator := 15779103088800282799771746304 }, { target := 99, numerator := 318636081728676678472810102784 }, { target := 100, numerator := 324235118308573553014664593408 }, { target := 101, numerator := 15779103088800282799771746304 }, { target := 102, numerator := 386842527338329513800855715840 }, { target := 103, numerator := 15779103088800282799771746304 }, { target := 200, numerator := 1168728101277187153263067136 }, { target := 202, numerator := 46725532644526319661783973888 }, { target := 205, numerator := 46725521225646086764170838016 }, { target := 212, numerator := 1168728101277187153263067136 }, { target := 216, numerator := 4403445820492331138070609920 }, { target := 217, numerator := 107955445921747473062376243200 }, { target := 218, numerator := 79830211326344841922441379840 }, { target := 219, numerator := 89063242885441665276460400640 }, { target := 220, numerator := 4403445820492331138070609920 }, { target := 221, numerator := 88921196246070944917167800320 }, { target := 222, numerator := 90483709279148868869386403840 }, { target := 223, numerator := 4403445820492331138070609920 }, { target := 224, numerator := 107955445921747473062376243200 }, { target := 225, numerator := 4403445820492331138070609920 }, { target := 296, numerator := 231799498978508530864934092800 }, { target := 298, numerator := 9267300961334863013926561382400 }, { target := 301, numerator := 9267298696573098503655181516800 }, { target := 308, numerator := 231799498978508530864934092800 }, { target := 347, numerator := 2379597594368011413447770112 }, { target := 350, numerator := 8668304510108910100500447232 }, { target := 352, numerator := 2379599195050901772351569920 }, { target := 659, numerator := 231799498978508530864934092800 }, { target := 661, numerator := 9267300961334863013926561382400 }, { target := 664, numerator := 9267298696573098503655181516800 }, { target := 671, numerator := 231799498978508530864934092800 }, { target := 710, numerator := 107553482204555899350980493312 }, { target := 713, numerator := 391791594124248609034634002432 }, { target := 715, numerator := 107553554552510516054374481920 }, { target := 1036, numerator := 1168728101277187153263067136 }, { target := 1038, numerator := 46725532644526319661783973888 }, { target := 1041, numerator := 46725521225646086764170838016 }, { target := 1048, numerator := 1168728101277187153263067136 }, { target := 1052, numerator := 2392298226112485230987182080 }, { target := 1055, numerator := 8714569871820663708062842880 }, { target := 1057, numerator := 2392299835338704083012812800 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 6817869542775546207352651776 }, { target := 30, numerator := 5077136893556257813986017280 }, { target := 31, numerator := 5367259001759472546213789696 }, { target := 32, numerator := 6962930596877153573466537984 }, { target := 33, numerator := 93274257787333536411228831744 }, { target := 34, numerator := 168706005920169366790449659904 }, { target := 35, numerator := 5077136893556257813986017280 }, { target := 36, numerator := 93274257787333536411228831744 }, { target := 37, numerator := 5512320055861079912327675904 }, { target := 38, numerator := 5512320055861079912327675904 }, { target := 39, numerator := 5367259001759472546213789696 }, { target := 40, numerator := 5367259001759472546213789696 }, { target := 41, numerator := 168706005920169366790449659904 }, { target := 42, numerator := 5367259001759472546213789696 }, { target := 43, numerator := 6817869542775546207352651776 }, { target := 44, numerator := 6962930596877153573466537984 }, { target := 104, numerator := 266824809716351842707354681344 }, { target := 105, numerator := 198699326384517329675689656320 }, { target := 106, numerator := 210053573606489748514300493824 }, { target := 107, numerator := 272501933327338052126660100096 }, { target := 108, numerator := 3650390481864132656613384257536 }, { target := 109, numerator := 6602494759576961554652202008576 }, { target := 110, numerator := 198699326384517329675689656320 }, { target := 111, numerator := 3650390481864132656613384257536 }, { target := 112, numerator := 215730697217475957933605912576 }, { target := 113, numerator := 215730697217475957933605912576 }, { target := 114, numerator := 210053573606489748514300493824 }, { target := 115, numerator := 210053573606489748514300493824 }, { target := 116, numerator := 6602494759576961554652202008576 }, { target := 117, numerator := 210053573606489748514300493824 }, { target := 118, numerator := 266824809716351842707354681344 }, { target := 119, numerator := 272501933327338052126660100096 }, { target := 226, numerator := 266824907578634996745739698176 }, { target := 227, numerator := 198699399260685635874487009280 }, { target := 228, numerator := 210053650647010529353029124096 }, { target := 229, numerator := 272502033271797443485010755584 }, { target := 230, numerator := 3650391820703453253351289913344 }, { target := 231, numerator := 6602497181147925557772239765504 }, { target := 232, numerator := 198699399260685635874487009280 }, { target := 233, numerator := 3650391820703453253351289913344 }, { target := 234, numerator := 215730776340172976092300181504 }, { target := 235, numerator := 215730776340172976092300181504 }, { target := 236, numerator := 210053650647010529353029124096 }, { target := 237, numerator := 210053650647010529353029124096 }, { target := 238, numerator := 6602497181147925557772239765504 }, { target := 239, numerator := 210053650647010529353029124096 }, { target := 240, numerator := 266824907578634996745739698176 }, { target := 241, numerator := 272502033271797443485010755584 }, { target := 624, numerator := 6817967405058700245737668608 }, { target := 625, numerator := 5077209769724564012783370240 }, { target := 626, numerator := 5367336042280253384942419968 }, { target := 627, numerator := 6963030541336544931817193472 }, { target := 628, numerator := 93275596626654133149134487552 }, { target := 629, numerator := 168708427491133369910487416832 }, { target := 630, numerator := 5077209769724564012783370240 }, { target := 631, numerator := 93275596626654133149134487552 }, { target := 632, numerator := 5512399178558098071021944832 }, { target := 633, numerator := 5512399178558098071021944832 }, { target := 634, numerator := 5367336042280253384942419968 }, { target := 635, numerator := 5367336042280253384942419968 }, { target := 636, numerator := 168708427491133369910487416832 }, { target := 637, numerator := 5367336042280253384942419968 }, { target := 638, numerator := 6817967405058700245737668608 }, { target := 639, numerator := 6963030541336544931817193472 }]

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
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 30324233647889657710510080 }, { target := 72, numerator := 439701387894400036802396160 }, { target := 73, numerator := 778321996962501214569758720 }, { target := 74, numerator := 25270194706574714758758400 }, { target := 75, numerator := 485187738366234523368161280 }, { target := 76, numerator := 25270194706574714758758400 }, { target := 77, numerator := 773267958021186271618007040 }, { target := 78, numerator := 808646230610390872280268800 }, { target := 79, numerator := 485187738366234523368161280 }, { target := 80, numerator := 12387449445162925174743367680 }, { target := 81, numerator := 793484113786446043425013760 }, { target := 82, numerator := 439701387894400036802396160 }, { target := 83, numerator := 773267958021186271618007040 }, { target := 84, numerator := 25270194706574714758758400 }, { target := 85, numerator := 793484113786446043425013760 }, { target := 86, numerator := 25270194706574714758758400 }, { target := 87, numerator := 773267958021186271618007040 }, { target := 88, numerator := 808646230610390872280268800 }, { target := 89, numerator := 30324233647889657710510080 }, { target := 146, numerator := 9768083360063174838331637760 }, { target := 147, numerator := 141637208720916035155808747520 }, { target := 148, numerator := 250714139574954820850512035840 }, { target := 149, numerator := 8140069466719312365276364800 }, { target := 150, numerator := 156289333761010797413306204160 }, { target := 151, numerator := 8140069466719312365276364800 }, { target := 152, numerator := 249086125681610958377456762880 }, { target := 153, numerator := 260482222935017995688843673600 }, { target := 154, numerator := 156289333761010797413306204160 }, { target := 155, numerator := 3990262052585806921458474024960 }, { target := 156, numerator := 255598181254986408269677854720 }, { target := 157, numerator := 141637208720916035155808747520 }, { target := 158, numerator := 249086125681610958377456762880 }, { target := 159, numerator := 8140069466719312365276364800 }, { target := 160, numerator := 255598181254986408269677854720 }, { target := 161, numerator := 8140069466719312365276364800 }, { target := 162, numerator := 249086125681610958377456762880 }, { target := 163, numerator := 260482222935017995688843673600 }, { target := 164, numerator := 9768083360063174838331637760 }, { target := 242, numerator := 103887674290291011788658966528 }, { target := 243, numerator := 1506371277209219670935555014656 }, { target := 244, numerator := 2666450306784135969242246807552 }, { target := 245, numerator := 86573061908575843157215805440 }, { target := 246, numerator := 1662202788644656188618543464448 }, { target := 247, numerator := 86573061908575843157215805440 }, { target := 248, numerator := 2649135694402420800610803646464 }, { target := 249, numerator := 2770337981074426981030905774080 }, { target := 250, numerator := 1662202788644656188618543464448 }, { target := 251, numerator := 42438114947583878315667187826688 }, { target := 252, numerator := 2718394143929281475136576290816 }, { target := 253, numerator := 1506371277209219670935555014656 }, { target := 254, numerator := 2649135694402420800610803646464 }, { target := 255, numerator := 86573061908575843157215805440 }, { target := 256, numerator := 2718394143929281475136576290816 }, { target := 257, numerator := 86573061908575843157215805440 }, { target := 258, numerator := 2649135694402420800610803646464 }, { target := 259, numerator := 2770337981074426981030905774080 }, { target := 260, numerator := 103887674290291011788658966528 }]

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
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 88385134647275568479862784 }, { target := 201, numerator := 99789668150149835380490240 }, { target := 202, numerator := 85534001271557001754705920 }, { target := 203, numerator := 1126197683408833856436961280 }, { target := 204, numerator := 99789668150149835380490240 }, { target := 205, numerator := 85534001271557001754705920 }, { target := 206, numerator := 99789668150149835380490240 }, { target := 207, numerator := 99789668150149835380490240 }, { target := 208, numerator := 4136994528167640318202609664 }, { target := 209, numerator := 102640801525868402105647104 }, { target := 210, numerator := 1126197683408833856436961280 }, { target := 211, numerator := 4136994528167640318202609664 }, { target := 212, numerator := 88385134647275568479862784 }, { target := 213, numerator := 99789668150149835380490240 }, { target := 214, numerator := 102640801525868402105647104 }, { target := 215, numerator := 99789668150149835380490240 }, { target := 640, numerator := 9768112801066716478776016896 }, { target := 641, numerator := 141637635615467388942252244992 }, { target := 642, numerator := 250714895227379056288584433664 }, { target := 643, numerator := 8140094000888930398980014080 }, { target := 644, numerator := 156289804817067463660416270336 }, { target := 645, numerator := 8140094000888930398980014080 }, { target := 646, numerator := 249086876427201270208788430848 }, { target := 647, numerator := 260483008028445772767360450560 }, { target := 648, numerator := 156289804817067463660416270336 }, { target := 649, numerator := 3990274079235753681580002902016 }, { target := 650, numerator := 255598951627912414527972442112 }, { target := 651, numerator := 141637635615467388942252244992 }, { target := 652, numerator := 249086876427201270208788430848 }, { target := 653, numerator := 8140094000888930398980014080 }, { target := 654, numerator := 255598951627912414527972442112 }, { target := 655, numerator := 8140094000888930398980014080 }, { target := 656, numerator := 249086876427201270208788430848 }, { target := 657, numerator := 260483008028445772767360450560 }, { target := 658, numerator := 9768112801066716478776016896 }, { target := 1017, numerator := 30324233647889657710510080 }, { target := 1018, numerator := 439701387894400036802396160 }, { target := 1019, numerator := 778321996962501214569758720 }, { target := 1020, numerator := 25270194706574714758758400 }, { target := 1021, numerator := 485187738366234523368161280 }, { target := 1022, numerator := 25270194706574714758758400 }, { target := 1023, numerator := 773267958021186271618007040 }, { target := 1024, numerator := 808646230610390872280268800 }, { target := 1025, numerator := 485187738366234523368161280 }, { target := 1026, numerator := 12387449445162925174743367680 }, { target := 1027, numerator := 793484113786446043425013760 }, { target := 1028, numerator := 439701387894400036802396160 }, { target := 1029, numerator := 773267958021186271618007040 }, { target := 1030, numerator := 25270194706574714758758400 }, { target := 1031, numerator := 793484113786446043425013760 }, { target := 1032, numerator := 25270194706574714758758400 }, { target := 1033, numerator := 773267958021186271618007040 }, { target := 1034, numerator := 808646230610390872280268800 }, { target := 1035, numerator := 30324233647889657710510080 }]

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
    Slot19.Left1.expected,
    Slot19.Left6.expected,
    Slot19.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 296, numerator := 15501922235102982268530982912 }, { target := 297, numerator := 17502170265438850948341432320 }, { target := 298, numerator := 15001860227519015098578370560 }, { target := 299, numerator := 197524492995667032131281879040 }, { target := 300, numerator := 17502170265438850948341432320 }, { target := 301, numerator := 15001860227519015098578370560 }, { target := 302, numerator := 17502170265438850948341432320 }, { target := 303, numerator := 17502170265438850948341432320 }, { target := 304, numerator := 725589973004336363601240522752 }, { target := 305, numerator := 18002232273022818118294044672 }, { target := 306, numerator := 197524492995667032131281879040 }, { target := 307, numerator := 725589973004336363601240522752 }, { target := 308, numerator := 15501922235102982268530982912 }, { target := 309, numerator := 17502170265438850948341432320 }, { target := 310, numerator := 18002232273022818118294044672 }, { target := 311, numerator := 17502170265438850948341432320 }, { target := 659, numerator := 15501924093612447694768308224 }, { target := 660, numerator := 17502172363755989332802928640 }, { target := 661, numerator := 15001862026076562285259653120 }, { target := 662, numerator := 197524516676674736755918766080 }, { target := 663, numerator := 17502172363755989332802928640 }, { target := 664, numerator := 15001862026076562285259653120 }, { target := 665, numerator := 17502172363755989332802928640 }, { target := 666, numerator := 17502172363755989332802928640 }, { target := 667, numerator := 725590059994569729197058555904 }, { target := 668, numerator := 18002234431291874742311583744 }, { target := 669, numerator := 197524516676674736755918766080 }, { target := 670, numerator := 725590059994569729197058555904 }, { target := 671, numerator := 15501924093612447694768308224 }, { target := 672, numerator := 17502172363755989332802928640 }, { target := 673, numerator := 18002234431291874742311583744 }, { target := 674, numerator := 17502172363755989332802928640 }, { target := 1036, numerator := 88383276137810142242537472 }, { target := 1037, numerator := 99787569833011450918993920 }, { target := 1038, numerator := 85532202714009815073423360 }, { target := 1039, numerator := 1126174002401129231800074240 }, { target := 1040, numerator := 99787569833011450918993920 }, { target := 1041, numerator := 85532202714009815073423360 }, { target := 1042, numerator := 99787569833011450918993920 }, { target := 1043, numerator := 99787569833011450918993920 }, { target := 1044, numerator := 4136907537934274722384576512 }, { target := 1045, numerator := 102638643256811778088108032 }, { target := 1046, numerator := 1126174002401129231800074240 }, { target := 1047, numerator := 4136907537934274722384576512 }, { target := 1048, numerator := 88383276137810142242537472 }, { target := 1049, numerator := 99787569833011450918993920 }, { target := 1050, numerator := 102638643256811778088108032 }, { target := 1051, numerator := 99787569833011450918993920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3
