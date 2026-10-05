import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2

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
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 142804362441978071262167040 }, { target := 201, numerator := 169580180399848959623823360 }, { target := 202, numerator := 129416453463042627081338880 }, { target := 203, numerator := 1334328261567232603355873280 }, { target := 204, numerator := 160654907747225330169937920 }, { target := 205, numerator := 129416453463042627081338880 }, { target := 206, numerator := 160654907747225330169937920 }, { target := 207, numerator := 160654907747225330169937920 }, { target := 208, numerator := 6881385215172818308945674240 }, { target := 209, numerator := 160654907747225330169937920 }, { target := 210, numerator := 1334328261567232603355873280 }, { target := 211, numerator := 6881385215172818308945674240 }, { target := 212, numerator := 142804362441978071262167040 }, { target := 213, numerator := 160654907747225330169937920 }, { target := 214, numerator := 160654907747225330169937920 }, { target := 215, numerator := 169580180399848959623823360 }, { target := 347, numerator := 606908573371999476672102400 }, { target := 350, numerator := 2171175349938226042031308800 }, { target := 352, numerator := 606908371610736170473881600 }, { target := 614, numerator := 12162447810374869512508932096 }, { target := 617, numerator := 43510354012762049882307428352 }, { target := 619, numerator := 12162443767079152856296587264 }, { target := 710, numerator := 20416404408234062395249524736 }, { target := 713, numerator := 73038338771921924053933228032 }, { target := 715, numerator := 20416397620985164774741377024 }, { target := 736, numerator := 19591008748448143106975465472 }, { target := 739, numerator := 70085540296005936636770648064 }, { target := 741, numerator := 19591002235594563582896898048 }, { target := 746, numerator := 10348405015901225735484866560 }, { target := 748, numerator := 10348405015901225735484866560 }, { target := 881, numerator := 606908573371999476672102400 }, { target := 884, numerator := 2171175349938226042031308800 }, { target := 886, numerator := 606908371610736170473881600 }, { target := 977, numerator := 19591008748448143106975465472 }, { target := 980, numerator := 70085540296005936636770648064 }, { target := 982, numerator := 19591002235594563582896898048 }, { target := 1003, numerator := 13084948841900308717050527744 }, { target := 1006, numerator := 46810540544668153466195017728 }, { target := 1008, numerator := 13084944491927471835416887296 }, { target := 1013, numerator := 9458635612664858662901121024 }, { target := 1015, numerator := 9458635612664858662901121024 }, { target := 1052, numerator := 631184916306879455738986496 }, { target := 1055, numerator := 2258022363935755083712561152 }, { target := 1057, numerator := 631184706475165617292836864 }, { target := 1078, numerator := 12162447810374869512508932096 }, { target := 1081, numerator := 43510354012762049882307428352 }, { target := 1083, numerator := 12162443767079152856296587264 }, { target := 1088, numerator := 10348405015901225735484866560 }, { target := 1090, numerator := 10348405015901225735484866560 }, { target := 1092, numerator := 582632230437119497605218304 }, { target := 1095, numerator := 2084328335940697000350056448 }, { target := 1097, numerator := 582632036746306723654926336 }, { target := 1102, numerator := 9458635612664858662901121024 }, { target := 1104, numerator := 9458635612664858662901121024 }]

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
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 296, numerator := 146884487083177444726800384 }, { target := 297, numerator := 174425328411273215613075456 }, { target := 298, numerator := 133114066419129559283662848 }, { target := 299, numerator := 1372451926183439249166041088 }, { target := 300, numerator := 165245047968574625317650432 }, { target := 301, numerator := 133114066419129559283662848 }, { target := 302, numerator := 165245047968574625317650432 }, { target := 303, numerator := 165245047968574625317650432 }, { target := 304, numerator := 7077996221320613117772693504 }, { target := 305, numerator := 165245047968574625317650432 }, { target := 306, numerator := 1372451926183439249166041088 }, { target := 307, numerator := 7077996221320613117772693504 }, { target := 308, numerator := 146884487083177444726800384 }, { target := 309, numerator := 165245047968574625317650432 }, { target := 310, numerator := 165245047968574625317650432 }, { target := 311, numerator := 174425328411273215613075456 }, { target := 331, numerator := 142804362441978071262167040 }, { target := 332, numerator := 169580180399848959623823360 }, { target := 333, numerator := 129416453463042627081338880 }, { target := 334, numerator := 1334328261567232603355873280 }, { target := 335, numerator := 160654907747225330169937920 }, { target := 336, numerator := 129416453463042627081338880 }, { target := 337, numerator := 160654907747225330169937920 }, { target := 338, numerator := 160654907747225330169937920 }, { target := 339, numerator := 6881385215172818308945674240 }, { target := 340, numerator := 160654907747225330169937920 }, { target := 341, numerator := 1334328261567232603355873280 }, { target := 342, numerator := 6881385215172818308945674240 }, { target := 343, numerator := 142804362441978071262167040 }, { target := 344, numerator := 160654907747225330169937920 }, { target := 345, numerator := 160654907747225330169937920 }, { target := 346, numerator := 169580180399848959623823360 }, { target := 467, numerator := 126483863877180577403633664 }, { target := 468, numerator := 150199588354151935666814976 }, { target := 469, numerator := 114626001638694898272043008 }, { target := 470, numerator := 1181833603102406020115202048 }, { target := 471, numerator := 142294346861828149579087872 }, { target := 472, numerator := 114626001638694898272043008 }, { target := 473, numerator := 142294346861828149579087872 }, { target := 474, numerator := 142294346861828149579087872 }, { target := 475, numerator := 6094941190581639073637597184 }, { target := 476, numerator := 142294346861828149579087872 }, { target := 477, numerator := 1181833603102406020115202048 }, { target := 478, numerator := 6094941190581639073637597184 }, { target := 479, numerator := 126483863877180577403633664 }, { target := 480, numerator := 142294346861828149579087872 }, { target := 481, numerator := 142294346861828149579087872 }, { target := 482, numerator := 150199588354151935666814976 }, { target := 563, numerator := 5920260854380290897182982144 }, { target := 564, numerator := 7030309764576595440404791296 }, { target := 565, numerator := 5365236399282138625572077568 }, { target := 566, numerator := 55317437358115843070553489408 }, { target := 567, numerator := 6660293461177827259330854912 }, { target := 568, numerator := 5365236399282138625572077568 }, { target := 569, numerator := 6660293461177827259330854912 }, { target := 570, numerator := 6660293461177827259330854912 }, { target := 571, numerator := 285282569920450267608004952064 }, { target := 572, numerator := 6660293461177827259330854912 }, { target := 573, numerator := 55317437358115843070553489408 }, { target := 574, numerator := 285282569920450267608004952064 }, { target := 575, numerator := 5920260854380290897182982144 }, { target := 576, numerator := 6660293461177827259330854912 }, { target := 577, numerator := 6660293461177827259330854912 }, { target := 578, numerator := 7030309764576595440404791296 }]

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
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 598, numerator := 1611649233273752518530170880 }, { target := 599, numerator := 1913833464512581115754577920 }, { target := 600, numerator := 1460557117654338219917967360 }, { target := 601, numerator := 15058847523401625095016284160 }, { target := 602, numerator := 1813105387432971583346442240 }, { target := 603, numerator := 1460557117654338219917967360 }, { target := 604, numerator := 1813105387432971583346442240 }, { target := 605, numerator := 1813105387432971583346442240 }, { target := 606, numerator := 77661347428378949486672609280 }, { target := 607, numerator := 1813105387432971583346442240 }, { target := 608, numerator := 15058847523401625095016284160 }, { target := 609, numerator := 77661347428378949486672609280 }, { target := 610, numerator := 1611649233273752518530170880 }, { target := 611, numerator := 1813105387432971583346442240 }, { target := 612, numerator := 1813105387432971583346442240 }, { target := 613, numerator := 1913833464512581115754577920 }, { target := 659, numerator := 146884487083177444726800384 }, { target := 660, numerator := 174425328411273215613075456 }, { target := 661, numerator := 133114066419129559283662848 }, { target := 662, numerator := 1372451926183439249166041088 }, { target := 663, numerator := 165245047968574625317650432 }, { target := 664, numerator := 133114066419129559283662848 }, { target := 665, numerator := 165245047968574625317650432 }, { target := 666, numerator := 165245047968574625317650432 }, { target := 667, numerator := 7077996221320613117772693504 }, { target := 668, numerator := 165245047968574625317650432 }, { target := 669, numerator := 1372451926183439249166041088 }, { target := 670, numerator := 7077996221320613117772693504 }, { target := 671, numerator := 146884487083177444726800384 }, { target := 672, numerator := 165245047968574625317650432 }, { target := 673, numerator := 165245047968574625317650432 }, { target := 674, numerator := 174425328411273215613075456 }, { target := 694, numerator := 5920260854380290897182982144 }, { target := 695, numerator := 7030309764576595440404791296 }, { target := 696, numerator := 5365236399282138625572077568 }, { target := 697, numerator := 55317437358115843070553489408 }, { target := 698, numerator := 6660293461177827259330854912 }, { target := 699, numerator := 5365236399282138625572077568 }, { target := 700, numerator := 6660293461177827259330854912 }, { target := 701, numerator := 6660293461177827259330854912 }, { target := 702, numerator := 285282569920450267608004952064 }, { target := 703, numerator := 6660293461177827259330854912 }, { target := 704, numerator := 55317437358115843070553489408 }, { target := 705, numerator := 285282569920450267608004952064 }, { target := 706, numerator := 5920260854380290897182982144 }, { target := 707, numerator := 6660293461177827259330854912 }, { target := 708, numerator := 6660293461177827259330854912 }, { target := 709, numerator := 7030309764576595440404791296 }, { target := 720, numerator := 142804362441978071262167040 }, { target := 721, numerator := 169580180399848959623823360 }, { target := 722, numerator := 129416453463042627081338880 }, { target := 723, numerator := 1334328261567232603355873280 }, { target := 724, numerator := 160654907747225330169937920 }, { target := 725, numerator := 129416453463042627081338880 }, { target := 726, numerator := 160654907747225330169937920 }, { target := 727, numerator := 160654907747225330169937920 }, { target := 728, numerator := 6881385215172818308945674240 }, { target := 729, numerator := 160654907747225330169937920 }, { target := 730, numerator := 1334328261567232603355873280 }, { target := 731, numerator := 6881385215172818308945674240 }, { target := 732, numerator := 142804362441978071262167040 }, { target := 733, numerator := 160654907747225330169937920 }, { target := 734, numerator := 160654907747225330169937920 }, { target := 735, numerator := 169580180399848959623823360 }]

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
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 830, numerator := 142804362441978071262167040 }, { target := 831, numerator := 169580180399848959623823360 }, { target := 832, numerator := 129416453463042627081338880 }, { target := 833, numerator := 1334328261567232603355873280 }, { target := 834, numerator := 160654907747225330169937920 }, { target := 835, numerator := 129416453463042627081338880 }, { target := 836, numerator := 160654907747225330169937920 }, { target := 837, numerator := 160654907747225330169937920 }, { target := 838, numerator := 6881385215172818308945674240 }, { target := 839, numerator := 160654907747225330169937920 }, { target := 840, numerator := 1334328261567232603355873280 }, { target := 841, numerator := 6881385215172818308945674240 }, { target := 842, numerator := 142804362441978071262167040 }, { target := 843, numerator := 160654907747225330169937920 }, { target := 844, numerator := 160654907747225330169937920 }, { target := 845, numerator := 169580180399848959623823360 }, { target := 865, numerator := 122403739235981203939000320 }, { target := 866, numerator := 145354440342727679677562880 }, { target := 867, numerator := 110928388682607966069719040 }, { target := 868, numerator := 1143709938486199374305034240 }, { target := 869, numerator := 137704206640478854431375360 }, { target := 870, numerator := 110928388682607966069719040 }, { target := 871, numerator := 137704206640478854431375360 }, { target := 872, numerator := 137704206640478854431375360 }, { target := 873, numerator := 5898330184433844264810577920 }, { target := 874, numerator := 137704206640478854431375360 }, { target := 875, numerator := 1143709938486199374305034240 }, { target := 876, numerator := 5898330184433844264810577920 }, { target := 877, numerator := 122403739235981203939000320 }, { target := 878, numerator := 137704206640478854431375360 }, { target := 879, numerator := 137704206640478854431375360 }, { target := 880, numerator := 145354440342727679677562880 }, { target := 926, numerator := 142804362441978071262167040 }, { target := 927, numerator := 169580180399848959623823360 }, { target := 928, numerator := 129416453463042627081338880 }, { target := 929, numerator := 1334328261567232603355873280 }, { target := 930, numerator := 160654907747225330169937920 }, { target := 931, numerator := 129416453463042627081338880 }, { target := 932, numerator := 160654907747225330169937920 }, { target := 933, numerator := 160654907747225330169937920 }, { target := 934, numerator := 6881385215172818308945674240 }, { target := 935, numerator := 160654907747225330169937920 }, { target := 936, numerator := 1334328261567232603355873280 }, { target := 937, numerator := 6881385215172818308945674240 }, { target := 938, numerator := 142804362441978071262167040 }, { target := 939, numerator := 160654907747225330169937920 }, { target := 940, numerator := 160654907747225330169937920 }, { target := 941, numerator := 169580180399848959623823360 }, { target := 961, numerator := 1611649233273752518530170880 }, { target := 962, numerator := 1913833464512581115754577920 }, { target := 963, numerator := 1460557117654338219917967360 }, { target := 964, numerator := 15058847523401625095016284160 }, { target := 965, numerator := 1813105387432971583346442240 }, { target := 966, numerator := 1460557117654338219917967360 }, { target := 967, numerator := 1813105387432971583346442240 }, { target := 968, numerator := 1813105387432971583346442240 }, { target := 969, numerator := 77661347428378949486672609280 }, { target := 970, numerator := 1813105387432971583346442240 }, { target := 971, numerator := 15058847523401625095016284160 }, { target := 972, numerator := 77661347428378949486672609280 }, { target := 973, numerator := 1611649233273752518530170880 }, { target := 974, numerator := 1813105387432971583346442240 }, { target := 975, numerator := 1813105387432971583346442240 }, { target := 976, numerator := 1913833464512581115754577920 }]

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
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 347, numerator := 74565516959620362172045983744 }, { target := 350, numerator := 271210858511428698282582343680 }, { target := 352, numerator := 74565516959620362172045983744 }, { target := 710, numerator := 722247046936459754779881504768 }, { target := 713, numerator := 2626968197150130575986613288960 }, { target := 715, numerator := 722247046936459754779881504768 }, { target := 746, numerator := 39614090701865134536062402560 }, { target := 748, numerator := 39614071812399203057481547776 }, { target := 987, numerator := 122403739235981203939000320 }, { target := 988, numerator := 145354440342727679677562880 }, { target := 989, numerator := 110928388682607966069719040 }, { target := 990, numerator := 1143709938486199374305034240 }, { target := 991, numerator := 137704206640478854431375360 }, { target := 992, numerator := 110928388682607966069719040 }, { target := 993, numerator := 137704206640478854431375360 }, { target := 994, numerator := 137704206640478854431375360 }, { target := 995, numerator := 5898330184433844264810577920 }, { target := 996, numerator := 137704206640478854431375360 }, { target := 997, numerator := 1143709938486199374305034240 }, { target := 998, numerator := 5898330184433844264810577920 }, { target := 999, numerator := 122403739235981203939000320 }, { target := 1000, numerator := 137704206640478854431375360 }, { target := 1001, numerator := 137704206640478854431375360 }, { target := 1002, numerator := 145354440342727679677562880 }, { target := 1013, numerator := 39614090701865134536062402560 }, { target := 1015, numerator := 39614071812399203057481547776 }, { target := 1036, numerator := 142804362441978071262167040 }, { target := 1037, numerator := 169580180399848959623823360 }, { target := 1038, numerator := 129416453463042627081338880 }, { target := 1039, numerator := 1334328261567232603355873280 }, { target := 1040, numerator := 160654907747225330169937920 }, { target := 1041, numerator := 129416453463042627081338880 }, { target := 1042, numerator := 160654907747225330169937920 }, { target := 1043, numerator := 160654907747225330169937920 }, { target := 1044, numerator := 6881385215172818308945674240 }, { target := 1045, numerator := 160654907747225330169937920 }, { target := 1046, numerator := 1334328261567232603355873280 }, { target := 1047, numerator := 6881385215172818308945674240 }, { target := 1048, numerator := 142804362441978071262167040 }, { target := 1049, numerator := 160654907747225330169937920 }, { target := 1050, numerator := 160654907747225330169937920 }, { target := 1051, numerator := 169580180399848959623823360 }, { target := 1062, numerator := 126483863877180577403633664 }, { target := 1063, numerator := 150199588354151935666814976 }, { target := 1064, numerator := 114626001638694898272043008 }, { target := 1065, numerator := 1181833603102406020115202048 }, { target := 1066, numerator := 142294346861828149579087872 }, { target := 1067, numerator := 114626001638694898272043008 }, { target := 1068, numerator := 142294346861828149579087872 }, { target := 1069, numerator := 142294346861828149579087872 }, { target := 1070, numerator := 6094941190581639073637597184 }, { target := 1071, numerator := 142294346861828149579087872 }, { target := 1072, numerator := 1181833603102406020115202048 }, { target := 1073, numerator := 6094941190581639073637597184 }, { target := 1074, numerator := 126483863877180577403633664 }, { target := 1075, numerator := 142294346861828149579087872 }, { target := 1076, numerator := 142294346861828149579087872 }, { target := 1077, numerator := 150199588354151935666814976 }, { target := 1088, numerator := 39614090701865134536062402560 }, { target := 1090, numerator := 39614071812399203057481547776 }, { target := 1102, numerator := 39614090701865134536062402560 }, { target := 1104, numerator := 39614071812399203057481547776 }]

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
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 51821844371697370828636160 }, { target := 72, numerator := 870606985444515829921087488 }, { target := 73, numerator := 1886315135129784298162356224 }, { target := 74, numerator := 62186213246036844994363392 }, { target := 75, numerator := 994979411936589519909814272 }, { target := 76, numerator := 72550582120376319160090624 }, { target := 77, numerator := 1886315135129784298162356224 }, { target := 78, numerator := 1886315135129784298162356224 }, { target := 79, numerator := 994979411936589519909814272 }, { target := 80, numerator := 23278372491766458976223363072 }, { target := 81, numerator := 1865586397381105349830901760 }, { target := 82, numerator := 870606985444515829921087488 }, { target := 83, numerator := 1886315135129784298162356224 }, { target := 84, numerator := 72550582120376319160090624 }, { target := 85, numerator := 1865586397381105349830901760 }, { target := 86, numerator := 72550582120376319160090624 }, { target := 87, numerator := 1886315135129784298162356224 }, { target := 88, numerator := 1886315135129784298162356224 }, { target := 89, numerator := 62186213246036844994363392 }, { target := 146, numerator := 5433426918196624991966986240 }, { target := 147, numerator := 91281572225703299865045368832 }, { target := 148, numerator := 197776739822357149707598299136 }, { target := 149, numerator := 6520112301835949990360383488 }, { target := 150, numerator := 104321796829375199845766135808 }, { target := 151, numerator := 7606797685475274988753780736 }, { target := 152, numerator := 197776739822357149707598299136 }, { target := 153, numerator := 197776739822357149707598299136 }, { target := 154, numerator := 104321796829375199845766135808 }, { target := 155, numerator := 2440695371653923946391570219008 }, { target := 156, numerator := 195603369055078499710811504640 }, { target := 157, numerator := 91281572225703299865045368832 }, { target := 158, numerator := 197776739822357149707598299136 }, { target := 159, numerator := 7606797685475274988753780736 }, { target := 160, numerator := 195603369055078499710811504640 }, { target := 161, numerator := 7606797685475274988753780736 }, { target := 162, numerator := 197776739822357149707598299136 }, { target := 163, numerator := 197776739822357149707598299136 }, { target := 164, numerator := 6520112301835949990360383488 }, { target := 200, numerator := 3716520415452663999753093120 }, { target := 202, numerator := 137246154515954867151411609600 }, { target := 205, numerator := 137246120907834203649783889920 }, { target := 212, numerator := 3716554023573327501380812800 }, { target := 296, numerator := 311181039194966414325996060672 }, { target := 298, numerator := 11491501784898974946749589749760 }, { target := 301, numerator := 11491498970920106439855153610752 }, { target := 308, numerator := 311183853173834921220432199680 }, { target := 659, numerator := 311181151811109501624536530944 }, { target := 661, numerator := 11491505943663315615045145067520 }, { target := 664, numerator := 11491503129683428731684969775104 }, { target := 671, numerator := 311183965790996384984711823360 }, { target := 1036, numerator := 3716407799309576701212622848 }, { target := 1038, numerator := 137241995751614198855856291840 }, { target := 1041, numerator := 137241962144511911819967725568 }, { target := 1048, numerator := 3716441406411863737101189120 }, { target := 1052, numerator := 74565516959620362172045983744 }, { target := 1055, numerator := 271210858511428698282582343680 }, { target := 1057, numerator := 74565516959620362172045983744 }]

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
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 58566911474344016341893120000 }, { target := 243, numerator := 983924112768979474543804416000 }, { target := 244, numerator := 2131835577666122194844909568000 }, { target := 245, numerator := 70280293769212819610271744000 }, { target := 246, numerator := 1124484700307405113764347904000 }, { target := 247, numerator := 81993676064081622878650368000 }, { target := 248, numerator := 2131835577666122194844909568000 }, { target := 249, numerator := 2131835577666122194844909568000 }, { target := 250, numerator := 1124484700307405113764347904000 }, { target := 251, numerator := 26308256634275332140778389504000 }, { target := 252, numerator := 2108408813076384588308152320000 }, { target := 253, numerator := 983924112768979474543804416000 }, { target := 254, numerator := 2131835577666122194844909568000 }, { target := 255, numerator := 81993676064081622878650368000 }, { target := 256, numerator := 2108408813076384588308152320000 }, { target := 257, numerator := 81993676064081622878650368000 }, { target := 258, numerator := 2131835577666122194844909568000 }, { target := 259, numerator := 2131835577666122194844909568000 }, { target := 260, numerator := 70280293769212819610271744000 }, { target := 347, numerator := 7836352264931098320038789120 }, { target := 350, numerator := 26900827133686584376375115776 }, { target := 352, numerator := 7836352264931098320038789120 }, { target := 614, numerator := 187566883244479837208670371840 }, { target := 617, numerator := 643884313974046632492591480832 }, { target := 619, numerator := 187566883244479837208670371840 }, { target := 640, numerator := 5433431062949434053581864960 }, { target := 641, numerator := 91281641857550492100175331328 }, { target := 642, numerator := 197776890691359399550379884544 }, { target := 643, numerator := 6520117275539320864298237952 }, { target := 644, numerator := 104321876408629133828771807232 }, { target := 645, numerator := 7606803488129207675014610944 }, { target := 646, numerator := 197776890691359399550379884544 }, { target := 647, numerator := 197776890691359399550379884544 }, { target := 648, numerator := 104321876408629133828771807232 }, { target := 649, numerator := 2440697233476885776868973740032 }, { target := 650, numerator := 195603518266179625928947138560 }, { target := 651, numerator := 91281641857550492100175331328 }, { target := 652, numerator := 197776890691359399550379884544 }, { target := 653, numerator := 7606803488129207675014610944 }, { target := 654, numerator := 195603518266179625928947138560 }, { target := 655, numerator := 7606803488129207675014610944 }, { target := 656, numerator := 197776890691359399550379884544 }, { target := 657, numerator := 197776890691359399550379884544 }, { target := 658, numerator := 6520117275539320864298237952 }, { target := 1017, numerator := 51821844371697370828636160 }, { target := 1018, numerator := 870606985444515829921087488 }, { target := 1019, numerator := 1886315135129784298162356224 }, { target := 1020, numerator := 62186213246036844994363392 }, { target := 1021, numerator := 994979411936589519909814272 }, { target := 1022, numerator := 72550582120376319160090624 }, { target := 1023, numerator := 1886315135129784298162356224 }, { target := 1024, numerator := 1886315135129784298162356224 }, { target := 1025, numerator := 994979411936589519909814272 }, { target := 1026, numerator := 23278372491766458976223363072 }, { target := 1027, numerator := 1865586397381105349830901760 }, { target := 1028, numerator := 870606985444515829921087488 }, { target := 1029, numerator := 1886315135129784298162356224 }, { target := 1030, numerator := 72550582120376319160090624 }, { target := 1031, numerator := 1865586397381105349830901760 }, { target := 1032, numerator := 72550582120376319160090624 }, { target := 1033, numerator := 1886315135129784298162356224 }, { target := 1034, numerator := 1886315135129784298162356224 }, { target := 1035, numerator := 62186213246036844994363392 }]

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
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 80079359617872475847655424 }, { target := 72, numerator := 12784444985238137703936032768 }, { target := 74, numerator := 127569535692999481879521394688 }, { target := 82, numerator := 12784444985238137703936032768 }, { target := 89, numerator := 80070222310750400028868608 }, { target := 146, numerator := 11827302344682850482529501184 }, { target := 147, numerator := 1888195620830479334428364505088 }, { target := 149, numerator := 18841352825643397529305568247808 }, { target := 157, numerator := 1888195620830479334428364505088 }, { target := 164, numerator := 11825952812238226697672982528 }, { target := 200, numerator := 8255672794423070942337957888 }, { target := 202, numerator := 310186835108424729695266799616 }, { target := 205, numerator := 310163375021854471561760735232 }, { target := 212, numerator := 8279132880993329075844022272 }, { target := 242, numerator := 123273994359159008183409704960 }, { target := 243, numerator := 19680347177045710632336983326720 }, { target := 245, numerator := 196380269503423329842400612843520 }, { target := 253, numerator := 19680347177045710632336983326720 }, { target := 260, numerator := 123259928408182381185670840320 }, { target := 296, numerator := 694213266493911259403387928576 }, { target := 298, numerator := 26083375805481644396951038328832 }, { target := 301, numerator := 26081403064587507861616972529664 }, { target := 308, numerator := 696186007388047794737453727744 }, { target := 640, numerator := 11827302344682850482529501184 }, { target := 641, numerator := 1888195620830479334428364505088 }, { target := 643, numerator := 18841352825643397529305568247808 }, { target := 651, numerator := 1888195620830479334428364505088 }, { target := 658, numerator := 11825952812238226697672982528 }, { target := 659, numerator := 694213099012264891296943964160 }, { target := 661, numerator := 26083369512765942199382829957120 }, { target := 664, numerator := 26081396772347737065470023434240 }, { target := 671, numerator := 696185839430470025209750487040 }, { target := 710, numerator := 140295984097959986052307353600 }, { target := 713, numerator := 481611582554711429964135137280 }, { target := 715, numerator := 140295984097959986052307353600 }, { target := 736, numerator := 162793898665020236067902586880 }, { target := 739, numerator := 558842989486908398012437889024 }, { target := 741, numerator := 162793898665020236067902586880 }, { target := 881, numerator := 7836352264931098320038789120 }, { target := 884, numerator := 26900827133686584376375115776 }, { target := 886, numerator := 7836352264931098320038789120 }, { target := 977, numerator := 162541113108086974831772303360 }, { target := 980, numerator := 557975220869692701742232240128 }, { target := 982, numerator := 162541113108086974831772303360 }, { target := 1003, numerator := 163299469778886758540163153920 }, { target := 1006, numerator := 560578526721339790552849186816 }, { target := 1008, numerator := 163299469778886758540163153920 }, { target := 1036, numerator := 8255840276069439048781922304 }, { target := 1038, numerator := 310193127824126927263475171328 }, { target := 1041, numerator := 310169667261625267708709830656 }, { target := 1048, numerator := 8279300838571098603547262976 }, { target := 1052, numerator := 7836352264931098320038789120 }, { target := 1055, numerator := 26900827133686584376375115776 }, { target := 1057, numerator := 7836352264931098320038789120 }, { target := 1078, numerator := 187566883244479837208670371840 }, { target := 1081, numerator := 643884313974046632492591480832 }, { target := 1083, numerator := 187566883244479837208670371840 }, { target := 1092, numerator := 7836352264931098320038789120 }, { target := 1095, numerator := 26900827133686584376375115776 }, { target := 1097, numerator := 7836352264931098320038789120 }]

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
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 7000280522036560508988948480 }, { target := 30, numerator := 5444662628250658173658071040 }, { target := 31, numerator := 6222471575143609341323509760 }, { target := 32, numerator := 7311404100793740976055123968 }, { target := 33, numerator := 86336793105117579610863697920 }, { target := 34, numerator := 194141113144480611449293504512 }, { target := 35, numerator := 5444662628250658173658071040 }, { target := 36, numerator := 86336793105117579610863697920 }, { target := 37, numerator := 6222471575143609341323509760 }, { target := 38, numerator := 6066909785765019107790422016 }, { target := 39, numerator := 6066909785765019107790422016 }, { target := 40, numerator := 6066909785765019107790422016 }, { target := 41, numerator := 194141113144480611449293504512 }, { target := 42, numerator := 6066909785765019107790422016 }, { target := 43, numerator := 7000280522036560508988948480 }, { target := 44, numerator := 7311404100793740976055123968 }, { target := 104, numerator := 253692483219662074724650844160 }, { target := 105, numerator := 197316375837514947008061767680 }, { target := 106, numerator := 225504429528588510866356305920 }, { target := 107, numerator := 264967704696091500267968659456 }, { target := 108, numerator := 3128873959709165588270693744640 }, { target := 109, numerator := 7035738201291961539030316744704 }, { target := 110, numerator := 197316375837514947008061767680 }, { target := 111, numerator := 3128873959709165588270693744640 }, { target := 112, numerator := 225504429528588510866356305920 }, { target := 113, numerator := 219866818790373798094697398272 }, { target := 114, numerator := 219866818790373798094697398272 }, { target := 115, numerator := 219866818790373798094697398272 }, { target := 116, numerator := 7035738201291961539030316744704 }, { target := 117, numerator := 219866818790373798094697398272 }, { target := 118, numerator := 253692483219662074724650844160 }, { target := 119, numerator := 264967704696091500267968659456 }, { target := 226, numerator := 253692576450659544757331558400 }, { target := 227, numerator := 197316448350512979255702323200 }, { target := 228, numerator := 225504512400586262006516940800 }, { target := 229, numerator := 264967802070688857857657405440 }, { target := 230, numerator := 3128875109558134385340422553600 }, { target := 231, numerator := 7035740786898291374603328552960 }, { target := 232, numerator := 197316448350512979255702323200 }, { target := 233, numerator := 3128875109558134385340422553600 }, { target := 234, numerator := 225504512400586262006516940800 }, { target := 235, numerator := 219866899590571605456354017280 }, { target := 236, numerator := 219866899590571605456354017280 }, { target := 237, numerator := 219866899590571605456354017280 }, { target := 238, numerator := 7035740786898291374603328552960 }, { target := 239, numerator := 219866899590571605456354017280 }, { target := 240, numerator := 253692576450659544757331558400 }, { target := 241, numerator := 264967802070688857857657405440 }, { target := 1017, numerator := 80079359617872475847655424 }, { target := 1018, numerator := 12784444985238137703936032768 }, { target := 1020, numerator := 127569535692999481879521394688 }, { target := 1028, numerator := 12784444985238137703936032768 }, { target := 1035, numerator := 80070222310750400028868608 }]

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
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected,
    Slot12.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 7093773417155579681062256640 }, { target := 202, numerator := 257080696685033187575731322880 }, { target := 205, numerator := 257080791161185882583806771200 }, { target := 212, numerator := 7093678941002884672986808320 }, { target := 296, numerator := 5517379324454339751937310720 }, { target := 298, numerator := 199951652977248034781124362240 }, { target := 301, numerator := 199951726458700130898516377600 }, { target := 308, numerator := 5517305843002243634545295360 }, { target := 331, numerator := 6305576370804959716499783680 }, { target := 333, numerator := 228516174831140611178427842560 }, { target := 336, numerator := 228516258809943006741161574400 }, { target := 343, numerator := 6305492392002564153766051840 }, { target := 467, numerator := 7409052235695827666887245824 }, { target := 469, numerator := 268506505426590218134652715008 }, { target := 472, numerator := 268506604101683032920864849920 }, { target := 479, numerator := 7408953560603012880675110912 }, { target := 563, numerator := 87489872144918816066434498560 }, { target := 565, numerator := 3170661925782075980100686315520 }, { target := 568, numerator := 3170663090987959218533616844800 }, { target := 575, numerator := 87488706939035577633503969280 }, { target := 598, numerator := 196733982769114743154793250816 }, { target := 600, numerator := 7129704654731587068766948687872 }, { target := 603, numerator := 7129707274870221810324241121280 }, { target := 610, numerator := 196731362630480001597500817408 }, { target := 624, numerator := 7000187291039090476308234240 }, { target := 625, numerator := 5444590115252625926017515520 }, { target := 626, numerator := 6222388703145858201162874880 }, { target := 627, numerator := 7311306726196383386366377984 }, { target := 628, numerator := 86335643256148782541134888960 }, { target := 629, numerator := 194138527538150775876281696256 }, { target := 630, numerator := 5444590115252625926017515520 }, { target := 631, numerator := 86335643256148782541134888960 }, { target := 632, numerator := 6222388703145858201162874880 }, { target := 633, numerator := 6066828985567211746133803008 }, { target := 634, numerator := 6066828985567211746133803008 }, { target := 635, numerator := 6066828985567211746133803008 }, { target := 636, numerator := 194138527538150775876281696256 }, { target := 637, numerator := 6066828985567211746133803008 }, { target := 638, numerator := 7000187291039090476308234240 }, { target := 639, numerator := 7311306726196383386366377984 }, { target := 659, numerator := 5517379324454339751937310720 }, { target := 661, numerator := 199951652977248034781124362240 }, { target := 664, numerator := 199951726458700130898516377600 }, { target := 671, numerator := 5517305843002243634545295360 }, { target := 694, numerator := 87489872144918816066434498560 }, { target := 696, numerator := 3170661925782075980100686315520 }, { target := 699, numerator := 3170663090987959218533616844800 }, { target := 706, numerator := 87488706939035577633503969280 }, { target := 720, numerator := 6305576370804959716499783680 }, { target := 722, numerator := 228516174831140611178427842560 }, { target := 725, numerator := 228516258809943006741161574400 }, { target := 732, numerator := 6305492392002564153766051840 }, { target := 830, numerator := 6147936961534835723587289088 }, { target := 832, numerator := 222803270460362095898967146496 }, { target := 835, numerator := 222803352339694431572632535040 }, { target := 842, numerator := 6147855082202500049921900544 }, { target := 865, numerator := 6147936961534835723587289088 }, { target := 867, numerator := 222803270460362095898967146496 }, { target := 870, numerator := 222803352339694431572632535040 }, { target := 877, numerator := 6147855082202500049921900544 }, { target := 926, numerator := 6147936961534835723587289088 }, { target := 928, numerator := 222803270460362095898967146496 }, { target := 931, numerator := 222803352339694431572632535040 }, { target := 938, numerator := 6147855082202500049921900544 }]

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
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 8237568248821265962201251840 }, { target := 30, numerator := 692690868979670225939784007680 }, { target := 35, numerator := 692690701865308170044099788800 }, { target := 43, numerator := 8237735363183321857885470720 }, { target := 71, numerator := 80034295262431917335642112 }, { target := 72, numerator := 11820646575214824117598420992 }, { target := 74, numerator := 123204622387094202888990228480 }, { target := 82, numerator := 11820646575214824117598420992 }, { target := 89, numerator := 80034295262431917335642112 }, { target := 104, numerator := 309506600820906254410847354880 }, { target := 105, numerator := 26026175419943307457484040437760 }, { target := 110, numerator := 26026169141027420396314007961600 }, { target := 118, numerator := 309512879736793315580879831040 }, { target := 146, numerator := 12777250587384880451429597184 }, { target := 147, numerator := 1887133045917237646564308025344 }, { target := 149, numerator := 19669272136428352325847204495360 }, { target := 157, numerator := 1887133045917237646564308025344 }, { target := 164, numerator := 12777250587384880451429597184 }, { target := 226, numerator := 309483192181894264387283189760 }, { target := 227, numerator := 26024207005235342274201145835520 }, { target := 232, numerator := 26024200726794342905238729523200 }, { target := 240, numerator := 309489470622893633349699502080 }, { target := 242, numerator := 127497746421365829948244230144 }, { target := 243, numerator := 18830749925910339905484912328704 }, { target := 245, numerator := 196269757252717970624706521333760 }, { target := 253, numerator := 18830749925910339905484912328704 }, { target := 260, numerator := 127497746421365829948244230144 }, { target := 624, numerator := 8260976887833255985765416960 }, { target := 625, numerator := 694659283687635409222678609920 }, { target := 630, numerator := 694659116098385661119378227200 }, { target := 638, numerator := 8261144477083004089065799680 }, { target := 640, numerator := 12777250587384880451429597184 }, { target := 641, numerator := 1887133045917237646564308025344 }, { target := 643, numerator := 19669272136428352325847204495360 }, { target := 651, numerator := 1887133045917237646564308025344 }, { target := 658, numerator := 12777250587384880451429597184 }, { target := 961, numerator := 196733982769114743154793250816 }, { target := 963, numerator := 7129704654731587068766948687872 }, { target := 966, numerator := 7129707274870221810324241121280 }, { target := 973, numerator := 196731362630480001597500817408 }, { target := 987, numerator := 6147936961534835723587289088 }, { target := 989, numerator := 222803270460362095898967146496 }, { target := 992, numerator := 222803352339694431572632535040 }, { target := 999, numerator := 6147855082202500049921900544 }, { target := 1017, numerator := 80025163097294716067119104 }, { target := 1018, numerator := 11819297802214457296042328064 }, { target := 1020, numerator := 123190564351678057954840412160 }, { target := 1028, numerator := 11819297802214457296042328064 }, { target := 1035, numerator := 80025163097294716067119104 }, { target := 1036, numerator := 7093773417155579681062256640 }, { target := 1038, numerator := 257080696685033187575731322880 }, { target := 1041, numerator := 257080791161185882583806771200 }, { target := 1048, numerator := 7093678941002884672986808320 }, { target := 1062, numerator := 7409052235695827666887245824 }, { target := 1064, numerator := 268506505426590218134652715008 }, { target := 1067, numerator := 268506604101683032920864849920 }, { target := 1074, numerator := 7408953560603012880675110912 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 7836352264931098320038789120 }, { target := 6, numerator := 187566883244479837208670371840 }, { target := 7, numerator := 140295984097959986052307353600 }, { target := 8, numerator := 162793898665020236067902586880 }, { target := 9, numerator := 7836352264931098320038789120 }, { target := 10, numerator := 162541113108086974831772303360 }, { target := 11, numerator := 163299469778886758540163153920 }, { target := 12, numerator := 7836352264931098320038789120 }, { target := 13, numerator := 187566883244479837208670371840 }, { target := 14, numerator := 7836352264931098320038789120 }, { target := 71, numerator := 51749769483836873789931520 }, { target := 72, numerator := 5425869996196351521880801280 }, { target := 74, numerator := 58485455408315721465200640000 }, { target := 82, numerator := 5425874135184553060461445120 }, { target := 89, numerator := 51749769483836873789931520 }, { target := 94, numerator := 26900827133686584376375115776 }, { target := 95, numerator := 643884313974046632492591480832 }, { target := 96, numerator := 481611582554711429964135137280 }, { target := 97, numerator := 558842989486908398012437889024 }, { target := 98, numerator := 26900827133686584376375115776 }, { target := 99, numerator := 557975220869692701742232240128 }, { target := 100, numerator := 560578526721339790552849186816 }, { target := 101, numerator := 26900827133686584376375115776 }, { target := 102, numerator := 643884313974046632492591480832 }, { target := 103, numerator := 26900827133686584376375115776 }, { target := 146, numerator := 869396127328459479670849536 }, { target := 147, numerator := 91154615936098705567597461504 }, { target := 149, numerator := 982555650859704120615370752000 }, { target := 157, numerator := 91154685471100491415752278016 }, { target := 164, numerator := 869396127328459479670849536 }, { target := 181, numerator := 1883691609211662205953507328 }, { target := 182, numerator := 197501667861547195396461166592 }, { target := 184, numerator := 2128870576862692261333303296000 }, { target := 192, numerator := 197501818520717731400796602368 }, { target := 199, numerator := 1883691609211662205953507328 }, { target := 216, numerator := 7836352264931098320038789120 }, { target := 217, numerator := 187566883244479837208670371840 }, { target := 218, numerator := 140295984097959986052307353600 }, { target := 219, numerator := 162793898665020236067902586880 }, { target := 220, numerator := 7836352264931098320038789120 }, { target := 221, numerator := 162541113108086974831772303360 }, { target := 222, numerator := 163299469778886758540163153920 }, { target := 223, numerator := 7836352264931098320038789120 }, { target := 224, numerator := 187566883244479837208670371840 }, { target := 225, numerator := 7836352264931098320038789120 }, { target := 242, numerator := 62099723380604248547917824 }, { target := 243, numerator := 6511043995435621826256961536 }, { target := 245, numerator := 70182546489978865758240768000 }, { target := 253, numerator := 6511048962221463672553734144 }, { target := 260, numerator := 62099723380604248547917824 }, { target := 277, numerator := 993595574089667976766685184 }, { target := 278, numerator := 104176703926969949220111384576 }, { target := 280, numerator := 1122920743839661852131852288000 }, { target := 288, numerator := 104176783395543418760859746304 }, { target := 295, numerator := 993595574089667976766685184 }, { target := 312, numerator := 72449677277371623305904128 }, { target := 313, numerator := 7596217994674892130633121792 }, { target := 315, numerator := 81879637571642010051280896000 }, { target := 323, numerator := 7596223789258374284646023168 }, { target := 330, numerator := 72449677277371623305904128 }]

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
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot16.Left10.expected,
    Slot16.Left11.expected,
    Slot16.Left12.expected,
    Slot16.Left13.expected,
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot16.Left16.expected,
    Slot16.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 1883691609211662205953507328 }, { target := 414, numerator := 197501667861547195396461166592 }, { target := 416, numerator := 2128870576862692261333303296000 }, { target := 424, numerator := 197501818520717731400796602368 }, { target := 431, numerator := 1883691609211662205953507328 }, { target := 448, numerator := 1883691609211662205953507328 }, { target := 449, numerator := 197501667861547195396461166592 }, { target := 451, numerator := 2128870576862692261333303296000 }, { target := 459, numerator := 197501818520717731400796602368 }, { target := 466, numerator := 1883691609211662205953507328 }, { target := 509, numerator := 993595574089667976766685184 }, { target := 510, numerator := 104176703926969949220111384576 }, { target := 512, numerator := 1122920743839661852131852288000 }, { target := 520, numerator := 104176783395543418760859746304 }, { target := 527, numerator := 993595574089667976766685184 }, { target := 544, numerator := 23245996452139523706437238784 }, { target := 545, numerator := 2437300802291401103628855934976 }, { target := 547, numerator := 26271666569415422082168127488000 }, { target := 555, numerator := 2437302661524901234759281147904 }, { target := 562, numerator := 23245996452139523706437238784 }, { target := 579, numerator := 1862991701418127456437534720 }, { target := 580, numerator := 195331319863068654787708846080 }, { target := 582, numerator := 2105476394699365972747223040000 }, { target := 590, numerator := 195331468866643910176612024320 }, { target := 597, numerator := 1862991701418127456437534720 }, { target := 640, numerator := 869396127328459479670849536 }, { target := 641, numerator := 91154615936098705567597461504 }, { target := 643, numerator := 982555650859704120615370752000 }, { target := 651, numerator := 91154685471100491415752278016 }, { target := 658, numerator := 869396127328459479670849536 }, { target := 675, numerator := 1883691609211662205953507328 }, { target := 676, numerator := 197501667861547195396461166592 }, { target := 678, numerator := 2128870576862692261333303296000 }, { target := 686, numerator := 197501818520717731400796602368 }, { target := 693, numerator := 1883691609211662205953507328 }, { target := 776, numerator := 72449677277371623305904128 }, { target := 777, numerator := 7596217994674892130633121792 }, { target := 779, numerator := 81879637571642010051280896000 }, { target := 787, numerator := 7596223789258374284646023168 }, { target := 794, numerator := 72449677277371623305904128 }, { target := 811, numerator := 1862991701418127456437534720 }, { target := 812, numerator := 195331319863068654787708846080 }, { target := 814, numerator := 2105476394699365972747223040000 }, { target := 822, numerator := 195331468866643910176612024320 }, { target := 829, numerator := 1862991701418127456437534720 }, { target := 846, numerator := 72449677277371623305904128 }, { target := 847, numerator := 7596217994674892130633121792 }, { target := 849, numerator := 81879637571642010051280896000 }, { target := 857, numerator := 7596223789258374284646023168 }, { target := 864, numerator := 72449677277371623305904128 }, { target := 907, numerator := 1883691609211662205953507328 }, { target := 908, numerator := 197501667861547195396461166592 }, { target := 910, numerator := 2128870576862692261333303296000 }, { target := 918, numerator := 197501818520717731400796602368 }, { target := 925, numerator := 1883691609211662205953507328 }, { target := 942, numerator := 1883691609211662205953507328 }, { target := 943, numerator := 197501667861547195396461166592 }, { target := 945, numerator := 2128870576862692261333303296000 }, { target := 953, numerator := 197501818520717731400796602368 }, { target := 960, numerator := 1883691609211662205953507328 }]

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
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 39614090701865134536062402560 }, { target := 2, numerator := 39614090701865134536062402560 }, { target := 3, numerator := 39614090701865134536062402560 }, { target := 4, numerator := 39614090701865134536062402560 }, { target := 5, numerator := 72160177702858415005205790720 }, { target := 7, numerator := 698948755099799762690207907840 }, { target := 12, numerator := 72160177702858415005205790720 }, { target := 29, numerator := 3916543898482100805367234560 }, { target := 30, numerator := 316993646054722198677944795136 }, { target := 31, numerator := 132226261520350065983488000 }, { target := 32, numerator := 117114688775167201299660800 }, { target := 33, numerator := 5481723013315084164058316800 }, { target := 34, numerator := 1492267808586807887527936000 }, { target := 35, numerator := 316993760725222788398183350272 }, { target := 36, numerator := 5481723013315084164058316800 }, { target := 37, numerator := 132226261520350065983488000 }, { target := 38, numerator := 132226261520350065983488000 }, { target := 39, numerator := 113336795588871485128704000 }, { target := 40, numerator := 132226261520350065983488000 }, { target := 41, numerator := 1492267808586807887527936000 }, { target := 42, numerator := 113336795588871485128704000 }, { target := 43, numerator := 3916429227981511085128679424 }, { target := 44, numerator := 117114688775167201299660800 }, { target := 90, numerator := 39614071812399203057481547776 }, { target := 91, numerator := 39614071812399203057481547776 }, { target := 92, numerator := 39614071812399203057481547776 }, { target := 93, numerator := 39614071812399203057481547776 }, { target := 94, numerator := 262462121140092288660563558400 }, { target := 96, numerator := 2542227287564642492890270924800 }, { target := 101, numerator := 262462121140092288660563558400 }, { target := 104, numerator := 139749815709446581145881804800 }, { target := 105, numerator := 11701131170693151935827940474880 }, { target := 110, numerator := 11701135405322182069050943733760 }, { target := 118, numerator := 139745581080416447922878545920 }, { target := 216, numerator := 72160177702858415005205790720 }, { target := 218, numerator := 698948755099799762690207907840 }, { target := 223, numerator := 72160177702858415005205790720 }, { target := 226, numerator := 139749781488242456121007144960 }, { target := 227, numerator := 11701128305381335578890653925376 }, { target := 232, numerator := 11701132540009328758299455127552 }, { target := 240, numerator := 139745546860249276712205942784 }, { target := 624, numerator := 3784351858165875764258406400 }, { target := 625, numerator := 316860507211831909833076899840 }, { target := 630, numerator := 316860621883369453367517511680 }, { target := 638, numerator := 3784237186628332229817794560 }, { target := 1017, numerator := 62099723380604248547917824 }, { target := 1018, numerator := 6511043995435621826256961536 }, { target := 1020, numerator := 70182546489978865758240768000 }, { target := 1028, numerator := 6511048962221463672553734144 }, { target := 1035, numerator := 62099723380604248547917824 }]

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
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 157018685555415703355392000 }, { target := 56, numerator := 161504933714141866308403200 }, { target := 57, numerator := 157018685555415703355392000 }, { target := 58, numerator := 139073692920511051543347200 }, { target := 59, numerator := 6509546078311662444819251200 }, { target := 60, numerator := 1772068022696834366439424000 }, { target := 61, numerator := 161504933714141866308403200 }, { target := 62, numerator := 6509546078311662444819251200 }, { target := 63, numerator := 157018685555415703355392000 }, { target := 64, numerator := 157018685555415703355392000 }, { target := 65, numerator := 134587444761784888590336000 }, { target := 66, numerator := 157018685555415703355392000 }, { target := 67, numerator := 1772068022696834366439424000 }, { target := 68, numerator := 134587444761784888590336000 }, { target := 69, numerator := 157018685555415703355392000 }, { target := 70, numerator := 139073692920511051543347200 }, { target := 104, numerator := 119830049502817247297536000 }, { target := 105, numerator := 123253765202897740077465600 }, { target := 106, numerator := 119830049502817247297536000 }, { target := 107, numerator := 106135186702495276177817600 }, { target := 108, numerator := 4967811480816795023677849600 }, { target := 109, numerator := 1352367701531794648072192000 }, { target := 110, numerator := 123253765202897740077465600 }, { target := 111, numerator := 4967811480816795023677849600 }, { target := 112, numerator := 119830049502817247297536000 }, { target := 113, numerator := 119830049502817247297536000 }, { target := 114, numerator := 102711471002414783397888000 }, { target := 115, numerator := 119830049502817247297536000 }, { target := 116, numerator := 1352367701531794648072192000 }, { target := 117, numerator := 102711471002414783397888000 }, { target := 118, numerator := 119830049502817247297536000 }, { target := 119, numerator := 106135186702495276177817600 }, { target := 130, numerator := 1235489131080770929033216000 }, { target := 131, numerator := 1270788820540221527005593600 }, { target := 132, numerator := 1235489131080770929033216000 }, { target := 133, numerator := 1094290373242968537143705600 }, { target := 134, numerator := 51219849405662817657919897600 }, { target := 135, numerator := 13943377336482986199089152000 }, { target := 136, numerator := 1270788820540221527005593600 }, { target := 137, numerator := 51219849405662817657919897600 }, { target := 138, numerator := 1235489131080770929033216000 }, { target := 139, numerator := 1235489131080770929033216000 }, { target := 140, numerator := 1058990683783517939171328000 }, { target := 141, numerator := 1235489131080770929033216000 }, { target := 142, numerator := 13943377336482986199089152000 }, { target := 143, numerator := 1058990683783517939171328000 }, { target := 144, numerator := 1235489131080770929033216000 }, { target := 145, numerator := 1094290373242968537143705600 }, { target := 165, numerator := 148754544210393824231424000 }, { target := 166, numerator := 153004674044976504923750400 }, { target := 167, numerator := 148754544210393824231424000 }, { target := 168, numerator := 131754024872063101462118400 }, { target := 169, numerator := 6166938389979469684565606400 }, { target := 170, numerator := 1678801284660158873468928000 }, { target := 171, numerator := 153004674044976504923750400 }, { target := 172, numerator := 6166938389979469684565606400 }, { target := 173, numerator := 148754544210393824231424000 }, { target := 174, numerator := 148754544210393824231424000 }, { target := 175, numerator := 127503895037480420769792000 }, { target := 176, numerator := 148754544210393824231424000 }, { target := 177, numerator := 1678801284660158873468928000 }, { target := 178, numerator := 127503895037480420769792000 }, { target := 179, numerator := 148754544210393824231424000 }, { target := 180, numerator := 131754024872063101462118400 }]

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
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 226, numerator := 119830049502817247297536000 }, { target := 227, numerator := 123253765202897740077465600 }, { target := 228, numerator := 119830049502817247297536000 }, { target := 229, numerator := 106135186702495276177817600 }, { target := 230, numerator := 4967811480816795023677849600 }, { target := 231, numerator := 1352367701531794648072192000 }, { target := 232, numerator := 123253765202897740077465600 }, { target := 233, numerator := 4967811480816795023677849600 }, { target := 234, numerator := 119830049502817247297536000 }, { target := 235, numerator := 119830049502817247297536000 }, { target := 236, numerator := 102711471002414783397888000 }, { target := 237, numerator := 119830049502817247297536000 }, { target := 238, numerator := 1352367701531794648072192000 }, { target := 239, numerator := 102711471002414783397888000 }, { target := 240, numerator := 119830049502817247297536000 }, { target := 241, numerator := 106135186702495276177817600 }, { target := 261, numerator := 148754544210393824231424000 }, { target := 262, numerator := 153004674044976504923750400 }, { target := 263, numerator := 148754544210393824231424000 }, { target := 264, numerator := 131754024872063101462118400 }, { target := 265, numerator := 6166938389979469684565606400 }, { target := 266, numerator := 1678801284660158873468928000 }, { target := 267, numerator := 153004674044976504923750400 }, { target := 268, numerator := 6166938389979469684565606400 }, { target := 269, numerator := 148754544210393824231424000 }, { target := 270, numerator := 148754544210393824231424000 }, { target := 271, numerator := 127503895037480420769792000 }, { target := 272, numerator := 148754544210393824231424000 }, { target := 273, numerator := 1678801284660158873468928000 }, { target := 274, numerator := 127503895037480420769792000 }, { target := 275, numerator := 148754544210393824231424000 }, { target := 276, numerator := 131754024872063101462118400 }, { target := 371, numerator := 148754544210393824231424000 }, { target := 372, numerator := 153004674044976504923750400 }, { target := 373, numerator := 148754544210393824231424000 }, { target := 374, numerator := 131754024872063101462118400 }, { target := 375, numerator := 6166938389979469684565606400 }, { target := 376, numerator := 1678801284660158873468928000 }, { target := 377, numerator := 153004674044976504923750400 }, { target := 378, numerator := 6166938389979469684565606400 }, { target := 379, numerator := 148754544210393824231424000 }, { target := 380, numerator := 148754544210393824231424000 }, { target := 381, numerator := 127503895037480420769792000 }, { target := 382, numerator := 148754544210393824231424000 }, { target := 383, numerator := 1678801284660158873468928000 }, { target := 384, numerator := 127503895037480420769792000 }, { target := 385, numerator := 148754544210393824231424000 }, { target := 386, numerator := 131754024872063101462118400 }, { target := 397, numerator := 6371652977011868804579328000 }, { target := 398, numerator := 6553700204926493627567308800 }, { target := 399, numerator := 6371652977011868804579328000 }, { target := 400, numerator := 5643464065353369512627404800 }, { target := 401, numerator := 264150527704120618155560140800 }, { target := 402, numerator := 71908655026276805080252416000 }, { target := 403, numerator := 6553700204926493627567308800 }, { target := 404, numerator := 264150527704120618155560140800 }, { target := 405, numerator := 6371652977011868804579328000 }, { target := 406, numerator := 6371652977011868804579328000 }, { target := 407, numerator := 5461416837438744689639424000 }, { target := 408, numerator := 6371652977011868804579328000 }, { target := 409, numerator := 71908655026276805080252416000 }, { target := 410, numerator := 5461416837438744689639424000 }, { target := 411, numerator := 6371652977011868804579328000 }, { target := 412, numerator := 5643464065353369512627404800 }]

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
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 432, numerator := 148754544210393824231424000 }, { target := 433, numerator := 153004674044976504923750400 }, { target := 434, numerator := 148754544210393824231424000 }, { target := 435, numerator := 131754024872063101462118400 }, { target := 436, numerator := 6166938389979469684565606400 }, { target := 437, numerator := 1678801284660158873468928000 }, { target := 438, numerator := 153004674044976504923750400 }, { target := 439, numerator := 6166938389979469684565606400 }, { target := 440, numerator := 148754544210393824231424000 }, { target := 441, numerator := 148754544210393824231424000 }, { target := 442, numerator := 127503895037480420769792000 }, { target := 443, numerator := 148754544210393824231424000 }, { target := 444, numerator := 1678801284660158873468928000 }, { target := 445, numerator := 127503895037480420769792000 }, { target := 446, numerator := 148754544210393824231424000 }, { target := 447, numerator := 131754024872063101462118400 }, { target := 493, numerator := 1235489131080770929033216000 }, { target := 494, numerator := 1270788820540221527005593600 }, { target := 495, numerator := 1235489131080770929033216000 }, { target := 496, numerator := 1094290373242968537143705600 }, { target := 497, numerator := 51219849405662817657919897600 }, { target := 498, numerator := 13943377336482986199089152000 }, { target := 499, numerator := 1270788820540221527005593600 }, { target := 500, numerator := 51219849405662817657919897600 }, { target := 501, numerator := 1235489131080770929033216000 }, { target := 502, numerator := 1235489131080770929033216000 }, { target := 503, numerator := 1058990683783517939171328000 }, { target := 504, numerator := 1235489131080770929033216000 }, { target := 505, numerator := 13943377336482986199089152000 }, { target := 506, numerator := 1058990683783517939171328000 }, { target := 507, numerator := 1235489131080770929033216000 }, { target := 508, numerator := 1094290373242968537143705600 }, { target := 528, numerator := 6371652977011868804579328000 }, { target := 529, numerator := 6553700204926493627567308800 }, { target := 530, numerator := 6371652977011868804579328000 }, { target := 531, numerator := 5643464065353369512627404800 }, { target := 532, numerator := 264150527704120618155560140800 }, { target := 533, numerator := 71908655026276805080252416000 }, { target := 534, numerator := 6553700204926493627567308800 }, { target := 535, numerator := 264150527704120618155560140800 }, { target := 536, numerator := 6371652977011868804579328000 }, { target := 537, numerator := 6371652977011868804579328000 }, { target := 538, numerator := 5461416837438744689639424000 }, { target := 539, numerator := 6371652977011868804579328000 }, { target := 540, numerator := 71908655026276805080252416000 }, { target := 541, numerator := 5461416837438744689639424000 }, { target := 542, numerator := 6371652977011868804579328000 }, { target := 543, numerator := 5643464065353369512627404800 }, { target := 624, numerator := 132226261520350065983488000 }, { target := 625, numerator := 136004154706645782154444800 }, { target := 626, numerator := 132226261520350065983488000 }, { target := 627, numerator := 117114688775167201299660800 }, { target := 628, numerator := 5481723013315084164058316800 }, { target := 629, numerator := 1492267808586807887527936000 }, { target := 630, numerator := 136004154706645782154444800 }, { target := 631, numerator := 5481723013315084164058316800 }, { target := 632, numerator := 132226261520350065983488000 }, { target := 633, numerator := 132226261520350065983488000 }, { target := 634, numerator := 113336795588871485128704000 }, { target := 635, numerator := 132226261520350065983488000 }, { target := 636, numerator := 1492267808586807887527936000 }, { target := 637, numerator := 113336795588871485128704000 }, { target := 638, numerator := 132226261520350065983488000 }, { target := 639, numerator := 117114688775167201299660800 }]

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
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 606908573371999476672102400 }, { target := 6, numerator := 12162447810374869512508932096 }, { target := 7, numerator := 20416404408234062395249524736 }, { target := 8, numerator := 19591008748448143106975465472 }, { target := 9, numerator := 606908573371999476672102400 }, { target := 10, numerator := 19591008748448143106975465472 }, { target := 11, numerator := 13084948841900308717050527744 }, { target := 12, numerator := 631184916306879455738986496 }, { target := 13, numerator := 12162447810374869512508932096 }, { target := 14, numerator := 582632230437119497605218304 }, { target := 760, numerator := 148754544210393824231424000 }, { target := 761, numerator := 153004674044976504923750400 }, { target := 762, numerator := 148754544210393824231424000 }, { target := 763, numerator := 131754024872063101462118400 }, { target := 764, numerator := 6166938389979469684565606400 }, { target := 765, numerator := 1678801284660158873468928000 }, { target := 766, numerator := 153004674044976504923750400 }, { target := 767, numerator := 6166938389979469684565606400 }, { target := 768, numerator := 148754544210393824231424000 }, { target := 769, numerator := 148754544210393824231424000 }, { target := 770, numerator := 127503895037480420769792000 }, { target := 771, numerator := 148754544210393824231424000 }, { target := 772, numerator := 1678801284660158873468928000 }, { target := 773, numerator := 127503895037480420769792000 }, { target := 774, numerator := 148754544210393824231424000 }, { target := 775, numerator := 131754024872063101462118400 }, { target := 795, numerator := 148754544210393824231424000 }, { target := 796, numerator := 153004674044976504923750400 }, { target := 797, numerator := 148754544210393824231424000 }, { target := 798, numerator := 131754024872063101462118400 }, { target := 799, numerator := 6166938389979469684565606400 }, { target := 800, numerator := 1678801284660158873468928000 }, { target := 801, numerator := 153004674044976504923750400 }, { target := 802, numerator := 6166938389979469684565606400 }, { target := 803, numerator := 148754544210393824231424000 }, { target := 804, numerator := 148754544210393824231424000 }, { target := 805, numerator := 127503895037480420769792000 }, { target := 806, numerator := 148754544210393824231424000 }, { target := 807, numerator := 1678801284660158873468928000 }, { target := 808, numerator := 127503895037480420769792000 }, { target := 809, numerator := 148754544210393824231424000 }, { target := 810, numerator := 131754024872063101462118400 }, { target := 891, numerator := 157018685555415703355392000 }, { target := 892, numerator := 161504933714141866308403200 }, { target := 893, numerator := 157018685555415703355392000 }, { target := 894, numerator := 139073692920511051543347200 }, { target := 895, numerator := 6509546078311662444819251200 }, { target := 896, numerator := 1772068022696834366439424000 }, { target := 897, numerator := 161504933714141866308403200 }, { target := 898, numerator := 6509546078311662444819251200 }, { target := 899, numerator := 157018685555415703355392000 }, { target := 900, numerator := 157018685555415703355392000 }, { target := 901, numerator := 134587444761784888590336000 }, { target := 902, numerator := 157018685555415703355392000 }, { target := 903, numerator := 1772068022696834366439424000 }, { target := 904, numerator := 134587444761784888590336000 }, { target := 905, numerator := 157018685555415703355392000 }, { target := 906, numerator := 139073692920511051543347200 }]

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

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 10348405015901225735484866560 }, { target := 2, numerator := 9458635612664858662901121024 }, { target := 3, numerator := 10348405015901225735484866560 }, { target := 4, numerator := 9458635612664858662901121024 }, { target := 90, numerator := 10348405015901225735484866560 }, { target := 91, numerator := 9458635612664858662901121024 }, { target := 92, numerator := 10348405015901225735484866560 }, { target := 93, numerator := 9458635612664858662901121024 }, { target := 94, numerator := 2171175349938226042031308800 }, { target := 95, numerator := 43510354012762049882307428352 }, { target := 96, numerator := 73038338771921924053933228032 }, { target := 97, numerator := 70085540296005936636770648064 }, { target := 98, numerator := 2171175349938226042031308800 }, { target := 99, numerator := 70085540296005936636770648064 }, { target := 100, numerator := 46810540544668153466195017728 }, { target := 101, numerator := 2258022363935755083712561152 }, { target := 102, numerator := 43510354012762049882307428352 }, { target := 103, numerator := 2084328335940697000350056448 }, { target := 216, numerator := 606908371610736170473881600 }, { target := 217, numerator := 12162443767079152856296587264 }, { target := 218, numerator := 20416397620985164774741377024 }, { target := 219, numerator := 19591002235594563582896898048 }, { target := 220, numerator := 606908371610736170473881600 }, { target := 221, numerator := 19591002235594563582896898048 }, { target := 222, numerator := 13084944491927471835416887296 }, { target := 223, numerator := 631184706475165617292836864 }, { target := 224, numerator := 12162443767079152856296587264 }, { target := 225, numerator := 582632036746306723654926336 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2
