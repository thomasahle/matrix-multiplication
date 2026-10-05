import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 200, numerator := 7217132098215396644214538240 }, { target := 202, numerator := 261551256118508961476462510080 }, { target := 205, numerator := 261551352237574800549294899200 }, { target := 212, numerator := 7217035979149557571382149120 }, { target := 296, numerator := 7423335872450122262620667904 }, { target := 298, numerator := 269024149150466360375790010368 }, { target := 301, numerator := 269024248015791223422131896320 }, { target := 308, numerator := 7423237007125259216278781952 }, { target := 331, numerator := 7217132098215396644214538240 }, { target := 333, numerator := 261551256118508961476462510080 }, { target := 336, numerator := 261551352237574800549294899200 }, { target := 343, numerator := 7217035979149557571382149120 }, { target := 347, numerator := 3947710684058073403962163200 }, { target := 350, numerator := 13381673057101326666904371200 }, { target := 352, numerator := 3947710684058073403962163200 }, { target := 467, numerator := 6392317001276494170590019584 }, { target := 469, numerator := 231659683990679365879152508928 }, { target := 472, numerator := 231659769124709109057946910720 }, { target := 479, numerator := 6392231867246750991795617792 }, { target := 563, numerator := 299201676414586872307294142464 }, { target := 565, numerator := 10843167789370185802924202917888 }, { target := 568, numerator := 10843171774192029588486482821120 }, { target := 575, numerator := 299197691592743086745014239232 }, { target := 598, numerator := 81450490822716619270421217280 }, { target := 600, numerator := 2951792747623172565234362613760 }, { target := 603, numerator := 2951793832395487034770613862400 }, { target := 610, numerator := 81449406050402149734169968640 }, { target := 614, numerator := 79112122108523791015401750528 }, { target := 617, numerator := 268168728064310586404763598848 }, { target := 619, numerator := 79112122108523791015401750528 }, { target := 710, numerator := 132800987411713589309287170048 }, { target := 713, numerator := 450159481640888629074663047168 }, { target := 715, numerator := 132800987411713589309287170048 }, { target := 736, numerator := 127432100881394609479898628096 }, { target := 739, numerator := 431960406283230824807673102336 }, { target := 741, numerator := 127432100881394609479898628096 }, { target := 746, numerator := 10348405015901225735484866560 }, { target := 748, numerator := 10348405015901225735484866560 }, { target := 881, numerator := 3947710684058073403962163200 }, { target := 884, numerator := 13381673057101326666904371200 }, { target := 886, numerator := 3947710684058073403962163200 }, { target := 977, numerator := 127432100881394609479898628096 }, { target := 980, numerator := 431960406283230824807673102336 }, { target := 982, numerator := 127432100881394609479898628096 }, { target := 1003, numerator := 85112642348292062589424238592 }, { target := 1006, numerator := 288508871111104602938458243072 }, { target := 1008, numerator := 85112642348292062589424238592 }, { target := 1013, numerator := 9458635612664858662901121024 }, { target := 1015, numerator := 9458635612664858662901121024 }, { target := 1052, numerator := 4105619111420396340120649728 }, { target := 1055, numerator := 13916939979385379733580546048 }, { target := 1057, numerator := 4105619111420396340120649728 }, { target := 1078, numerator := 79112122108523791015401750528 }, { target := 1081, numerator := 268168728064310586404763598848 }, { target := 1083, numerator := 79112122108523791015401750528 }, { target := 1088, numerator := 10348405015901225735484866560 }, { target := 1090, numerator := 10348405015901225735484866560 }, { target := 1092, numerator := 3789802256695750467803676672 }, { target := 1095, numerator := 12846406134817273600228196352 }, { target := 1097, numerator := 3789802256695750467803676672 }, { target := 1102, numerator := 9458635612664858662901121024 }, { target := 1104, numerator := 9458635612664858662901121024 }]

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
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 56866239124626277505433600 }, { target := 72, numerator := 8398845926608532068211097600 }, { target := 74, numerator := 87539766483237644003180544000 }, { target := 82, numerator := 8398845926608532068211097600 }, { target := 89, numerator := 56866239124626277505433600 }, { target := 146, numerator := 1516433043323367400144896000 }, { target := 147, numerator := 223969224709560855152295936000 }, { target := 149, numerator := 2334393772886337173418147840000 }, { target := 157, numerator := 223969224709560855152295936000 }, { target := 164, numerator := 1516433043323367400144896000 }, { target := 181, numerator := 1450089097677970076388556800 }, { target := 182, numerator := 214170571128517567739382988800 }, { target := 184, numerator := 2232264045322559922081103872000 }, { target := 192, numerator := 214170571128517567739382988800 }, { target := 199, numerator := 1450089097677970076388556800 }, { target := 242, numerator := 47388532603855231254528000 }, { target := 243, numerator := 6999038272173776723509248000 }, { target := 245, numerator := 72949805402698036669317120000 }, { target := 253, numerator := 6999038272173776723509248000 }, { target := 260, numerator := 47388532603855231254528000 }, { target := 659, numerator := 7423335872450122262620667904 }, { target := 661, numerator := 269024149150466360375790010368 }, { target := 664, numerator := 269024248015791223422131896320 }, { target := 671, numerator := 7423237007125259216278781952 }, { target := 694, numerator := 299201676414586872307294142464 }, { target := 696, numerator := 10843167789370185802924202917888 }, { target := 699, numerator := 10843171774192029588486482821120 }, { target := 706, numerator := 299197691592743086745014239232 }, { target := 720, numerator := 7217132098215396644214538240 }, { target := 722, numerator := 261551256118508961476462510080 }, { target := 725, numerator := 261551352237574800549294899200 }, { target := 732, numerator := 7217035979149557571382149120 }, { target := 830, numerator := 7217132098215396644214538240 }, { target := 832, numerator := 261551256118508961476462510080 }, { target := 835, numerator := 261551352237574800549294899200 }, { target := 842, numerator := 7217035979149557571382149120 }, { target := 865, numerator := 6186113227041768552183889920 }, { target := 867, numerator := 224186790958721966979825008640 }, { target := 870, numerator := 224186873346492686185109913600 }, { target := 877, numerator := 6186030839271049346898984960 }, { target := 926, numerator := 7217132098215396644214538240 }, { target := 928, numerator := 261551256118508961476462510080 }, { target := 931, numerator := 261551352237574800549294899200 }, { target := 938, numerator := 7217035979149557571382149120 }, { target := 961, numerator := 81450490822716619270421217280 }, { target := 963, numerator := 2951792747623172565234362613760 }, { target := 966, numerator := 2951793832395487034770613862400 }, { target := 973, numerator := 81449406050402149734169968640 }, { target := 987, numerator := 6186113227041768552183889920 }, { target := 989, numerator := 224186790958721966979825008640 }, { target := 992, numerator := 224186873346492686185109913600 }, { target := 999, numerator := 6186030839271049346898984960 }, { target := 1036, numerator := 7217132098215396644214538240 }, { target := 1038, numerator := 261551256118508961476462510080 }, { target := 1041, numerator := 261551352237574800549294899200 }, { target := 1048, numerator := 7217035979149557571382149120 }, { target := 1062, numerator := 6392317001276494170590019584 }, { target := 1064, numerator := 231659683990679365879152508928 }, { target := 1067, numerator := 231659769124709109057946910720 }, { target := 1074, numerator := 6392231867246750991795617792 }]

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
    Slot4.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 277, numerator := 1487999923761054261392179200 }, { target := 278, numerator := 219769801746256589118190387200 }, { target := 280, numerator := 2290623889644718351416557568000 }, { target := 288, numerator := 219769801746256589118190387200 }, { target := 295, numerator := 1487999923761054261392179200 }, { target := 312, numerator := 47388532603855231254528000 }, { target := 313, numerator := 6999038272173776723509248000 }, { target := 315, numerator := 72949805402698036669317120000 }, { target := 323, numerator := 6999038272173776723509248000 }, { target := 330, numerator := 47388532603855231254528000 }, { target := 413, numerator := 1450089097677970076388556800 }, { target := 414, numerator := 214170571128517567739382988800 }, { target := 416, numerator := 2232264045322559922081103872000 }, { target := 424, numerator := 214170571128517567739382988800 }, { target := 431, numerator := 1450089097677970076388556800 }, { target := 448, numerator := 824560467307081023828787200 }, { target := 449, numerator := 121783265935823714989060915200 }, { target := 451, numerator := 1269326614006945838046117888000 }, { target := 459, numerator := 121783265935823714989060915200 }, { target := 466, numerator := 824560467307081023828787200 }, { target := 509, numerator := 1487999923761054261392179200 }, { target := 510, numerator := 219769801746256589118190387200 }, { target := 512, numerator := 2290623889644718351416557568000 }, { target := 520, numerator := 219769801746256589118190387200 }, { target := 527, numerator := 1487999923761054261392179200 }, { target := 544, numerator := 23229858682409834360969625600 }, { target := 545, numerator := 3430928561019585349864233369600 }, { target := 547, numerator := 35759994608402577575299252224000 }, { target := 555, numerator := 3430928561019585349864233369600 }, { target := 562, numerator := 23229858682409834360969625600 }, { target := 579, numerator := 909859825994020440086937600 }, { target := 580, numerator := 134381534825736513091377561600 }, { target := 582, numerator := 1400636263731802304050888704000 }, { target := 590, numerator := 134381534825736513091377561600 }, { target := 597, numerator := 909859825994020440086937600 }, { target := 640, numerator := 1516433043323367400144896000 }, { target := 641, numerator := 223969224709560855152295936000 }, { target := 643, numerator := 2334393772886337173418147840000 }, { target := 651, numerator := 223969224709560855152295936000 }, { target := 658, numerator := 1516433043323367400144896000 }, { target := 675, numerator := 1450089097677970076388556800 }, { target := 676, numerator := 214170571128517567739382988800 }, { target := 678, numerator := 2232264045322559922081103872000 }, { target := 686, numerator := 214170571128517567739382988800 }, { target := 693, numerator := 1450089097677970076388556800 }, { target := 776, numerator := 47388532603855231254528000 }, { target := 777, numerator := 6999038272173776723509248000 }, { target := 779, numerator := 72949805402698036669317120000 }, { target := 787, numerator := 6999038272173776723509248000 }, { target := 794, numerator := 47388532603855231254528000 }, { target := 811, numerator := 909859825994020440086937600 }, { target := 812, numerator := 134381534825736513091377561600 }, { target := 814, numerator := 1400636263731802304050888704000 }, { target := 822, numerator := 134381534825736513091377561600 }, { target := 829, numerator := 909859825994020440086937600 }, { target := 846, numerator := 47388532603855231254528000 }, { target := 847, numerator := 6999038272173776723509248000 }, { target := 849, numerator := 72949805402698036669317120000 }, { target := 857, numerator := 6999038272173776723509248000 }, { target := 864, numerator := 47388532603855231254528000 }]

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
    Slot4.Left16.expected,
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
    Slot5.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 256421290286352909641711616 }, { target := 30, numerator := 21562271902118474435455352832 }, { target := 35, numerator := 21562266700136645649361797120 }, { target := 43, numerator := 256426492268181695735267328 }, { target := 55, numerator := 251079180072053890690842624 }, { target := 56, numerator := 21113057904157672884716699648 }, { target := 61, numerator := 21113052810550465531666759680 }, { target := 69, numerator := 251084273679261243740782592 }, { target := 104, numerator := 197658077929063701182152704 }, { target := 105, numerator := 16620917924549657377330167808 }, { target := 110, numerator := 16620913914688664354716385280 }, { target := 118, numerator := 197662087790056723795935232 }, { target := 130, numerator := 6212874179229759039860637696 }, { target := 131, numerator := 522435879628412203509053652992 }, { target := 136, numerator := 522435753588727476879328542720 }, { target := 144, numerator := 6213000218914485669585747968 }, { target := 165, numerator := 197658077929063701182152704 }, { target := 166, numerator := 16620917924549657377330167808 }, { target := 171, numerator := 16620913914688664354716385280 }, { target := 179, numerator := 197662087790056723795935232 }, { target := 226, numerator := 197658077929063701182152704 }, { target := 227, numerator := 16620917924549657377330167808 }, { target := 232, numerator := 16620913914688664354716385280 }, { target := 240, numerator := 197662087790056723795935232 }, { target := 261, numerator := 203000188143362720133021696 }, { target := 262, numerator := 17070131922510458928068820992 }, { target := 267, numerator := 17070127804274844472411422720 }, { target := 275, numerator := 203004306378977175790419968 }, { target := 371, numerator := 203000188143362720133021696 }, { target := 372, numerator := 17070131922510458928068820992 }, { target := 377, numerator := 17070127804274844472411422720 }, { target := 385, numerator := 203004306378977175790419968 }, { target := 397, numerator := 3434976867794269185408761856 }, { target := 398, numerator := 288844600688795397124953997312 }, { target := 403, numerator := 288844531003913815677909073920 }, { target := 411, numerator := 3435046552675850632453685248 }, { target := 432, numerator := 186973857500465663280414720 }, { target := 433, numerator := 15722489928628054275852861440 }, { target := 438, numerator := 15722486135516304119326310400 }, { target := 446, numerator := 186977650612215819806965760 }, { target := 493, numerator := 6212874179229759039860637696 }, { target := 494, numerator := 522435879628412203509053652992 }, { target := 499, numerator := 522435753588727476879328542720 }, { target := 507, numerator := 6213000218914485669585747968 }, { target := 528, numerator := 3434976867794269185408761856 }, { target := 529, numerator := 288844600688795397124953997312 }, { target := 534, numerator := 288844531003913815677909073920 }, { target := 542, numerator := 3435046552675850632453685248 }, { target := 907, numerator := 1459566804198741122639462400 }, { target := 908, numerator := 215570378782952323084084838400 }, { target := 910, numerator := 2246854006403099529414967296000 }, { target := 918, numerator := 215570378782952323084084838400 }, { target := 925, numerator := 1459566804198741122639462400 }, { target := 942, numerator := 824560467307081023828787200 }, { target := 943, numerator := 121783265935823714989060915200 }, { target := 945, numerator := 1269326614006945838046117888000 }, { target := 953, numerator := 121783265935823714989060915200 }, { target := 960, numerator := 824560467307081023828787200 }, { target := 1017, numerator := 56866239124626277505433600 }, { target := 1018, numerator := 8398845926608532068211097600 }, { target := 1020, numerator := 87539766483237644003180544000 }, { target := 1028, numerator := 8398845926608532068211097600 }, { target := 1035, numerator := 56866239124626277505433600 }]

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
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
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
    Slot10.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 112908049834579717903089664 }, { target := 72, numerator := 11838205387906721591167287296 }, { target := 74, numerator := 127604021809269725775003648000 }, { target := 82, numerator := 11838214418383393956177117184 }, { target := 89, numerator := 112908049834579717903089664 }, { target := 146, numerator := 11838205387906721591167287296 }, { target := 147, numerator := 1241214483923739562355294470144 }, { target := 149, numerator := 13379051544280767904006275072000 }, { target := 157, numerator := 1241215430752931588806673432576 }, { target := 164, numerator := 11838205387906721591167287296 }, { target := 200, numerator := 3195063169011828530431918080 }, { target := 202, numerator := 111819244954793846602192650240 }, { target := 205, numerator := 111819299797896222863555297280 }, { target := 212, numerator := 3195035747460640399750594560 }, { target := 242, numerator := 127604021809269725775003648000 }, { target := 243, numerator := 13379051544280767904006275072000 }, { target := 245, numerator := 144212803301060521582657536000000 }, { target := 253, numerator := 13379061750153103285092876288000 }, { target := 260, numerator := 127604021809269725775003648000 }, { target := 296, numerator := 267519875067218431608040194048 }, { target := 298, numerator := 9362528644361334631332518559744 }, { target := 301, numerator := 9362533236326851398802046189568 }, { target := 308, numerator := 267517579084460047873276379136 }, { target := 347, numerator := 10008671093676592501327134720 }, { target := 350, numerator := 34220324584904699535691874304 }, { target := 352, numerator := 10008667860859923785777676288 }, { target := 624, numerator := 256421290286352909641711616 }, { target := 625, numerator := 21562271902118474435455352832 }, { target := 630, numerator := 21562266700136645649361797120 }, { target := 638, numerator := 256426492268181695735267328 }, { target := 640, numerator := 11838214418383393956177117184 }, { target := 641, numerator := 1241215430752931588806673432576 }, { target := 643, numerator := 13379061750153103285092876288000 }, { target := 651, numerator := 1241216377582845880048291938304 }, { target := 658, numerator := 11838214418383393956177117184 }, { target := 659, numerator := 267519971882424805381946474496 }, { target := 661, numerator := 9362532032652177158291155058688 }, { target := 664, numerator := 9362536624619355754023182401536 }, { target := 671, numerator := 267517675898835507515932803072 }, { target := 710, numerator := 96944719703087669363699875840 }, { target := 713, numerator := 331460564942355455901421273088 }, { target := 715, numerator := 96944688389789143837637083136 }, { target := 760, numerator := 197658077929063701182152704 }, { target := 761, numerator := 16620917924549657377330167808 }, { target := 766, numerator := 16620913914688664354716385280 }, { target := 774, numerator := 197662087790056723795935232 }, { target := 795, numerator := 186973857500465663280414720 }, { target := 796, numerator := 15722489928628054275852861440 }, { target := 801, numerator := 15722486135516304119326310400 }, { target := 809, numerator := 186977650612215819806965760 }, { target := 891, numerator := 251079180072053890690842624 }, { target := 892, numerator := 21113057904157672884716699648 }, { target := 897, numerator := 21113052810550465531666759680 }, { target := 905, numerator := 251084273679261243740782592 }, { target := 1036, numerator := 3194966353805454756525637632 }, { target := 1038, numerator := 111815856663951319643556151296 }, { target := 1041, numerator := 111815911505391867642419085312 }, { target := 1048, numerator := 3194938933085180757094170624 }, { target := 1052, numerator := 10008671093676592501327134720 }, { target := 1055, numerator := 34220324584904699535691874304 }, { target := 1057, numerator := 10008667860859923785777676288 }]

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
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 11259754980386166563993026560 }, { target := 7, numerator := 109062809665973628034162360320 }, { target := 12, numerator := 11259754980386166563993026560 }, { target := 29, numerator := 3201557199843153385168568320 }, { target := 30, numerator := 268063614650688387769845153792 }, { target := 35, numerator := 268063711662673636287194333184 }, { target := 43, numerator := 3201460187857904867819388928 }, { target := 94, numerator := 38497865158017786977653358592 }, { target := 96, numerator := 372893135560149887889098932224 }, { target := 101, numerator := 38497865158017786977653358592 }, { target := 104, numerator := 112046519842913346290408488960 }, { target := 105, numerator := 9381558174126296693591324491776 }, { target := 110, numerator := 9381561569303909225686055780352 }, { target := 118, numerator := 112043124665300814195677200384 }, { target := 200, numerator := 267332834553857288775401472 }, { target := 201, numerator := 261763400500651928592580608 }, { target := 202, numerator := 206069059968598326764371968 }, { target := 203, numerator := 6477251803877833892620664832 }, { target := 204, numerator := 206069059968598326764371968 }, { target := 205, numerator := 206069059968598326764371968 }, { target := 206, numerator := 211638494021803686947192832 }, { target := 207, numerator := 211638494021803686947192832 }, { target := 208, numerator := 3581146096211046597553815552 }, { target := 209, numerator := 194930191862187606398730240 }, { target := 210, numerator := 6477251803877833892620664832 }, { target := 211, numerator := 3581146096211046597553815552 }, { target := 212, numerator := 267332834553857288775401472 }, { target := 213, numerator := 206069059968598326764371968 }, { target := 214, numerator := 194930191862187606398730240 }, { target := 215, numerator := 261763400500651928592580608 }, { target := 216, numerator := 11259751343467414258999885824 }, { target := 218, numerator := 109062774438512786817341718528 }, { target := 223, numerator := 11259751343467414258999885824 }, { target := 226, numerator := 112046574797485442828725125120 }, { target := 227, numerator := 9381562775425076706523188559872 }, { target := 232, numerator := 9381566170604354444580140089344 }, { target := 240, numerator := 112043179618207704771773595648 }, { target := 296, numerator := 22479815387315005262496006144 }, { target := 297, numerator := 22011485900079275986194006016 }, { target := 298, numerator := 17328191027721983223174004736 }, { target := 299, numerator := 544667193655153148339226148864 }, { target := 300, numerator := 17328191027721983223174004736 }, { target := 301, numerator := 17328191027721983223174004736 }, { target := 302, numerator := 17796520514957712499476004864 }, { target := 303, numerator := 17796520514957712499476004864 }, { target := 304, numerator := 301135860292573924662186082304 }, { target := 305, numerator := 16391532053250524670570004480 }, { target := 306, numerator := 544667193655153148339226148864 }, { target := 307, numerator := 301135860292573924662186082304 }, { target := 308, numerator := 22479815387315005262496006144 }, { target := 309, numerator := 17328191027721983223174004736 }, { target := 310, numerator := 16391532053250524670570004480 }, { target := 311, numerator := 22011485900079275986194006016 }, { target := 624, numerator := 3201529722557105116010250240 }, { target := 625, numerator := 268061314001298381303913119744 }, { target := 630, numerator := 268061411012451026840152178688 }, { target := 638, numerator := 3201432711404459579771191296 }, { target := 1017, numerator := 112908049834579717903089664 }, { target := 1018, numerator := 11838205387906721591167287296 }, { target := 1020, numerator := 127604021809269725775003648000 }, { target := 1028, numerator := 11838214418383393956177117184 }, { target := 1035, numerator := 112908049834579717903089664 }]

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
    Slot15.Left6.expected,
    Slot15.Left14.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 56739869704349330222088192 }, { target := 72, numerator := 1513063192115982139255685120 }, { target := 73, numerator := 1446866677460907920663248896 }, { target := 74, numerator := 47283224753624441851740160 }, { target := 75, numerator := 1484693257263807474144641024 }, { target := 76, numerator := 47283224753624441851740160 }, { target := 77, numerator := 1446866677460907920663248896 }, { target := 78, numerator := 822728110713065288220278784 }, { target := 79, numerator := 1484693257263807474144641024 }, { target := 80, numerator := 23178236774226701395723026432 }, { target := 81, numerator := 907837915269589283553411072 }, { target := 82, numerator := 1513063192115982139255685120 }, { target := 83, numerator := 1446866677460907920663248896 }, { target := 84, numerator := 47283224753624441851740160 }, { target := 85, numerator := 907837915269589283553411072 }, { target := 86, numerator := 47283224753624441851740160 }, { target := 87, numerator := 1456323322411632809033596928 }, { target := 88, numerator := 822728110713065288220278784 }, { target := 89, numerator := 56739869704349330222088192 }, { target := 659, numerator := 22479809963972247591887831040 }, { target := 660, numerator := 22011480589722825767056834560 }, { target := 661, numerator := 17328186847228607518746869760 }, { target := 662, numerator := 544667062252077582278448906240 }, { target := 663, numerator := 17328186847228607518746869760 }, { target := 664, numerator := 17328186847228607518746869760 }, { target := 665, numerator := 17796516221478029343577866240 }, { target := 666, numerator := 17796516221478029343577866240 }, { target := 667, numerator := 301135787642378233366330736640 }, { target := 668, numerator := 16391528098729763869084876800 }, { target := 669, numerator := 544667062252077582278448906240 }, { target := 670, numerator := 301135787642378233366330736640 }, { target := 671, numerator := 22479809963972247591887831040 }, { target := 672, numerator := 17328186847228607518746869760 }, { target := 673, numerator := 16391528098729763869084876800 }, { target := 674, numerator := 22011480589722825767056834560 }, { target := 1036, numerator := 267338257896614959383576576 }, { target := 1037, numerator := 261768710857102147729752064 }, { target := 1038, numerator := 206073240461974031191506944 }, { target := 1039, numerator := 6477383206953399953397907456 }, { target := 1040, numerator := 206073240461974031191506944 }, { target := 1041, numerator := 206073240461974031191506944 }, { target := 1042, numerator := 211642787501486842845331456 }, { target := 1043, numerator := 211642787501486842845331456 }, { target := 1044, numerator := 3581218746406737893409161216 }, { target := 1045, numerator := 194934146382948407883857920 }, { target := 1046, numerator := 6477383206953399953397907456 }, { target := 1047, numerator := 3581218746406737893409161216 }, { target := 1048, numerator := 267338257896614959383576576 }, { target := 1049, numerator := 206073240461974031191506944 }, { target := 1050, numerator := 194934146382948407883857920 }, { target := 1051, numerator := 261768710857102147729752064 }]

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
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 8380181824549401996948406272 }, { target := 147, numerator := 223471515321317386585290833920 }, { target := 148, numerator := 213694636526009750922184359936 }, { target := 149, numerator := 6983484853791168330790338560 }, { target := 150, numerator := 219281424409042685586816630784 }, { target := 151, numerator := 6983484853791168330790338560 }, { target := 152, numerator := 213694636526009750922184359936 }, { target := 153, numerator := 121512636455966328955751890944 }, { target := 154, numerator := 219281424409042685586816630784 }, { target := 155, numerator := 3423304275328430715753423962112 }, { target := 156, numerator := 134082909192790431951174500352 }, { target := 157, numerator := 223471515321317386585290833920 }, { target := 158, numerator := 213694636526009750922184359936 }, { target := 159, numerator := 6983484853791168330790338560 }, { target := 160, numerator := 134082909192790431951174500352 }, { target := 161, numerator := 6983484853791168330790338560 }, { target := 162, numerator := 215091333496767984588342427648 }, { target := 163, numerator := 121512636455966328955751890944 }, { target := 164, numerator := 8380181824549401996948406272 }, { target := 242, numerator := 87345233668830449238729031680 }, { target := 243, numerator := 2329206231168811979699440844800 }, { target := 244, numerator := 2227303458555176455587590307840 }, { target := 245, numerator := 72787694724025374365607526400 }, { target := 246, numerator := 2285533614334396755080076328960 }, { target := 247, numerator := 72787694724025374365607526400 }, { target := 248, numerator := 2227303458555176455587590307840 }, { target := 249, numerator := 1266505888198041513961570959360 }, { target := 250, numerator := 2285533614334396755080076328960 }, { target := 251, numerator := 35680527953717238514020809441280 }, { target := 252, numerator := 1397523738701287187819664506880 }, { target := 253, numerator := 2329206231168811979699440844800 }, { target := 254, numerator := 2227303458555176455587590307840 }, { target := 255, numerator := 72787694724025374365607526400 }, { target := 256, numerator := 1397523738701287187819664506880 }, { target := 257, numerator := 72787694724025374365607526400 }, { target := 258, numerator := 2241860997499981530460711813120 }, { target := 259, numerator := 1266505888198041513961570959360 }, { target := 260, numerator := 87345233668830449238729031680 }, { target := 640, numerator := 8380181824549401996948406272 }, { target := 641, numerator := 223471515321317386585290833920 }, { target := 642, numerator := 213694636526009750922184359936 }, { target := 643, numerator := 6983484853791168330790338560 }, { target := 644, numerator := 219281424409042685586816630784 }, { target := 645, numerator := 6983484853791168330790338560 }, { target := 646, numerator := 213694636526009750922184359936 }, { target := 647, numerator := 121512636455966328955751890944 }, { target := 648, numerator := 219281424409042685586816630784 }, { target := 649, numerator := 3423304275328430715753423962112 }, { target := 650, numerator := 134082909192790431951174500352 }, { target := 651, numerator := 223471515321317386585290833920 }, { target := 652, numerator := 213694636526009750922184359936 }, { target := 653, numerator := 6983484853791168330790338560 }, { target := 654, numerator := 134082909192790431951174500352 }, { target := 655, numerator := 6983484853791168330790338560 }, { target := 656, numerator := 215091333496767984588342427648 }, { target := 657, numerator := 121512636455966328955751890944 }, { target := 658, numerator := 8380181824549401996948406272 }]

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
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 7180773750113555855074918400 }, { target := 30, numerator := 7385938714402514593791344640 }, { target := 31, numerator := 7180773750113555855074918400 }, { target := 32, numerator := 6360113892957720900209213440 }, { target := 33, numerator := 297694363183279129877534474240 }, { target := 34, numerator := 81040160894138701792988364800 }, { target := 35, numerator := 7385938714402514593791344640 }, { target := 36, numerator := 297694363183279129877534474240 }, { target := 37, numerator := 7180773750113555855074918400 }, { target := 38, numerator := 7180773750113555855074918400 }, { target := 39, numerator := 6154948928668762161492787200 }, { target := 40, numerator := 7180773750113555855074918400 }, { target := 41, numerator := 81040160894138701792988364800 }, { target := 42, numerator := 6154948928668762161492787200 }, { target := 43, numerator := 7180773750113555855074918400 }, { target := 44, numerator := 6360113892957720900209213440 }, { target := 104, numerator := 260233617548642417589931212800 }, { target := 105, numerator := 267668863764317915235357818880 }, { target := 106, numerator := 260233617548642417589931212800 }, { target := 107, numerator := 230492632685940427008224788480 }, { target := 108, numerator := 10788542258945147083514005422080 }, { target := 109, numerator := 2936922255191821569943509401600 }, { target := 110, numerator := 267668863764317915235357818880 }, { target := 111, numerator := 10788542258945147083514005422080 }, { target := 112, numerator := 260233617548642417589931212800 }, { target := 113, numerator := 260233617548642417589931212800 }, { target := 114, numerator := 223057386470264929362798182400 }, { target := 115, numerator := 260233617548642417589931212800 }, { target := 116, numerator := 2936922255191821569943509401600 }, { target := 117, numerator := 223057386470264929362798182400 }, { target := 118, numerator := 260233617548642417589931212800 }, { target := 119, numerator := 230492632685940427008224788480 }, { target := 1017, numerator := 56739869704349330222088192 }, { target := 1018, numerator := 1513063192115982139255685120 }, { target := 1019, numerator := 1446866677460907920663248896 }, { target := 1020, numerator := 47283224753624441851740160 }, { target := 1021, numerator := 1484693257263807474144641024 }, { target := 1022, numerator := 47283224753624441851740160 }, { target := 1023, numerator := 1446866677460907920663248896 }, { target := 1024, numerator := 822728110713065288220278784 }, { target := 1025, numerator := 1484693257263807474144641024 }, { target := 1026, numerator := 23178236774226701395723026432 }, { target := 1027, numerator := 907837915269589283553411072 }, { target := 1028, numerator := 1513063192115982139255685120 }, { target := 1029, numerator := 1446866677460907920663248896 }, { target := 1030, numerator := 47283224753624441851740160 }, { target := 1031, numerator := 907837915269589283553411072 }, { target := 1032, numerator := 47283224753624441851740160 }, { target := 1033, numerator := 1456323322411632809033596928 }, { target := 1034, numerator := 822728110713065288220278784 }, { target := 1035, numerator := 56739869704349330222088192 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 3947710684058073403962163200 }, { target := 6, numerator := 79112122108523791015401750528 }, { target := 7, numerator := 132800987411713589309287170048 }, { target := 8, numerator := 127432100881394609479898628096 }, { target := 9, numerator := 3947710684058073403962163200 }, { target := 10, numerator := 127432100881394609479898628096 }, { target := 11, numerator := 85112642348292062589424238592 }, { target := 12, numerator := 4105619111420396340120649728 }, { target := 13, numerator := 79112122108523791015401750528 }, { target := 14, numerator := 3789802256695750467803676672 }, { target := 94, numerator := 13381673057101326666904371200 }, { target := 95, numerator := 268168728064310586404763598848 }, { target := 96, numerator := 450159481640888629074663047168 }, { target := 97, numerator := 431960406283230824807673102336 }, { target := 98, numerator := 13381673057101326666904371200 }, { target := 99, numerator := 431960406283230824807673102336 }, { target := 100, numerator := 288508871111104602938458243072 }, { target := 101, numerator := 13916939979385379733580546048 }, { target := 102, numerator := 268168728064310586404763598848 }, { target := 103, numerator := 12846406134817273600228196352 }, { target := 216, numerator := 3947710684058073403962163200 }, { target := 217, numerator := 79112122108523791015401750528 }, { target := 218, numerator := 132800987411713589309287170048 }, { target := 219, numerator := 127432100881394609479898628096 }, { target := 220, numerator := 3947710684058073403962163200 }, { target := 221, numerator := 127432100881394609479898628096 }, { target := 222, numerator := 85112642348292062589424238592 }, { target := 223, numerator := 4105619111420396340120649728 }, { target := 224, numerator := 79112122108523791015401750528 }, { target := 225, numerator := 3789802256695750467803676672 }, { target := 226, numerator := 260233713183481224727887872000 }, { target := 227, numerator := 267668962131580688291541811200 }, { target := 228, numerator := 260233713183481224727887872000 }, { target := 229, numerator := 230492717391083370473272115200 }, { target := 230, numerator := 10788546223692321630861865779200 }, { target := 231, numerator := 2936923334499288107643305984000 }, { target := 232, numerator := 267668962131580688291541811200 }, { target := 233, numerator := 10788546223692321630861865779200 }, { target := 234, numerator := 260233713183481224727887872000 }, { target := 235, numerator := 260233713183481224727887872000 }, { target := 236, numerator := 223057468442983906909618176000 }, { target := 237, numerator := 260233713183481224727887872000 }, { target := 238, numerator := 2936923334499288107643305984000 }, { target := 239, numerator := 223057468442983906909618176000 }, { target := 240, numerator := 260233713183481224727887872000 }, { target := 241, numerator := 230492717391083370473272115200 }, { target := 624, numerator := 7180678115274748717118259200 }, { target := 625, numerator := 7385840347139741537607352320 }, { target := 626, numerator := 7180678115274748717118259200 }, { target := 627, numerator := 6360029187814777435161886720 }, { target := 628, numerator := 297690398436104582529674117120 }, { target := 629, numerator := 81039081586672164093191782400 }, { target := 630, numerator := 7385840347139741537607352320 }, { target := 631, numerator := 297690398436104582529674117120 }, { target := 632, numerator := 7180678115274748717118259200 }, { target := 633, numerator := 7180678115274748717118259200 }, { target := 634, numerator := 6154866955949784614672793600 }, { target := 635, numerator := 7180678115274748717118259200 }, { target := 636, numerator := 81039081586672164093191782400 }, { target := 637, numerator := 6154866955949784614672793600 }, { target := 638, numerator := 7180678115274748717118259200 }, { target := 639, numerator := 6360029187814777435161886720 }]

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
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 10348405015901225735484866560 }, { target := 2, numerator := 9458635612664858662901121024 }, { target := 3, numerator := 10348405015901225735484866560 }, { target := 4, numerator := 9458635612664858662901121024 }, { target := 90, numerator := 10348405015901225735484866560 }, { target := 91, numerator := 9458635612664858662901121024 }, { target := 92, numerator := 10348405015901225735484866560 }, { target := 93, numerator := 9458635612664858662901121024 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1
