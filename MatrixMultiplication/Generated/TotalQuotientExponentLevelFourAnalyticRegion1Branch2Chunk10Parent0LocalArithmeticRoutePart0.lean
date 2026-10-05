import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
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
  [{ target := 200, numerator := 2597066461825085439297454080 }, { target := 202, numerator := 95906209320374899715761766400 }, { target := 205, numerator := 95906185835363850874288865280 }, { target := 212, numerator := 2597089946836134280770355200 }, { target := 296, numerator := 2671268360734373594705952768 }, { target := 298, numerator := 98646386729528468279069245440 }, { target := 301, numerator := 98646362573517103756411404288 }, { target := 308, numerator := 2671292516745738117363793920 }, { target := 331, numerator := 2597066461825085439297454080 }, { target := 333, numerator := 95906209320374899715761766400 }, { target := 336, numerator := 95906185835363850874288865280 }, { target := 343, numerator := 2597089946836134280770355200 }, { target := 347, numerator := 4203306723507722274000076800 }, { target := 350, numerator := 15288332617431287276240896000 }, { target := 352, numerator := 4203306723507722274000076800 }, { target := 467, numerator := 2300258866187932817663459328 }, { target := 469, numerator := 84945499683760625462531850240 }, { target := 472, numerator := 84945478882750839345798709248 }, { target := 479, numerator := 2300279667197718934396600320 }, { target := 563, numerator := 107666955317377113497731596288 }, { target := 565, numerator := 3975997420681827985359152087040 }, { target := 568, numerator := 3975996447060369931959804100608 }, { target := 575, numerator := 107667928938835166897079582720 }, { target := 598, numerator := 29309750069168821386356981760 }, { target := 600, numerator := 1082370076615659582506454220800 }, { target := 603, numerator := 1082369811570534888438402908160 }, { target := 610, numerator := 29310015114293515454408294400 }, { target := 614, numerator := 84234266739094754370961539072 }, { target := 617, numerator := 306378185653322997015867555840 }, { target := 619, numerator := 84234266739094754370961539072 }, { target := 710, numerator := 141399238178799777297362583552 }, { target := 713, numerator := 514299509250388503972743741440 }, { target := 715, numerator := 141399238178799777297362583552 }, { target := 736, numerator := 135682741034829275004722479104 }, { target := 739, numerator := 493507376890681953277056122880 }, { target := 741, numerator := 135682741034829275004722479104 }, { target := 746, numerator := 51742037415766227970686976000 }, { target := 748, numerator := 51742012743246029384161689600 }, { target := 881, numerator := 4203306723507722274000076800 }, { target := 884, numerator := 15288332617431287276240896000 }, { target := 886, numerator := 4203306723507722274000076800 }, { target := 977, numerator := 135682741034829275004722479104 }, { target := 980, numerator := 493507376890681953277056122880 }, { target := 982, numerator := 135682741034829275004722479104 }, { target := 1003, numerator := 90623292958826492227441655808 }, { target := 1006, numerator := 329616451231818553675753717760 }, { target := 1008, numerator := 90623292958826492227441655808 }, { target := 1013, numerator := 47293189338896608369469030400 }, { target := 1015, numerator := 47293166787751978259542179840 }, { target := 1052, numerator := 4371438992448031164960079872 }, { target := 1055, numerator := 15899865922128538767290531840 }, { target := 1057, numerator := 4371438992448031164960079872 }, { target := 1078, numerator := 84234266739094754370961539072 }, { target := 1081, numerator := 306378185653322997015867555840 }, { target := 1083, numerator := 84234266739094754370961539072 }, { target := 1088, numerator := 51742037415766227970686976000 }, { target := 1090, numerator := 51742012743246029384161689600 }, { target := 1092, numerator := 4035174454567413383040073728 }, { target := 1095, numerator := 14676799312734035785191260160 }, { target := 1097, numerator := 4035174454567413383040073728 }, { target := 1102, numerator := 47293189338896608369469030400 }, { target := 1104, numerator := 47293166787751978259542179840 }, { target := 1106, numerator := 79228162514264337593543950336 }]

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
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 21250649172913403461632000 }, { target := 72, numerator := 357010906104945178155417600 }, { target := 73, numerator := 773523629894047886003404800 }, { target := 74, numerator := 25500779007496084153958400 }, { target := 75, numerator := 408012464119937346463334400 }, { target := 76, numerator := 29750908842078764846284800 }, { target := 77, numerator := 773523629894047886003404800 }, { target := 78, numerator := 773523629894047886003404800 }, { target := 79, numerator := 408012464119937346463334400 }, { target := 80, numerator := 9545791608472700834965094400 }, { target := 81, numerator := 765023370224882524618752000 }, { target := 82, numerator := 357010906104945178155417600 }, { target := 83, numerator := 773523629894047886003404800 }, { target := 84, numerator := 29750908842078764846284800 }, { target := 85, numerator := 765023370224882524618752000 }, { target := 86, numerator := 29750908842078764846284800 }, { target := 87, numerator := 773523629894047886003404800 }, { target := 88, numerator := 773523629894047886003404800 }, { target := 89, numerator := 25500779007496084153958400 }, { target := 659, numerator := 2671268360734373594705952768 }, { target := 661, numerator := 98646386729528468279069245440 }, { target := 664, numerator := 98646362573517103756411404288 }, { target := 671, numerator := 2671292516745738117363793920 }, { target := 694, numerator := 107666955317377113497731596288 }, { target := 696, numerator := 3975997420681827985359152087040 }, { target := 699, numerator := 3975996447060369931959804100608 }, { target := 706, numerator := 107667928938835166897079582720 }, { target := 720, numerator := 2597066461825085439297454080 }, { target := 722, numerator := 95906209320374899715761766400 }, { target := 725, numerator := 95906185835363850874288865280 }, { target := 732, numerator := 2597089946836134280770355200 }, { target := 830, numerator := 2597066461825085439297454080 }, { target := 832, numerator := 95906209320374899715761766400 }, { target := 835, numerator := 95906185835363850874288865280 }, { target := 842, numerator := 2597089946836134280770355200 }, { target := 865, numerator := 2226056967278644662254960640 }, { target := 867, numerator := 82205322274607056899224371200 }, { target := 870, numerator := 82205302144597586463676170240 }, { target := 877, numerator := 2226077097288115097803161600 }, { target := 926, numerator := 2597066461825085439297454080 }, { target := 928, numerator := 95906209320374899715761766400 }, { target := 931, numerator := 95906185835363850874288865280 }, { target := 938, numerator := 2597089946836134280770355200 }, { target := 961, numerator := 29309750069168821386356981760 }, { target := 963, numerator := 1082370076615659582506454220800 }, { target := 966, numerator := 1082369811570534888438402908160 }, { target := 973, numerator := 29310015114293515454408294400 }, { target := 987, numerator := 2226056967278644662254960640 }, { target := 989, numerator := 82205322274607056899224371200 }, { target := 992, numerator := 82205302144597586463676170240 }, { target := 999, numerator := 2226077097288115097803161600 }, { target := 1036, numerator := 2597066461825085439297454080 }, { target := 1038, numerator := 95906209320374899715761766400 }, { target := 1041, numerator := 95906185835363850874288865280 }, { target := 1048, numerator := 2597089946836134280770355200 }, { target := 1062, numerator := 2300258866187932817663459328 }, { target := 1064, numerator := 84945499683760625462531850240 }, { target := 1067, numerator := 84945478882750839345798709248 }, { target := 1074, numerator := 2300279667197718934396600320 }]

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
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 566683977944357425643520000 }, { target := 147, numerator := 9520290829465204750811136000 }, { target := 148, numerator := 20627296797174610293424128000 }, { target := 149, numerator := 680020773533228910772224000 }, { target := 150, numerator := 10880332376531662572355584000 }, { target := 151, numerator := 793357569122100395900928000 }, { target := 152, numerator := 20627296797174610293424128000 }, { target := 153, numerator := 20627296797174610293424128000 }, { target := 154, numerator := 10880332376531662572355584000 }, { target := 155, numerator := 254554442892605355599069184000 }, { target := 156, numerator := 20400623205996867323166720000 }, { target := 157, numerator := 9520290829465204750811136000 }, { target := 158, numerator := 20627296797174610293424128000 }, { target := 159, numerator := 793357569122100395900928000 }, { target := 160, numerator := 20400623205996867323166720000 }, { target := 161, numerator := 793357569122100395900928000 }, { target := 162, numerator := 20627296797174610293424128000 }, { target := 163, numerator := 20627296797174610293424128000 }, { target := 164, numerator := 680020773533228910772224000 }, { target := 181, numerator := 541891553909291788271616000 }, { target := 182, numerator := 9103778105676102042963148800 }, { target := 183, numerator := 19724852562298221093086822400 }, { target := 184, numerator := 650269864691150145925939200 }, { target := 185, numerator := 10404317835058402334815027200 }, { target := 186, numerator := 758648175473008503580262400 }, { target := 187, numerator := 19724852562298221093086822400 }, { target := 188, numerator := 19724852562298221093086822400 }, { target := 189, numerator := 10404317835058402334815027200 }, { target := 190, numerator := 243417686016053871291609907200 }, { target := 191, numerator := 19508095940734504377778176000 }, { target := 192, numerator := 9103778105676102042963148800 }, { target := 193, numerator := 19724852562298221093086822400 }, { target := 194, numerator := 758648175473008503580262400 }, { target := 195, numerator := 19508095940734504377778176000 }, { target := 196, numerator := 758648175473008503580262400 }, { target := 197, numerator := 19724852562298221093086822400 }, { target := 198, numerator := 19724852562298221093086822400 }, { target := 199, numerator := 650269864691150145925939200 }, { target := 242, numerator := 17708874310761169551360000 }, { target := 243, numerator := 297509088420787648462848000 }, { target := 244, numerator := 644603024911706571669504000 }, { target := 245, numerator := 21250649172913403461632000 }, { target := 246, numerator := 340010386766614455386112000 }, { target := 247, numerator := 24792424035065637371904000 }, { target := 248, numerator := 644603024911706571669504000 }, { target := 249, numerator := 644603024911706571669504000 }, { target := 250, numerator := 340010386766614455386112000 }, { target := 251, numerator := 7954826340393917362470912000 }, { target := 252, numerator := 637519475187402103848960000 }, { target := 253, numerator := 297509088420787648462848000 }, { target := 254, numerator := 644603024911706571669504000 }, { target := 255, numerator := 24792424035065637371904000 }, { target := 256, numerator := 637519475187402103848960000 }, { target := 257, numerator := 24792424035065637371904000 }, { target := 258, numerator := 644603024911706571669504000 }, { target := 259, numerator := 644603024911706571669504000 }, { target := 260, numerator := 21250649172913403461632000 }]

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
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 277, numerator := 556058653357900723912704000 }, { target := 278, numerator := 9341785376412732161733427200 }, { target := 279, numerator := 20240534982227586350422425600 }, { target := 280, numerator := 667270384029480868695244800 }, { target := 281, numerator := 10676326144471693899123916800 }, { target := 282, numerator := 778482114701061013477785600 }, { target := 283, numerator := 20240534982227586350422425600 }, { target := 284, numerator := 20240534982227586350422425600 }, { target := 285, numerator := 10676326144471693899123916800 }, { target := 286, numerator := 249781547088369005181586636800 }, { target := 287, numerator := 20018111520884426060857344000 }, { target := 288, numerator := 9341785376412732161733427200 }, { target := 289, numerator := 20240534982227586350422425600 }, { target := 290, numerator := 778482114701061013477785600 }, { target := 291, numerator := 20018111520884426060857344000 }, { target := 292, numerator := 778482114701061013477785600 }, { target := 293, numerator := 20240534982227586350422425600 }, { target := 294, numerator := 20240534982227586350422425600 }, { target := 295, numerator := 667270384029480868695244800 }, { target := 312, numerator := 17708874310761169551360000 }, { target := 313, numerator := 297509088420787648462848000 }, { target := 314, numerator := 644603024911706571669504000 }, { target := 315, numerator := 21250649172913403461632000 }, { target := 316, numerator := 340010386766614455386112000 }, { target := 317, numerator := 24792424035065637371904000 }, { target := 318, numerator := 644603024911706571669504000 }, { target := 319, numerator := 644603024911706571669504000 }, { target := 320, numerator := 340010386766614455386112000 }, { target := 321, numerator := 7954826340393917362470912000 }, { target := 322, numerator := 637519475187402103848960000 }, { target := 323, numerator := 297509088420787648462848000 }, { target := 324, numerator := 644603024911706571669504000 }, { target := 325, numerator := 24792424035065637371904000 }, { target := 326, numerator := 637519475187402103848960000 }, { target := 327, numerator := 24792424035065637371904000 }, { target := 328, numerator := 644603024911706571669504000 }, { target := 329, numerator := 644603024911706571669504000 }, { target := 330, numerator := 21250649172913403461632000 }, { target := 413, numerator := 541891553909291788271616000 }, { target := 414, numerator := 9103778105676102042963148800 }, { target := 415, numerator := 19724852562298221093086822400 }, { target := 416, numerator := 650269864691150145925939200 }, { target := 417, numerator := 10404317835058402334815027200 }, { target := 418, numerator := 758648175473008503580262400 }, { target := 419, numerator := 19724852562298221093086822400 }, { target := 420, numerator := 19724852562298221093086822400 }, { target := 421, numerator := 10404317835058402334815027200 }, { target := 422, numerator := 243417686016053871291609907200 }, { target := 423, numerator := 19508095940734504377778176000 }, { target := 424, numerator := 9103778105676102042963148800 }, { target := 425, numerator := 19724852562298221093086822400 }, { target := 426, numerator := 758648175473008503580262400 }, { target := 427, numerator := 19508095940734504377778176000 }, { target := 428, numerator := 758648175473008503580262400 }, { target := 429, numerator := 19724852562298221093086822400 }, { target := 430, numerator := 19724852562298221093086822400 }, { target := 431, numerator := 650269864691150145925939200 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 448, numerator := 308134413007244350193664000 }, { target := 449, numerator := 5176658138521705083253555200 }, { target := 450, numerator := 11216092633463694347049369600 }, { target := 451, numerator := 369761295608693220232396800 }, { target := 452, numerator := 5916180729739091523718348800 }, { target := 453, numerator := 431388178210142090271129600 }, { target := 454, numerator := 11216092633463694347049369600 }, { target := 455, numerator := 11216092633463694347049369600 }, { target := 456, numerator := 5916180729739091523718348800 }, { target := 457, numerator := 138413978322854162106993868800 }, { target := 458, numerator := 11092838868260796606971904000 }, { target := 459, numerator := 5176658138521705083253555200 }, { target := 460, numerator := 11216092633463694347049369600 }, { target := 461, numerator := 431388178210142090271129600 }, { target := 462, numerator := 11092838868260796606971904000 }, { target := 463, numerator := 431388178210142090271129600 }, { target := 464, numerator := 11216092633463694347049369600 }, { target := 465, numerator := 11216092633463694347049369600 }, { target := 466, numerator := 369761295608693220232396800 }, { target := 509, numerator := 556058653357900723912704000 }, { target := 510, numerator := 9341785376412732161733427200 }, { target := 511, numerator := 20240534982227586350422425600 }, { target := 512, numerator := 667270384029480868695244800 }, { target := 513, numerator := 10676326144471693899123916800 }, { target := 514, numerator := 778482114701061013477785600 }, { target := 515, numerator := 20240534982227586350422425600 }, { target := 516, numerator := 20240534982227586350422425600 }, { target := 517, numerator := 10676326144471693899123916800 }, { target := 518, numerator := 249781547088369005181586636800 }, { target := 519, numerator := 20018111520884426060857344000 }, { target := 520, numerator := 9341785376412732161733427200 }, { target := 521, numerator := 20240534982227586350422425600 }, { target := 522, numerator := 778482114701061013477785600 }, { target := 523, numerator := 20018111520884426060857344000 }, { target := 524, numerator := 778482114701061013477785600 }, { target := 525, numerator := 20240534982227586350422425600 }, { target := 526, numerator := 20240534982227586350422425600 }, { target := 527, numerator := 667270384029480868695244800 }, { target := 544, numerator := 8680890187135125314076672000 }, { target := 545, numerator := 145838955143870105276488089600 }, { target := 546, numerator := 315984402811718561432390860800 }, { target := 547, numerator := 10417068224562150376892006400 }, { target := 548, numerator := 166673091592994406030272102400 }, { target := 549, numerator := 12153246261989175439707340800 }, { target := 550, numerator := 315984402811718561432390860800 }, { target := 551, numerator := 315984402811718561432390860800 }, { target := 552, numerator := 166673091592994406030272102400 }, { target := 553, numerator := 3899455872061098291083241062400 }, { target := 554, numerator := 312512046736864511306760192000 }, { target := 555, numerator := 145838955143870105276488089600 }, { target := 556, numerator := 315984402811718561432390860800 }, { target := 557, numerator := 12153246261989175439707340800 }, { target := 558, numerator := 312512046736864511306760192000 }, { target := 559, numerator := 12153246261989175439707340800 }, { target := 560, numerator := 315984402811718561432390860800 }, { target := 561, numerator := 315984402811718561432390860800 }, { target := 562, numerator := 10417068224562150376892006400 }]

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
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 579, numerator := 340010386766614455386112000 }, { target := 580, numerator := 5712174497679122850486681600 }, { target := 581, numerator := 12376378078304766176054476800 }, { target := 582, numerator := 408012464119937346463334400 }, { target := 583, numerator := 6528199425918997543413350400 }, { target := 584, numerator := 476014541473260237540556800 }, { target := 585, numerator := 12376378078304766176054476800 }, { target := 586, numerator := 12376378078304766176054476800 }, { target := 587, numerator := 6528199425918997543413350400 }, { target := 588, numerator := 152732665735563213359441510400 }, { target := 589, numerator := 12240373923598120393900032000 }, { target := 590, numerator := 5712174497679122850486681600 }, { target := 591, numerator := 12376378078304766176054476800 }, { target := 592, numerator := 476014541473260237540556800 }, { target := 593, numerator := 12240373923598120393900032000 }, { target := 594, numerator := 476014541473260237540556800 }, { target := 595, numerator := 12376378078304766176054476800 }, { target := 596, numerator := 12376378078304766176054476800 }, { target := 597, numerator := 408012464119937346463334400 }, { target := 640, numerator := 566683977944357425643520000 }, { target := 641, numerator := 9520290829465204750811136000 }, { target := 642, numerator := 20627296797174610293424128000 }, { target := 643, numerator := 680020773533228910772224000 }, { target := 644, numerator := 10880332376531662572355584000 }, { target := 645, numerator := 793357569122100395900928000 }, { target := 646, numerator := 20627296797174610293424128000 }, { target := 647, numerator := 20627296797174610293424128000 }, { target := 648, numerator := 10880332376531662572355584000 }, { target := 649, numerator := 254554442892605355599069184000 }, { target := 650, numerator := 20400623205996867323166720000 }, { target := 651, numerator := 9520290829465204750811136000 }, { target := 652, numerator := 20627296797174610293424128000 }, { target := 653, numerator := 793357569122100395900928000 }, { target := 654, numerator := 20400623205996867323166720000 }, { target := 655, numerator := 793357569122100395900928000 }, { target := 656, numerator := 20627296797174610293424128000 }, { target := 657, numerator := 20627296797174610293424128000 }, { target := 658, numerator := 680020773533228910772224000 }, { target := 675, numerator := 541891553909291788271616000 }, { target := 676, numerator := 9103778105676102042963148800 }, { target := 677, numerator := 19724852562298221093086822400 }, { target := 678, numerator := 650269864691150145925939200 }, { target := 679, numerator := 10404317835058402334815027200 }, { target := 680, numerator := 758648175473008503580262400 }, { target := 681, numerator := 19724852562298221093086822400 }, { target := 682, numerator := 19724852562298221093086822400 }, { target := 683, numerator := 10404317835058402334815027200 }, { target := 684, numerator := 243417686016053871291609907200 }, { target := 685, numerator := 19508095940734504377778176000 }, { target := 686, numerator := 9103778105676102042963148800 }, { target := 687, numerator := 19724852562298221093086822400 }, { target := 688, numerator := 758648175473008503580262400 }, { target := 689, numerator := 19508095940734504377778176000 }, { target := 690, numerator := 758648175473008503580262400 }, { target := 691, numerator := 19724852562298221093086822400 }, { target := 692, numerator := 19724852562298221093086822400 }, { target := 693, numerator := 650269864691150145925939200 }]

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
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 776, numerator := 17708874310761169551360000 }, { target := 777, numerator := 297509088420787648462848000 }, { target := 778, numerator := 644603024911706571669504000 }, { target := 779, numerator := 21250649172913403461632000 }, { target := 780, numerator := 340010386766614455386112000 }, { target := 781, numerator := 24792424035065637371904000 }, { target := 782, numerator := 644603024911706571669504000 }, { target := 783, numerator := 644603024911706571669504000 }, { target := 784, numerator := 340010386766614455386112000 }, { target := 785, numerator := 7954826340393917362470912000 }, { target := 786, numerator := 637519475187402103848960000 }, { target := 787, numerator := 297509088420787648462848000 }, { target := 788, numerator := 644603024911706571669504000 }, { target := 789, numerator := 24792424035065637371904000 }, { target := 790, numerator := 637519475187402103848960000 }, { target := 791, numerator := 24792424035065637371904000 }, { target := 792, numerator := 644603024911706571669504000 }, { target := 793, numerator := 644603024911706571669504000 }, { target := 794, numerator := 21250649172913403461632000 }, { target := 811, numerator := 340010386766614455386112000 }, { target := 812, numerator := 5712174497679122850486681600 }, { target := 813, numerator := 12376378078304766176054476800 }, { target := 814, numerator := 408012464119937346463334400 }, { target := 815, numerator := 6528199425918997543413350400 }, { target := 816, numerator := 476014541473260237540556800 }, { target := 817, numerator := 12376378078304766176054476800 }, { target := 818, numerator := 12376378078304766176054476800 }, { target := 819, numerator := 6528199425918997543413350400 }, { target := 820, numerator := 152732665735563213359441510400 }, { target := 821, numerator := 12240373923598120393900032000 }, { target := 822, numerator := 5712174497679122850486681600 }, { target := 823, numerator := 12376378078304766176054476800 }, { target := 824, numerator := 476014541473260237540556800 }, { target := 825, numerator := 12240373923598120393900032000 }, { target := 826, numerator := 476014541473260237540556800 }, { target := 827, numerator := 12376378078304766176054476800 }, { target := 828, numerator := 12376378078304766176054476800 }, { target := 829, numerator := 408012464119937346463334400 }, { target := 846, numerator := 17708874310761169551360000 }, { target := 847, numerator := 297509088420787648462848000 }, { target := 848, numerator := 644603024911706571669504000 }, { target := 849, numerator := 21250649172913403461632000 }, { target := 850, numerator := 340010386766614455386112000 }, { target := 851, numerator := 24792424035065637371904000 }, { target := 852, numerator := 644603024911706571669504000 }, { target := 853, numerator := 644603024911706571669504000 }, { target := 854, numerator := 340010386766614455386112000 }, { target := 855, numerator := 7954826340393917362470912000 }, { target := 856, numerator := 637519475187402103848960000 }, { target := 857, numerator := 297509088420787648462848000 }, { target := 858, numerator := 644603024911706571669504000 }, { target := 859, numerator := 24792424035065637371904000 }, { target := 860, numerator := 637519475187402103848960000 }, { target := 861, numerator := 24792424035065637371904000 }, { target := 862, numerator := 644603024911706571669504000 }, { target := 863, numerator := 644603024911706571669504000 }, { target := 864, numerator := 21250649172913403461632000 }]

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
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 746, numerator := 39614081257132168796771975168 }, { target := 748, numerator := 39614081257132168796771975168 }, { target := 907, numerator := 545433328771444022181888000 }, { target := 908, numerator := 9163279923360259572655718400 }, { target := 909, numerator := 19853773167280562407420723200 }, { target := 910, numerator := 654519994525732826618265600 }, { target := 911, numerator := 10472319912411725225892249600 }, { target := 912, numerator := 763606660280021631054643200 }, { target := 913, numerator := 19853773167280562407420723200 }, { target := 914, numerator := 19853773167280562407420723200 }, { target := 915, numerator := 10472319912411725225892249600 }, { target := 916, numerator := 245008651284132654764104089600 }, { target := 917, numerator := 19635599835771984798547968000 }, { target := 918, numerator := 9163279923360259572655718400 }, { target := 919, numerator := 19853773167280562407420723200 }, { target := 920, numerator := 763606660280021631054643200 }, { target := 921, numerator := 19635599835771984798547968000 }, { target := 922, numerator := 763606660280021631054643200 }, { target := 923, numerator := 19853773167280562407420723200 }, { target := 924, numerator := 19853773167280562407420723200 }, { target := 925, numerator := 654519994525732826618265600 }, { target := 942, numerator := 308134413007244350193664000 }, { target := 943, numerator := 5176658138521705083253555200 }, { target := 944, numerator := 11216092633463694347049369600 }, { target := 945, numerator := 369761295608693220232396800 }, { target := 946, numerator := 5916180729739091523718348800 }, { target := 947, numerator := 431388178210142090271129600 }, { target := 948, numerator := 11216092633463694347049369600 }, { target := 949, numerator := 11216092633463694347049369600 }, { target := 950, numerator := 5916180729739091523718348800 }, { target := 951, numerator := 138413978322854162106993868800 }, { target := 952, numerator := 11092838868260796606971904000 }, { target := 953, numerator := 5176658138521705083253555200 }, { target := 954, numerator := 11216092633463694347049369600 }, { target := 955, numerator := 431388178210142090271129600 }, { target := 956, numerator := 11092838868260796606971904000 }, { target := 957, numerator := 431388178210142090271129600 }, { target := 958, numerator := 11216092633463694347049369600 }, { target := 959, numerator := 11216092633463694347049369600 }, { target := 960, numerator := 369761295608693220232396800 }, { target := 1013, numerator := 39614081257132168796771975168 }, { target := 1015, numerator := 39614081257132168796771975168 }, { target := 1017, numerator := 21250649172913403461632000 }, { target := 1018, numerator := 357010906104945178155417600 }, { target := 1019, numerator := 773523629894047886003404800 }, { target := 1020, numerator := 25500779007496084153958400 }, { target := 1021, numerator := 408012464119937346463334400 }, { target := 1022, numerator := 29750908842078764846284800 }, { target := 1023, numerator := 773523629894047886003404800 }, { target := 1024, numerator := 773523629894047886003404800 }, { target := 1025, numerator := 408012464119937346463334400 }, { target := 1026, numerator := 9545791608472700834965094400 }, { target := 1027, numerator := 765023370224882524618752000 }, { target := 1028, numerator := 357010906104945178155417600 }, { target := 1029, numerator := 773523629894047886003404800 }, { target := 1030, numerator := 29750908842078764846284800 }, { target := 1031, numerator := 765023370224882524618752000 }, { target := 1032, numerator := 29750908842078764846284800 }, { target := 1033, numerator := 773523629894047886003404800 }, { target := 1034, numerator := 773523629894047886003404800 }, { target := 1035, numerator := 25500779007496084153958400 }, { target := 1088, numerator := 39614081257132168796771975168 }, { target := 1090, numerator := 39614081257132168796771975168 }]

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
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 71123921654534535393574912 }, { target := 72, numerator := 11354734451745628266413686784 }, { target := 74, numerator := 113303174568709137460304543744 }, { target := 82, numerator := 11354734451745628266413686784 }, { target := 89, numerator := 71115806191086961850056704 }, { target := 146, numerator := 7457214908709705633411104768 }, { target := 147, numerator := 1190523428239544410951150206976 }, { target := 149, numerator := 11879633503646203019439338684416 }, { target := 157, numerator := 1190523428239544410951150206976 }, { target := 164, numerator := 7456364017004010778820345856 }, { target := 200, numerator := 9072564340941354017394524160 }, { target := 202, numerator := 340879549045985800432511877120 }, { target := 205, numerator := 340853767604526964713707274240 }, { target := 212, numerator := 9098345782400189736199127040 }, { target := 242, numerator := 80381323238358268860432384000 }, { target := 243, numerator := 12832652629655693194835263488000 }, { target := 245, numerator := 128050575489588369050679902208000 }, { target := 253, numerator := 12832652629655693194835263488000 }, { target := 260, numerator := 80372151476236137611132928000 }, { target := 296, numerator := 759637963520635029409178320896 }, { target := 298, numerator := 28541549744055866160524738691072 }, { target := 301, numerator := 28539391086266244535848108294144 }, { target := 308, numerator := 761796621310256654085808717824 }, { target := 347, numerator := 122295741184674816771269591040 }, { target := 350, numerator := 419819895988805260286720212992 }, { target := 352, numerator := 122295741184674816771269591040 }, { target := 640, numerator := 7457220597258186360799363072 }, { target := 641, numerator := 1190524336400341959189834235904 }, { target := 643, numerator := 11879642565725269540205351665664 }, { target := 651, numerator := 1190524336400341959189834235904 }, { target := 658, numerator := 7456369704903410209913831424 }, { target := 659, numerator := 759638238432942719162847854592 }, { target := 661, numerator := 28541560073217495754559396511744 }, { target := 664, numerator := 28539401414646657783470896447488 }, { target := 671, numerator := 761796897003780690251347918848 }, { target := 710, numerator := 1184565487172432426634712186880 }, { target := 713, numerator := 4066406195336730443239363969024 }, { target := 715, numerator := 1184565487172432426634712186880 }, { target := 1017, numerator := 71123921654534535393574912 }, { target := 1018, numerator := 11354734451745628266413686784 }, { target := 1020, numerator := 113303174568709137460304543744 }, { target := 1028, numerator := 11354734451745628266413686784 }, { target := 1035, numerator := 71115806191086961850056704 }, { target := 1036, numerator := 9072289428633664263724990464 }, { target := 1038, numerator := 340869219884356206397854056448 }, { target := 1041, numerator := 340843439224113717090919120896 }, { target := 1048, numerator := 9098070088876153570659926016 }, { target := 1052, numerator := 122295741184674816771269591040 }, { target := 1055, numerator := 419819895988805260286720212992 }, { target := 1057, numerator := 122295741184674816771269591040 }, { target := 1102, numerator := 39614081257132168796771975168 }, { target := 1104, numerator := 39614081257132168796771975168 }]

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2925802763545385874090885120 }, { target := 30, numerator := 2275624371646411235404021760 }, { target := 31, numerator := 2600713567595898554747453440 }, { target := 32, numerator := 3055838441925180801828257792 }, { target := 33, numerator := 36084900750393092447120916480 }, { target := 34, numerator := 81142263308992034908120547328 }, { target := 35, numerator := 2275624371646411235404021760 }, { target := 36, numerator := 36084900750393092447120916480 }, { target := 37, numerator := 2600713567595898554747453440 }, { target := 38, numerator := 2535695728406001090878767104 }, { target := 39, numerator := 2535695728406001090878767104 }, { target := 40, numerator := 2535695728406001090878767104 }, { target := 41, numerator := 81142263308992034908120547328 }, { target := 42, numerator := 2535695728406001090878767104 }, { target := 43, numerator := 2925802763545385874090885120 }, { target := 44, numerator := 3055838441925180801828257792 }, { target := 104, numerator := 102395802085965922657747599360 }, { target := 105, numerator := 79641179400195717622692577280 }, { target := 106, numerator := 91018490743080820140220088320 }, { target := 107, numerator := 106946726623119963664758603776 }, { target := 108, numerator := 1262881559060246379445553725440 }, { target := 109, numerator := 2839776911184121588374866755584 }, { target := 110, numerator := 79641179400195717622692577280 }, { target := 111, numerator := 1262881559060246379445553725440 }, { target := 112, numerator := 91018490743080820140220088320 }, { target := 113, numerator := 88743028474503799636714586112 }, { target := 114, numerator := 88743028474503799636714586112 }, { target := 115, numerator := 88743028474503799636714586112 }, { target := 116, numerator := 2839776911184121588374866755584 }, { target := 117, numerator := 88743028474503799636714586112 }, { target := 118, numerator := 102395802085965922657747599360 }, { target := 119, numerator := 106946726623119963664758603776 }, { target := 226, numerator := 102395852307226663332001873920 }, { target := 227, numerator := 79641218461176293702668124160 }, { target := 228, numerator := 91018535384201478517334999040 }, { target := 229, numerator := 106946779076436737257868623872 }, { target := 230, numerator := 1262882178455795514428023111680 }, { target := 231, numerator := 2839778303987086129740851970048 }, { target := 232, numerator := 79641218461176293702668124160 }, { target := 233, numerator := 1262882178455795514428023111680 }, { target := 234, numerator := 91018535384201478517334999040 }, { target := 235, numerator := 88743071999596441554401624064 }, { target := 236, numerator := 88743071999596441554401624064 }, { target := 237, numerator := 88743071999596441554401624064 }, { target := 238, numerator := 2839778303987086129740851970048 }, { target := 239, numerator := 88743071999596441554401624064 }, { target := 240, numerator := 102395852307226663332001873920 }, { target := 241, numerator := 106946779076436737257868623872 }, { target := 624, numerator := 2925777652915015536963747840 }, { target := 625, numerator := 2275604841156123195416248320 }, { target := 626, numerator := 2600691247035569366189998080 }, { target := 627, numerator := 3055812215266794005273247744 }, { target := 628, numerator := 36084591052618524955886223360 }, { target := 629, numerator := 81141566907509764225127940096 }, { target := 630, numerator := 2275604841156123195416248320 }, { target := 631, numerator := 36084591052618524955886223360 }, { target := 632, numerator := 2600691247035569366189998080 }, { target := 633, numerator := 2535673965859680132035248128 }, { target := 634, numerator := 2535673965859680132035248128 }, { target := 635, numerator := 2535673965859680132035248128 }, { target := 636, numerator := 81141566907509764225127940096 }, { target := 637, numerator := 2535673965859680132035248128 }, { target := 638, numerator := 2925777652915015536963747840 }, { target := 639, numerator := 3055812215266794005273247744 }]

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 127162854253014761802301440 }, { target := 72, numerator := 18781288105200793334883287040 }, { target := 74, numerator := 195754224967379586559613337600 }, { target := 82, numerator := 18781288105200793334883287040 }, { target := 89, numerator := 127162854253014761802301440 }, { target := 146, numerator := 18781288105200793334883287040 }, { target := 147, numerator := 2773897967001587370666114416640 }, { target := 149, numerator := 28911874607717716988255639961600 }, { target := 157, numerator := 2773897967001587370666114416640 }, { target := 164, numerator := 18781288105200793334883287040 }, { target := 200, numerator := 7050834248625819215607103488 }, { target := 202, numerator := 255524567004599560257505591296 }, { target := 205, numerator := 255524660908880670982448087040 }, { target := 212, numerator := 7050740344344708490664607744 }, { target := 242, numerator := 195754224967379586559613337600 }, { target := 243, numerator := 28911874607717716988255639961600 }, { target := 245, numerator := 301343633859736033881388744704000 }, { target := 253, numerator := 28911874607717716988255639961600 }, { target := 260, numerator := 195754224967379586559613337600 }, { target := 296, numerator := 592899306589794809256949579776 }, { target := 298, numerator := 21486867121179523012649331720192 }, { target := 301, numerator := 21486875017519330917364090798080 }, { target := 308, numerator := 592891410249986904542190501888 }, { target := 347, numerator := 4450146589301828200830074880 }, { target := 350, numerator := 15084795082550586424510382080 }, { target := 352, numerator := 4450146589301828200830074880 }, { target := 614, numerator := 106516411911676016935997276160 }, { target := 617, numerator := 361061869395243068612474306560 }, { target := 619, numerator := 106516411911676016935997276160 }, { target := 659, numerator := 592899163550534698778398556160 }, { target := 661, numerator := 21486861937389390446168081694720 }, { target := 664, numerator := 21486869833727293328240463052800 }, { target := 671, numerator := 592891267212631816706017198080 }, { target := 710, numerator := 79671979260081117789054566400 }, { target := 713, numerator := 270066492606954047277524582400 }, { target := 715, numerator := 79671979260081117789054566400 }, { target := 736, numerator := 92448206564850882623695749120 }, { target := 739, numerator := 313374452682663795399506001920 }, { target := 741, numerator := 92448206564850882623695749120 }, { target := 881, numerator := 4450146589301828200830074880 }, { target := 884, numerator := 15084795082550586424510382080 }, { target := 886, numerator := 4450146589301828200830074880 }, { target := 977, numerator := 92304653449066952681733488640 }, { target := 980, numerator := 312887846389678292611618570240 }, { target := 982, numerator := 92304653449066952681733488640 }, { target := 1003, numerator := 92735312796418742507620270080 }, { target := 1006, numerator := 314347665268634800975280865280 }, { target := 1008, numerator := 92735312796418742507620270080 }, { target := 1036, numerator := 7050977287885929694158127104 }, { target := 1038, numerator := 255529750794732126738755616768 }, { target := 1041, numerator := 255529844700918260106075832320 }, { target := 1048, numerator := 7050883381699796326837911552 }, { target := 1052, numerator := 4450146589301828200830074880 }, { target := 1055, numerator := 15084795082550586424510382080 }, { target := 1057, numerator := 4450146589301828200830074880 }, { target := 1078, numerator := 106516411911676016935997276160 }, { target := 1081, numerator := 361061869395243068612474306560 }, { target := 1083, numerator := 106516411911676016935997276160 }, { target := 1092, numerator := 4450146589301828200830074880 }, { target := 1095, numerator := 15084795082550586424510382080 }, { target := 1097, numerator := 4450146589301828200830074880 }]

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
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4561400254034373905850826752 }, { target := 6, numerator := 109179322209467917359397208064 }, { target := 7, numerator := 81663778741583145733780930560 }, { target := 8, numerator := 94759411728972154689288142848 }, { target := 9, numerator := 4561400254034373905850826752 }, { target := 10, numerator := 94612269785293626498776825856 }, { target := 11, numerator := 95053695616329211070310776832 }, { target := 12, numerator := 4561400254034373905850826752 }, { target := 13, numerator := 109179322209467917359397208064 }, { target := 14, numerator := 4561400254034373905850826752 }, { target := 29, numerator := 6963323894476207984207724544 }, { target := 30, numerator := 585540627252687426872554815488 }, { target := 35, numerator := 585540485988737282304198574080 }, { target := 43, numerator := 6963465158426352552563965952 }, { target := 94, numerator := 15461914959614351085123141632 }, { target := 95, numerator := 370088416130124145327786164224 }, { target := 96, numerator := 276818154922127898459462696960 }, { target := 97, numerator := 321208813999730390284493651968 }, { target := 98, numerator := 15461914959614351085123141632 }, { target := 99, numerator := 320710042549420249926909034496 }, { target := 100, numerator := 322206356900350670999662886912 }, { target := 101, numerator := 15461914959614351085123141632 }, { target := 102, numerator := 370088416130124145327786164224 }, { target := 103, numerator := 15461914959614351085123141632 }, { target := 104, numerator := 252353162804187863587642933248 }, { target := 105, numerator := 21220186146271266521357584695296 }, { target := 110, numerator := 21220181026818954749141172879360 }, { target := 118, numerator := 252358282256499635804054749184 }, { target := 200, numerator := 2816991916967251688690810880 }, { target := 202, numerator := 98587693743925867682872688640 }, { target := 205, numerator := 98587742097453770894034862080 }, { target := 212, numerator := 2816967740203300083109724160 }, { target := 216, numerator := 4561400254034373905850826752 }, { target := 217, numerator := 109179322209467917359397208064 }, { target := 218, numerator := 81663778741583145733780930560 }, { target := 219, numerator := 94759411728972154689288142848 }, { target := 220, numerator := 4561400254034373905850826752 }, { target := 221, numerator := 94612269785293626498776825856 }, { target := 222, numerator := 95053695616329211070310776832 }, { target := 223, numerator := 4561400254034373905850826752 }, { target := 224, numerator := 109179322209467917359397208064 }, { target := 225, numerator := 4561400254034373905850826752 }, { target := 226, numerator := 252353255542990308044722667520 }, { target := 227, numerator := 21220193944606856952077657047040 }, { target := 232, numerator := 21220188825152663801116911206400 }, { target := 240, numerator := 252358374997183459005468508160 }, { target := 296, numerator := 2190993713196751313426186240 }, { target := 298, numerator := 76679317356386785975567646720 }, { target := 301, numerator := 76679354964686266250916003840 }, { target := 308, numerator := 2190974909047011175752007680 }, { target := 624, numerator := 6963231155673763527127990272 }, { target := 625, numerator := 585532828917096996152482463744 }, { target := 630, numerator := 585532687655028230328460247040 }, { target := 638, numerator := 6963372417742529351150206976 }, { target := 640, numerator := 18781288105200793334883287040 }, { target := 641, numerator := 2773897967001587370666114416640 }, { target := 643, numerator := 28911874607717716988255639961600 }, { target := 651, numerator := 2773897967001587370666114416640 }, { target := 658, numerator := 18781288105200793334883287040 }, { target := 1017, numerator := 127162854253014761802301440 }, { target := 1018, numerator := 18781288105200793334883287040 }, { target := 1020, numerator := 195754224967379586559613337600 }, { target := 1028, numerator := 18781288105200793334883287040 }, { target := 1035, numerator := 127162854253014761802301440 }]

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
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 71463194481160675848617984 }, { target := 72, numerator := 7492787052680133544064843776 }, { target := 74, numerator := 80764755396043412380581888000 }, { target := 82, numerator := 7492792768363927926267183104 }, { target := 89, numerator := 71463194481160675848617984 }, { target := 331, numerator := 2503992815082001501058498560 }, { target := 333, numerator := 87633505550156326829220167680 }, { target := 336, numerator := 87633548531070018572475432960 }, { target := 343, numerator := 2503971324625155629430865920 }, { target := 467, numerator := 2942191557721351763743735808 }, { target := 469, numerator := 102969369021433684024333697024 }, { target := 472, numerator := 102969419524007271822658633728 }, { target := 479, numerator := 2942166306434557864581267456 }, { target := 563, numerator := 34742900309262770827186667520 }, { target := 565, numerator := 1215914889508419034755429826560 }, { target := 568, numerator := 1215915485868596507693096632320 }, { target := 575, numerator := 34742602129174034358353264640 }, { target := 598, numerator := 78124575830558446833025155072 }, { target := 600, numerator := 2734165373164877397071669231616 }, { target := 603, numerator := 2734166714169384579461233508352 }, { target := 610, numerator := 78123905328304855638243016704 }, { target := 659, numerator := 2190993713196751313426186240 }, { target := 661, numerator := 76679317356386785975567646720 }, { target := 664, numerator := 76679354964686266250916003840 }, { target := 671, numerator := 2190974909047011175752007680 }, { target := 694, numerator := 34742900309262770827186667520 }, { target := 696, numerator := 1215914889508419034755429826560 }, { target := 699, numerator := 1215915485868596507693096632320 }, { target := 706, numerator := 34742602129174034358353264640 }, { target := 720, numerator := 2503992815082001501058498560 }, { target := 722, numerator := 87633505550156326829220167680 }, { target := 725, numerator := 87633548531070018572475432960 }, { target := 732, numerator := 2503971324625155629430865920 }, { target := 830, numerator := 2441392994704951463532036096 }, { target := 832, numerator := 85442667911402418658489663488 }, { target := 835, numerator := 85442709817793268108163547136 }, { target := 842, numerator := 2441372041509526738695094272 }, { target := 865, numerator := 2441392994704951463532036096 }, { target := 867, numerator := 85442667911402418658489663488 }, { target := 870, numerator := 85442709817793268108163547136 }, { target := 877, numerator := 2441372041509526738695094272 }, { target := 926, numerator := 2441392994704951463532036096 }, { target := 928, numerator := 85442667911402418658489663488 }, { target := 931, numerator := 85442709817793268108163547136 }, { target := 938, numerator := 2441372041509526738695094272 }, { target := 961, numerator := 78124575830558446833025155072 }, { target := 963, numerator := 2734165373164877397071669231616 }, { target := 966, numerator := 2734166714169384579461233508352 }, { target := 973, numerator := 78123905328304855638243016704 }, { target := 987, numerator := 2441392994704951463532036096 }, { target := 989, numerator := 85442667911402418658489663488 }, { target := 992, numerator := 85442709817793268108163547136 }, { target := 999, numerator := 2441372041509526738695094272 }, { target := 1036, numerator := 2816991916967251688690810880 }, { target := 1038, numerator := 98587693743925867682872688640 }, { target := 1041, numerator := 98587742097453770894034862080 }, { target := 1048, numerator := 2816967740203300083109724160 }, { target := 1062, numerator := 2942191557721351763743735808 }, { target := 1064, numerator := 102969369021433684024333697024 }, { target := 1067, numerator := 102969419524007271822658633728 }, { target := 1074, numerator := 2942166306434557864581267456 }]

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
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 39614081257132168796771975168 }, { target := 2, numerator := 39614081257132168796771975168 }, { target := 3, numerator := 39614081257132168796771975168 }, { target := 4, numerator := 39614081257132168796771975168 }, { target := 5, numerator := 121047825458300583947072962560 }, { target := 7, numerator := 1172478084242101483505786552320 }, { target := 12, numerator := 121047825458300583947072962560 }, { target := 29, numerator := 9054382849276140883091128320 }, { target := 30, numerator := 758115642952457404099741089792 }, { target := 35, numerator := 758115917313838625537271005184 }, { target := 43, numerator := 9054108487894919445561212928 }, { target := 90, numerator := 39614081257132168796771975168 }, { target := 91, numerator := 39614081257132168796771975168 }, { target := 92, numerator := 39614081257132168796771975168 }, { target := 93, numerator := 39614081257132168796771975168 }, { target := 94, numerator := 415536019499123573957263884288 }, { target := 96, numerator := 4024912254567988295859370459136 }, { target := 101, numerator := 415536019499123573957263884288 }, { target := 104, numerator := 340196423697196249730242314240 }, { target := 105, numerator := 28484352249578800296475590918144 }, { target := 110, numerator := 28484362558040707185912984895488 }, { target := 118, numerator := 340186115235289360292848336896 }, { target := 146, numerator := 11408898406198881480173682688 }, { target := 147, numerator := 1196202421175639375617439301632 }, { target := 149, numerator := 12893866497360035183188770816000 }, { target := 157, numerator := 1196203333668513581718493462528 }, { target := 164, numerator := 11408898406198881480173682688 }, { target := 216, numerator := 121047825458300583947072962560 }, { target := 218, numerator := 1172478084242101483505786552320 }, { target := 223, numerator := 121047825458300583947072962560 }, { target := 226, numerator := 340170693921952762379611668480 }, { target := 227, numerator := 28482197917756692943591899660288 }, { target := 232, numerator := 28482208225438949050437888638976 }, { target := 240, numerator := 340160386239696655533622689792 }, { target := 242, numerator := 113843649382349987638996369408 }, { target := 243, numerator := 11936301313073830180416716275712 }, { target := 245, numerator := 128661397835809302294200057856000 }, { target := 253, numerator := 11936310418380507165939201998848 }, { target := 260, numerator := 113843649382349987638996369408 }, { target := 624, numerator := 9080112624519628233721774080 }, { target := 625, numerator := 760269974774564756983432347648 }, { target := 630, numerator := 760270249915596761012367261696 }, { target := 638, numerator := 9079837483487624204786860032 }, { target := 640, numerator := 11408898406198881480173682688 }, { target := 641, numerator := 1196202421175639375617439301632 }, { target := 643, numerator := 12893866497360035183188770816000 }, { target := 651, numerator := 1196203333668513581718493462528 }, { target := 658, numerator := 11408898406198881480173682688 }, { target := 1017, numerator := 71455040305615130358448128 }, { target := 1018, numerator := 7491932102080786198840737792 }, { target := 1020, numerator := 80755539883104566715088896000 }, { target := 1028, numerator := 7491937817112403060004487168 }, { target := 1035, numerator := 71455040305615130358448128 }]

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
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 22100675139829939600097280 }, { target := 72, numerator := 589351337062131722669260800 }, { target := 73, numerator := 563567216065663459802480640 }, { target := 74, numerator := 18417229283191616333414400 }, { target := 75, numerator := 578300999492216752869212160 }, { target := 76, numerator := 18417229283191616333414400 }, { target := 77, numerator := 563567216065663459802480640 }, { target := 78, numerator := 320459789527534124201410560 }, { target := 79, numerator := 578300999492216752869212160 }, { target := 80, numerator := 9028125794620530326639738880 }, { target := 81, numerator := 353610802237279033601556480 }, { target := 82, numerator := 589351337062131722669260800 }, { target := 83, numerator := 563567216065663459802480640 }, { target := 84, numerator := 18417229283191616333414400 }, { target := 85, numerator := 353610802237279033601556480 }, { target := 86, numerator := 18417229283191616333414400 }, { target := 87, numerator := 567250661922301783069163520 }, { target := 88, numerator := 320459789527534124201410560 }, { target := 89, numerator := 22100675139829939600097280 }, { target := 146, numerator := 371291342349142985281634304 }, { target := 147, numerator := 9901102462643812940843581440 }, { target := 148, numerator := 9467929229903146124681674752 }, { target := 149, numerator := 309409451957619154401361920 }, { target := 150, numerator := 9715456791469241448202764288 }, { target := 151, numerator := 309409451957619154401361920 }, { target := 152, numerator := 9467929229903146124681674752 }, { target := 153, numerator := 5383724464062573286583697408 }, { target := 154, numerator := 9715456791469241448202764288 }, { target := 155, numerator := 151672513349624909487547613184 }, { target := 156, numerator := 5940661477586287764506148864 }, { target := 157, numerator := 9901102462643812940843581440 }, { target := 158, numerator := 9467929229903146124681674752 }, { target := 159, numerator := 309409451957619154401361920 }, { target := 160, numerator := 5940661477586287764506148864 }, { target := 161, numerator := 309409451957619154401361920 }, { target := 162, numerator := 9529811120294669955561947136 }, { target := 163, numerator := 5383724464062573286583697408 }, { target := 164, numerator := 371291342349142985281634304 }, { target := 181, numerator := 804464575089809801443540992 }, { target := 182, numerator := 21452388669061594705161093120 }, { target := 183, numerator := 20513846664790149936810295296 }, { target := 184, numerator := 670387145908174834536284160 }, { target := 185, numerator := 21050156381516689804439322624 }, { target := 186, numerator := 670387145908174834536284160 }, { target := 187, numerator := 20513846664790149936810295296 }, { target := 188, numerator := 11664736338802242120931344384 }, { target := 189, numerator := 21050156381516689804439322624 }, { target := 190, numerator := 328623778924187303889686495232 }, { target := 191, numerator := 12871433201436956823096655872 }, { target := 192, numerator := 21452388669061594705161093120 }, { target := 193, numerator := 20513846664790149936810295296 }, { target := 194, numerator := 670387145908174834536284160 }, { target := 195, numerator := 12871433201436956823096655872 }, { target := 196, numerator := 670387145908174834536284160 }, { target := 197, numerator := 20647924093971784903717552128 }, { target := 198, numerator := 11664736338802242120931344384 }, { target := 199, numerator := 804464575089809801443540992 }]

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
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 26520810167795927520116736 }, { target := 243, numerator := 707221604474558067203112960 }, { target := 244, numerator := 676280659278796151762976768 }, { target := 245, numerator := 22100675139829939600097280 }, { target := 246, numerator := 693961199390660103443054592 }, { target := 247, numerator := 22100675139829939600097280 }, { target := 248, numerator := 676280659278796151762976768 }, { target := 249, numerator := 384551747433040949041692672 }, { target := 250, numerator := 693961199390660103443054592 }, { target := 251, numerator := 10833750953544636391967686656 }, { target := 252, numerator := 424332962684734840321867776 }, { target := 253, numerator := 707221604474558067203112960 }, { target := 254, numerator := 676280659278796151762976768 }, { target := 255, numerator := 22100675139829939600097280 }, { target := 256, numerator := 424332962684734840321867776 }, { target := 257, numerator := 22100675139829939600097280 }, { target := 258, numerator := 680700794306762139682996224 }, { target := 259, numerator := 384551747433040949041692672 }, { target := 260, numerator := 26520810167795927520116736 }, { target := 277, numerator := 424332962684734840321867776 }, { target := 278, numerator := 11315545671592929075249807360 }, { target := 279, numerator := 10820490548460738428207628288 }, { target := 280, numerator := 353610802237279033601556480 }, { target := 281, numerator := 11103379190250561655088873472 }, { target := 282, numerator := 353610802237279033601556480 }, { target := 283, numerator := 10820490548460738428207628288 }, { target := 284, numerator := 6152827958928655184667082752 }, { target := 285, numerator := 11103379190250561655088873472 }, { target := 286, numerator := 173340015256714182271482986496 }, { target := 287, numerator := 6789327402955757445149884416 }, { target := 288, numerator := 11315545671592929075249807360 }, { target := 289, numerator := 10820490548460738428207628288 }, { target := 290, numerator := 353610802237279033601556480 }, { target := 291, numerator := 6789327402955757445149884416 }, { target := 292, numerator := 353610802237279033601556480 }, { target := 293, numerator := 10891212708908194234927939584 }, { target := 294, numerator := 6152827958928655184667082752 }, { target := 295, numerator := 424332962684734840321867776 }, { target := 312, numerator := 30940945195761915440136192 }, { target := 313, numerator := 825091871886984411736965120 }, { target := 314, numerator := 788994102491928843723472896 }, { target := 315, numerator := 25784120996468262866780160 }, { target := 316, numerator := 809621399289103454016897024 }, { target := 317, numerator := 25784120996468262866780160 }, { target := 318, numerator := 788994102491928843723472896 }, { target := 319, numerator := 448643705338547773881974784 }, { target := 320, numerator := 809621399289103454016897024 }, { target := 321, numerator := 12639376112468742457295634432 }, { target := 322, numerator := 495055123132190647042179072 }, { target := 323, numerator := 825091871886984411736965120 }, { target := 324, numerator := 788994102491928843723472896 }, { target := 325, numerator := 25784120996468262866780160 }, { target := 326, numerator := 495055123132190647042179072 }, { target := 327, numerator := 25784120996468262866780160 }, { target := 328, numerator := 794150926691222496296828928 }, { target := 329, numerator := 448643705338547773881974784 }, { target := 330, numerator := 30940945195761915440136192 }]

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
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 413, numerator := 804464575089809801443540992 }, { target := 414, numerator := 21452388669061594705161093120 }, { target := 415, numerator := 20513846664790149936810295296 }, { target := 416, numerator := 670387145908174834536284160 }, { target := 417, numerator := 21050156381516689804439322624 }, { target := 418, numerator := 670387145908174834536284160 }, { target := 419, numerator := 20513846664790149936810295296 }, { target := 420, numerator := 11664736338802242120931344384 }, { target := 421, numerator := 21050156381516689804439322624 }, { target := 422, numerator := 328623778924187303889686495232 }, { target := 423, numerator := 12871433201436956823096655872 }, { target := 424, numerator := 21452388669061594705161093120 }, { target := 425, numerator := 20513846664790149936810295296 }, { target := 426, numerator := 670387145908174834536284160 }, { target := 427, numerator := 12871433201436956823096655872 }, { target := 428, numerator := 670387145908174834536284160 }, { target := 429, numerator := 20647924093971784903717552128 }, { target := 430, numerator := 11664736338802242120931344384 }, { target := 431, numerator := 804464575089809801443540992 }, { target := 448, numerator := 804464575089809801443540992 }, { target := 449, numerator := 21452388669061594705161093120 }, { target := 450, numerator := 20513846664790149936810295296 }, { target := 451, numerator := 670387145908174834536284160 }, { target := 452, numerator := 21050156381516689804439322624 }, { target := 453, numerator := 670387145908174834536284160 }, { target := 454, numerator := 20513846664790149936810295296 }, { target := 455, numerator := 11664736338802242120931344384 }, { target := 456, numerator := 21050156381516689804439322624 }, { target := 457, numerator := 328623778924187303889686495232 }, { target := 458, numerator := 12871433201436956823096655872 }, { target := 459, numerator := 21452388669061594705161093120 }, { target := 460, numerator := 20513846664790149936810295296 }, { target := 461, numerator := 670387145908174834536284160 }, { target := 462, numerator := 12871433201436956823096655872 }, { target := 463, numerator := 670387145908174834536284160 }, { target := 464, numerator := 20647924093971784903717552128 }, { target := 465, numerator := 11664736338802242120931344384 }, { target := 466, numerator := 804464575089809801443540992 }, { target := 509, numerator := 424332962684734840321867776 }, { target := 510, numerator := 11315545671592929075249807360 }, { target := 511, numerator := 10820490548460738428207628288 }, { target := 512, numerator := 353610802237279033601556480 }, { target := 513, numerator := 11103379190250561655088873472 }, { target := 514, numerator := 353610802237279033601556480 }, { target := 515, numerator := 10820490548460738428207628288 }, { target := 516, numerator := 6152827958928655184667082752 }, { target := 517, numerator := 11103379190250561655088873472 }, { target := 518, numerator := 173340015256714182271482986496 }, { target := 519, numerator := 6789327402955757445149884416 }, { target := 520, numerator := 11315545671592929075249807360 }, { target := 521, numerator := 10820490548460738428207628288 }, { target := 522, numerator := 353610802237279033601556480 }, { target := 523, numerator := 6789327402955757445149884416 }, { target := 524, numerator := 353610802237279033601556480 }, { target := 525, numerator := 10891212708908194234927939584 }, { target := 526, numerator := 6152827958928655184667082752 }, { target := 527, numerator := 424332962684734840321867776 }]

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
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 544, numerator := 9927623272811608868363698176 }, { target := 545, numerator := 264736620608309569823031951360 }, { target := 546, numerator := 253154393456696026143274303488 }, { target := 547, numerator := 8273019394009674056969748480 }, { target := 548, numerator := 259772808971903765388850102272 }, { target := 549, numerator := 8273019394009674056969748480 }, { target := 550, numerator := 253154393456696026143274303488 }, { target := 551, numerator := 143950537455768328591273623552 }, { target := 552, numerator := 259772808971903765388850102272 }, { target := 553, numerator := 4055434106943542222726570704896 }, { target := 554, numerator := 158841972364985741893819170816 }, { target := 555, numerator := 264736620608309569823031951360 }, { target := 556, numerator := 253154393456696026143274303488 }, { target := 557, numerator := 8273019394009674056969748480 }, { target := 558, numerator := 158841972364985741893819170816 }, { target := 559, numerator := 8273019394009674056969748480 }, { target := 560, numerator := 254808997335497960954668253184 }, { target := 561, numerator := 143950537455768328591273623552 }, { target := 562, numerator := 9927623272811608868363698176 }, { target := 579, numerator := 795624305033877825603502080 }, { target := 580, numerator := 21216648134236742016093388800 }, { target := 581, numerator := 20288419778363884552889303040 }, { target := 582, numerator := 663020254194898188002918400 }, { target := 583, numerator := 20818835981719803103291637760 }, { target := 584, numerator := 663020254194898188002918400 }, { target := 585, numerator := 20288419778363884552889303040 }, { target := 586, numerator := 11536552422991228471250780160 }, { target := 587, numerator := 20818835981719803103291637760 }, { target := 588, numerator := 325012528606339091759030599680 }, { target := 589, numerator := 12729988880542045209656033280 }, { target := 590, numerator := 21216648134236742016093388800 }, { target := 591, numerator := 20288419778363884552889303040 }, { target := 592, numerator := 663020254194898188002918400 }, { target := 593, numerator := 12729988880542045209656033280 }, { target := 594, numerator := 663020254194898188002918400 }, { target := 595, numerator := 20421023829202864190489886720 }, { target := 596, numerator := 11536552422991228471250780160 }, { target := 597, numerator := 795624305033877825603502080 }, { target := 640, numerator := 371291342349142985281634304 }, { target := 641, numerator := 9901102462643812940843581440 }, { target := 642, numerator := 9467929229903146124681674752 }, { target := 643, numerator := 309409451957619154401361920 }, { target := 644, numerator := 9715456791469241448202764288 }, { target := 645, numerator := 309409451957619154401361920 }, { target := 646, numerator := 9467929229903146124681674752 }, { target := 647, numerator := 5383724464062573286583697408 }, { target := 648, numerator := 9715456791469241448202764288 }, { target := 649, numerator := 151672513349624909487547613184 }, { target := 650, numerator := 5940661477586287764506148864 }, { target := 651, numerator := 9901102462643812940843581440 }, { target := 652, numerator := 9467929229903146124681674752 }, { target := 653, numerator := 309409451957619154401361920 }, { target := 654, numerator := 5940661477586287764506148864 }, { target := 655, numerator := 309409451957619154401361920 }, { target := 656, numerator := 9529811120294669955561947136 }, { target := 657, numerator := 5383724464062573286583697408 }, { target := 658, numerator := 371291342349142985281634304 }]

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
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 675, numerator := 804464575089809801443540992 }, { target := 676, numerator := 21452388669061594705161093120 }, { target := 677, numerator := 20513846664790149936810295296 }, { target := 678, numerator := 670387145908174834536284160 }, { target := 679, numerator := 21050156381516689804439322624 }, { target := 680, numerator := 670387145908174834536284160 }, { target := 681, numerator := 20513846664790149936810295296 }, { target := 682, numerator := 11664736338802242120931344384 }, { target := 683, numerator := 21050156381516689804439322624 }, { target := 684, numerator := 328623778924187303889686495232 }, { target := 685, numerator := 12871433201436956823096655872 }, { target := 686, numerator := 21452388669061594705161093120 }, { target := 687, numerator := 20513846664790149936810295296 }, { target := 688, numerator := 670387145908174834536284160 }, { target := 689, numerator := 12871433201436956823096655872 }, { target := 690, numerator := 670387145908174834536284160 }, { target := 691, numerator := 20647924093971784903717552128 }, { target := 692, numerator := 11664736338802242120931344384 }, { target := 693, numerator := 804464575089809801443540992 }, { target := 776, numerator := 30940945195761915440136192 }, { target := 777, numerator := 825091871886984411736965120 }, { target := 778, numerator := 788994102491928843723472896 }, { target := 779, numerator := 25784120996468262866780160 }, { target := 780, numerator := 809621399289103454016897024 }, { target := 781, numerator := 25784120996468262866780160 }, { target := 782, numerator := 788994102491928843723472896 }, { target := 783, numerator := 448643705338547773881974784 }, { target := 784, numerator := 809621399289103454016897024 }, { target := 785, numerator := 12639376112468742457295634432 }, { target := 786, numerator := 495055123132190647042179072 }, { target := 787, numerator := 825091871886984411736965120 }, { target := 788, numerator := 788994102491928843723472896 }, { target := 789, numerator := 25784120996468262866780160 }, { target := 790, numerator := 495055123132190647042179072 }, { target := 791, numerator := 25784120996468262866780160 }, { target := 792, numerator := 794150926691222496296828928 }, { target := 793, numerator := 448643705338547773881974784 }, { target := 794, numerator := 30940945195761915440136192 }, { target := 811, numerator := 795624305033877825603502080 }, { target := 812, numerator := 21216648134236742016093388800 }, { target := 813, numerator := 20288419778363884552889303040 }, { target := 814, numerator := 663020254194898188002918400 }, { target := 815, numerator := 20818835981719803103291637760 }, { target := 816, numerator := 663020254194898188002918400 }, { target := 817, numerator := 20288419778363884552889303040 }, { target := 818, numerator := 11536552422991228471250780160 }, { target := 819, numerator := 20818835981719803103291637760 }, { target := 820, numerator := 325012528606339091759030599680 }, { target := 821, numerator := 12729988880542045209656033280 }, { target := 822, numerator := 21216648134236742016093388800 }, { target := 823, numerator := 20288419778363884552889303040 }, { target := 824, numerator := 663020254194898188002918400 }, { target := 825, numerator := 12729988880542045209656033280 }, { target := 826, numerator := 663020254194898188002918400 }, { target := 827, numerator := 20421023829202864190489886720 }, { target := 828, numerator := 11536552422991228471250780160 }, { target := 829, numerator := 795624305033877825603502080 }]

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

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left15.expected,
    Slot20.Left16.expected,
    Slot20.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 846, numerator := 30940945195761915440136192 }, { target := 847, numerator := 825091871886984411736965120 }, { target := 848, numerator := 788994102491928843723472896 }, { target := 849, numerator := 25784120996468262866780160 }, { target := 850, numerator := 809621399289103454016897024 }, { target := 851, numerator := 25784120996468262866780160 }, { target := 852, numerator := 788994102491928843723472896 }, { target := 853, numerator := 448643705338547773881974784 }, { target := 854, numerator := 809621399289103454016897024 }, { target := 855, numerator := 12639376112468742457295634432 }, { target := 856, numerator := 495055123132190647042179072 }, { target := 857, numerator := 825091871886984411736965120 }, { target := 858, numerator := 788994102491928843723472896 }, { target := 859, numerator := 25784120996468262866780160 }, { target := 860, numerator := 495055123132190647042179072 }, { target := 861, numerator := 25784120996468262866780160 }, { target := 862, numerator := 794150926691222496296828928 }, { target := 863, numerator := 448643705338547773881974784 }, { target := 864, numerator := 30940945195761915440136192 }, { target := 907, numerator := 804464575089809801443540992 }, { target := 908, numerator := 21452388669061594705161093120 }, { target := 909, numerator := 20513846664790149936810295296 }, { target := 910, numerator := 670387145908174834536284160 }, { target := 911, numerator := 21050156381516689804439322624 }, { target := 912, numerator := 670387145908174834536284160 }, { target := 913, numerator := 20513846664790149936810295296 }, { target := 914, numerator := 11664736338802242120931344384 }, { target := 915, numerator := 21050156381516689804439322624 }, { target := 916, numerator := 328623778924187303889686495232 }, { target := 917, numerator := 12871433201436956823096655872 }, { target := 918, numerator := 21452388669061594705161093120 }, { target := 919, numerator := 20513846664790149936810295296 }, { target := 920, numerator := 670387145908174834536284160 }, { target := 921, numerator := 12871433201436956823096655872 }, { target := 922, numerator := 670387145908174834536284160 }, { target := 923, numerator := 20647924093971784903717552128 }, { target := 924, numerator := 11664736338802242120931344384 }, { target := 925, numerator := 804464575089809801443540992 }, { target := 942, numerator := 804464575089809801443540992 }, { target := 943, numerator := 21452388669061594705161093120 }, { target := 944, numerator := 20513846664790149936810295296 }, { target := 945, numerator := 670387145908174834536284160 }, { target := 946, numerator := 21050156381516689804439322624 }, { target := 947, numerator := 670387145908174834536284160 }, { target := 948, numerator := 20513846664790149936810295296 }, { target := 949, numerator := 11664736338802242120931344384 }, { target := 950, numerator := 21050156381516689804439322624 }, { target := 951, numerator := 328623778924187303889686495232 }, { target := 952, numerator := 12871433201436956823096655872 }, { target := 953, numerator := 21452388669061594705161093120 }, { target := 954, numerator := 20513846664790149936810295296 }, { target := 955, numerator := 670387145908174834536284160 }, { target := 956, numerator := 12871433201436956823096655872 }, { target := 957, numerator := 670387145908174834536284160 }, { target := 958, numerator := 20647924093971784903717552128 }, { target := 959, numerator := 11664736338802242120931344384 }, { target := 960, numerator := 804464575089809801443540992 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk19

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
