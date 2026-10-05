import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 39; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent1

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
    Slot1.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 219, numerator := 25264660683352601893273600 }, { target := 220, numerator := 424446299480323711806996480 }, { target := 221, numerator := 919633648874034708915159040 }, { target := 222, numerator := 30317592820023122271928320 }, { target := 223, numerator := 485081485120369956350853120 }, { target := 224, numerator := 35370524956693642650583040 }, { target := 225, numerator := 919633648874034708915159040 }, { target := 226, numerator := 919633648874034708915159040 }, { target := 227, numerator := 485081485120369956350853120 }, { target := 228, numerator := 11348885578961988770458501120 }, { target := 229, numerator := 909527784600693668157849600 }, { target := 230, numerator := 424446299480323711806996480 }, { target := 231, numerator := 919633648874034708915159040 }, { target := 232, numerator := 35370524956693642650583040 }, { target := 233, numerator := 909527784600693668157849600 }, { target := 234, numerator := 35370524956693642650583040 }, { target := 235, numerator := 919633648874034708915159040 }, { target := 236, numerator := 919633648874034708915159040 }, { target := 237, numerator := 30317592820023122271928320 }, { target := 359, numerator := 23092372101232565094973440 }, { target := 360, numerator := 387951851300707093595553792 }, { target := 361, numerator := 840562344484865369457033216 }, { target := 362, numerator := 27710846521479078113968128 }, { target := 363, numerator := 443373544343665249823490048 }, { target := 364, numerator := 32329320941725591132962816 }, { target := 365, numerator := 840562344484865369457033216 }, { target := 366, numerator := 840562344484865369457033216 }, { target := 367, numerator := 443373544343665249823490048 }, { target := 368, numerator := 10373093547873668240662069248 }, { target := 369, numerator := 831325395644372343419043840 }, { target := 370, numerator := 387951851300707093595553792 }, { target := 371, numerator := 840562344484865369457033216 }, { target := 372, numerator := 32329320941725591132962816 }, { target := 373, numerator := 831325395644372343419043840 }, { target := 374, numerator := 32329320941725591132962816 }, { target := 375, numerator := 840562344484865369457033216 }, { target := 376, numerator := 840562344484865369457033216 }, { target := 377, numerator := 27710846521479078113968128 }, { target := 434, numerator := 25264660683352601893273600 }, { target := 435, numerator := 424446299480323711806996480 }, { target := 436, numerator := 919633648874034708915159040 }, { target := 437, numerator := 30317592820023122271928320 }, { target := 438, numerator := 485081485120369956350853120 }, { target := 439, numerator := 35370524956693642650583040 }, { target := 440, numerator := 919633648874034708915159040 }, { target := 441, numerator := 919633648874034708915159040 }, { target := 442, numerator := 485081485120369956350853120 }, { target := 443, numerator := 11348885578961988770458501120 }, { target := 444, numerator := 909527784600693668157849600 }, { target := 445, numerator := 424446299480323711806996480 }, { target := 446, numerator := 919633648874034708915159040 }, { target := 447, numerator := 35370524956693642650583040 }, { target := 448, numerator := 909527784600693668157849600 }, { target := 449, numerator := 35370524956693642650583040 }, { target := 450, numerator := 919633648874034708915159040 }, { target := 451, numerator := 919633648874034708915159040 }, { target := 452, numerator := 30317592820023122271928320 }, { target := 488, numerator := 3133309050849941077868150784 }, { target := 490, numerator := 115708934720546565312447774720 }, { target := 493, numerator := 115708906386347668094576492544 }, { target := 500, numerator := 3133337385048838295739432960 }]

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
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 297936384188825038089093120 }, { target := 62, numerator := 231728298813530585180405760 }, { target := 63, numerator := 264832341501177811634749440 }, { target := 64, numerator := 311178001263883928670830592 }, { target := 65, numerator := 3674548738328842136432148480 }, { target := 66, numerator := 8262769054836747723004182528 }, { target := 67, numerator := 231728298813530585180405760 }, { target := 68, numerator := 3674548738328842136432148480 }, { target := 69, numerator := 264832341501177811634749440 }, { target := 70, numerator := 258211532963648366343880704 }, { target := 71, numerator := 258211532963648366343880704 }, { target := 72, numerator := 258211532963648366343880704 }, { target := 73, numerator := 8262769054836747723004182528 }, { target := 74, numerator := 258211532963648366343880704 }, { target := 75, numerator := 297936384188825038089093120 }, { target := 76, numerator := 311178001263883928670830592 }, { target := 219, numerator := 41386819855869570652831744 }, { target := 220, numerator := 6607289619774098361452331008 }, { target := 222, numerator := 65930814357370884598978838528 }, { target := 230, numerator := 6607289619774098361452331008 }, { target := 237, numerator := 41382097489386701007618048 }, { target := 359, numerator := 41386819855869570652831744 }, { target := 360, numerator := 6607289619774098361452331008 }, { target := 362, numerator := 65930814357370884598978838528 }, { target := 370, numerator := 6607289619774098361452331008 }, { target := 377, numerator := 41382097489386701007618048 }, { target := 434, numerator := 41386819855869570652831744 }, { target := 435, numerator := 6607289619774098361452331008 }, { target := 437, numerator := 65930814357370884598978838528 }, { target := 445, numerator := 6607289619774098361452331008 }, { target := 452, numerator := 41382097489386701007618048 }, { target := 469, numerator := 64479191957102135747805184 }, { target := 470, numerator := 6995241471074805455047884800 }, { target := 471, numerator := 840562344484865369457033216 }, { target := 472, numerator := 65958525203892363677092806656 }, { target := 473, numerator := 443373544343665249823490048 }, { target := 474, numerator := 32329320941725591132962816 }, { target := 475, numerator := 840562344484865369457033216 }, { target := 476, numerator := 840562344484865369457033216 }, { target := 477, numerator := 443373544343665249823490048 }, { target := 478, numerator := 10373093547873668240662069248 }, { target := 479, numerator := 831325395644372343419043840 }, { target := 480, numerator := 6995241471074805455047884800 }, { target := 481, numerator := 840562344484865369457033216 }, { target := 482, numerator := 32329320941725591132962816 }, { target := 483, numerator := 831325395644372343419043840 }, { target := 484, numerator := 32329320941725591132962816 }, { target := 485, numerator := 840562344484865369457033216 }, { target := 486, numerator := 840562344484865369457033216 }, { target := 487, numerator := 69092944010865779121586176 }]

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
    Slot3.Left2.expected,
    Slot3.Left7.expected,
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
  [{ target := 61, numerator := 24664636521338023666778112 }, { target := 62, numerator := 2074030586329658223623143424 }, { target := 67, numerator := 2074030085961725224251555840 }, { target := 75, numerator := 24665136889271023038365696 }, { target := 132, numerator := 590360009639768179379011584 }, { target := 133, numerator := 49642925646987303288012013568 }, { target := 138, numerator := 49642913670438713432085626880 }, { target := 146, numerator := 590371986188358035305398272 }, { target := 177, numerator := 3327410149188049790042112000 }, { target := 178, numerator := 39376375154856815087782461440 }, { target := 179, numerator := 2565185415211095063978311680 }, { target := 180, numerator := 3014092862873036700174516224 }, { target := 181, numerator := 35591947636053944012699074560 }, { target := 182, numerator := 80033784954586165996123324416 }, { target := 183, numerator := 39376366196656724292581457920 }, { target := 184, numerator := 35591947636053944012699074560 }, { target := 185, numerator := 2565185415211095063978311680 }, { target := 186, numerator := 2501055779830817687378853888 }, { target := 187, numerator := 2501055779830817687378853888 }, { target := 188, numerator := 2501055779830817687378853888 }, { target := 189, numerator := 80033784954586165996123324416 }, { target := 190, numerator := 2501055779830817687378853888 }, { target := 191, numerator := 3327419107388140585243115520 }, { target := 192, numerator := 3014092862873036700174516224 }, { target := 203, numerator := 512387932894893136819519488 }, { target := 204, numerator := 43086312825687093419784011776 }, { target := 209, numerator := 43086302430946807884451676160 }, { target := 217, numerator := 512398327635178672151855104 }, { target := 272, numerator := 24664636521338023666778112 }, { target := 273, numerator := 2074030586329658223623143424 }, { target := 278, numerator := 2074030085961725224251555840 }, { target := 286, numerator := 24665136889271023038365696 }, { target := 317, numerator := 511592299458720942507687936 }, { target := 318, numerator := 43019408613224846380312297472 }, { target := 323, numerator := 43019398234625461909475819520 }, { target := 331, numerator := 511602678058105413344165888 }, { target := 343, numerator := 513979199767237525443182592 }, { target := 344, numerator := 43220121250611587498727440384 }, { target := 349, numerator := 43220110823589499834403389440 }, { target := 357, numerator := 513989626789325189767233536 }, { target := 392, numerator := 322601020710163061755871232 }, { target := 393, numerator := 2305758885143188808803549184 }, { target := 394, numerator := 264832341501177811634749440 }, { target := 395, numerator := 311178001263883928670830592 }, { target := 396, numerator := 3674548738328842136432148480 }, { target := 397, numerator := 8262769054836747723004182528 }, { target := 398, numerator := 2305758384775255809431961600 }, { target := 399, numerator := 3674548738328842136432148480 }, { target := 400, numerator := 264832341501177811634749440 }, { target := 401, numerator := 258211532963648366343880704 }, { target := 402, numerator := 258211532963648366343880704 }, { target := 403, numerator := 258211532963648366343880704 }, { target := 404, numerator := 8262769054836747723004182528 }, { target := 405, numerator := 258211532963648366343880704 }, { target := 406, numerator := 322601521078096061127458816 }, { target := 407, numerator := 311178001263883928670830592 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 322601020710163061755871232 }, { target := 18, numerator := 590360009639768179379011584 }, { target := 19, numerator := 3327410149188049790042112000 }, { target := 20, numerator := 512387932894893136819519488 }, { target := 21, numerator := 24664636521338023666778112 }, { target := 22, numerator := 511592299458720942507687936 }, { target := 23, numerator := 513979199767237525443182592 }, { target := 24, numerator := 322601020710163061755871232 }, { target := 25, numerator := 590360009639768179379011584 }, { target := 26, numerator := 24664636521338023666778112 }, { target := 37, numerator := 2305758885143188808803549184 }, { target := 38, numerator := 49642925646987303288012013568 }, { target := 39, numerator := 39376375154856815087782461440 }, { target := 40, numerator := 43086312825687093419784011776 }, { target := 41, numerator := 2074030586329658223623143424 }, { target := 42, numerator := 43019408613224846380312297472 }, { target := 43, numerator := 43220121250611587498727440384 }, { target := 44, numerator := 2305758885143188808803549184 }, { target := 45, numerator := 49642925646987303288012013568 }, { target := 46, numerator := 2074030586329658223623143424 }, { target := 51, numerator := 264832341501177811634749440 }, { target := 53, numerator := 2565185415211095063978311680 }, { target := 58, numerator := 264832341501177811634749440 }, { target := 88, numerator := 311178001263883928670830592 }, { target := 90, numerator := 3014092862873036700174516224 }, { target := 95, numerator := 311178001263883928670830592 }, { target := 108, numerator := 3674548738328842136432148480 }, { target := 110, numerator := 35591947636053944012699074560 }, { target := 115, numerator := 3674548738328842136432148480 }, { target := 153, numerator := 2074030085961725224251555840 }, { target := 154, numerator := 49642913670438713432085626880 }, { target := 155, numerator := 37131828958347016111600435200 }, { target := 156, numerator := 43086302430946807884451676160 }, { target := 157, numerator := 2074030085961725224251555840 }, { target := 158, numerator := 43019398234625461909475819520 }, { target := 159, numerator := 43220110823589499834403389440 }, { target := 160, numerator := 2074030085961725224251555840 }, { target := 161, numerator := 49642913670438713432085626880 }, { target := 162, numerator := 2074030085961725224251555840 }, { target := 382, numerator := 24665136889271023038365696 }, { target := 383, numerator := 590371986188358035305398272 }, { target := 384, numerator := 441585515275658638267514880 }, { target := 385, numerator := 512398327635178672151855104 }, { target := 386, numerator := 24665136889271023038365696 }, { target := 387, numerator := 511602678058105413344165888 }, { target := 388, numerator := 513989626789325189767233536 }, { target := 389, numerator := 24665136889271023038365696 }, { target := 390, numerator := 590371986188358035305398272 }, { target := 391, numerator := 24665136889271023038365696 }, { target := 418, numerator := 590360009639768179379011584 }, { target := 419, numerator := 49642925646987303288012013568 }, { target := 424, numerator := 49642913670438713432085626880 }, { target := 432, numerator := 590371986188358035305398272 }, { target := 453, numerator := 24664636521338023666778112 }, { target := 454, numerator := 2074030586329658223623143424 }, { target := 459, numerator := 2074030085961725224251555840 }, { target := 467, numerator := 24665136889271023038365696 }]

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
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 66651480539222172546105344 }, { target := 3, numerator := 64479191957102135747805184 }, { target := 4, numerator := 66651480539222172546105344 }, { target := 5, numerator := 64479191957102135747805184 }, { target := 8, numerator := 7031735919254422073259327488 }, { target := 9, numerator := 6995241471074805455047884800 }, { target := 10, numerator := 7031735919254422073259327488 }, { target := 11, numerator := 6995241471074805455047884800 }, { target := 28, numerator := 65930814357370884598978838528 }, { target := 29, numerator := 65930814357370884598978838528 }, { target := 30, numerator := 65930814357370884598978838528 }, { target := 31, numerator := 65930814357370884598978838528 }, { target := 122, numerator := 8262769054836747723004182528 }, { target := 124, numerator := 80033784954586165996123324416 }, { target := 129, numerator := 8262769054836747723004182528 }, { target := 149, numerator := 6607289619774098361452331008 }, { target := 150, numerator := 6607289619774098361452331008 }, { target := 151, numerator := 6607289619774098361452331008 }, { target := 152, numerator := 6607289619774098361452331008 }, { target := 153, numerator := 231728298813530585180405760 }, { target := 155, numerator := 2244537238309708180981022720 }, { target := 160, numerator := 231728298813530585180405760 }, { target := 167, numerator := 3674548738328842136432148480 }, { target := 169, numerator := 35591947636053944012699074560 }, { target := 174, numerator := 3674548738328842136432148480 }, { target := 193, numerator := 264832341501177811634749440 }, { target := 195, numerator := 2565185415211095063978311680 }, { target := 200, numerator := 264832341501177811634749440 }, { target := 248, numerator := 258211532963648366343880704 }, { target := 250, numerator := 2501055779830817687378853888 }, { target := 255, numerator := 258211532963648366343880704 }, { target := 262, numerator := 258211532963648366343880704 }, { target := 264, numerator := 2501055779830817687378853888 }, { target := 269, numerator := 258211532963648366343880704 }, { target := 293, numerator := 258211532963648366343880704 }, { target := 295, numerator := 2501055779830817687378853888 }, { target := 300, numerator := 258211532963648366343880704 }, { target := 307, numerator := 8262769054836747723004182528 }, { target := 309, numerator := 80033784954586165996123324416 }, { target := 314, numerator := 8262769054836747723004182528 }, { target := 333, numerator := 258211532963648366343880704 }, { target := 335, numerator := 2501055779830817687378853888 }, { target := 340, numerator := 258211532963648366343880704 }, { target := 378, numerator := 41382097489386701007618048 }, { target := 379, numerator := 41382097489386701007618048 }, { target := 380, numerator := 41382097489386701007618048 }, { target := 381, numerator := 41382097489386701007618048 }, { target := 382, numerator := 297936384188825038089093120 }, { target := 384, numerator := 2885833592112481946975600640 }, { target := 389, numerator := 297936384188825038089093120 }, { target := 408, numerator := 311178001263883928670830592 }, { target := 410, numerator := 3014092862873036700174516224 }, { target := 415, numerator := 311178001263883928670830592 }]

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
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected,
    Slot8.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 13, numerator := 919633648874034708915159040 }, { target := 14, numerator := 840562344484865369457033216 }, { target := 15, numerator := 919633648874034708915159040 }, { target := 16, numerator := 840562344484865369457033216 }, { target := 28, numerator := 30317592820023122271928320 }, { target := 29, numerator := 27710846521479078113968128 }, { target := 30, numerator := 30317592820023122271928320 }, { target := 31, numerator := 27710846521479078113968128 }, { target := 33, numerator := 485081485120369956350853120 }, { target := 34, numerator := 443373544343665249823490048 }, { target := 35, numerator := 485081485120369956350853120 }, { target := 36, numerator := 443373544343665249823490048 }, { target := 47, numerator := 35370524956693642650583040 }, { target := 48, numerator := 32329320941725591132962816 }, { target := 49, numerator := 35370524956693642650583040 }, { target := 50, numerator := 32329320941725591132962816 }, { target := 79, numerator := 919633648874034708915159040 }, { target := 80, numerator := 840562344484865369457033216 }, { target := 81, numerator := 919633648874034708915159040 }, { target := 82, numerator := 840562344484865369457033216 }, { target := 84, numerator := 919633648874034708915159040 }, { target := 85, numerator := 840562344484865369457033216 }, { target := 86, numerator := 919633648874034708915159040 }, { target := 87, numerator := 840562344484865369457033216 }, { target := 99, numerator := 485081485120369956350853120 }, { target := 100, numerator := 443373544343665249823490048 }, { target := 101, numerator := 485081485120369956350853120 }, { target := 102, numerator := 443373544343665249823490048 }, { target := 104, numerator := 11348885578961988770458501120 }, { target := 105, numerator := 10373093547873668240662069248 }, { target := 106, numerator := 11348885578961988770458501120 }, { target := 107, numerator := 10373093547873668240662069248 }, { target := 118, numerator := 909527784600693668157849600 }, { target := 119, numerator := 831325395644372343419043840 }, { target := 120, numerator := 909527784600693668157849600 }, { target := 121, numerator := 831325395644372343419043840 }, { target := 149, numerator := 424446299480323711806996480 }, { target := 150, numerator := 387951851300707093595553792 }, { target := 151, numerator := 424446299480323711806996480 }, { target := 152, numerator := 387951851300707093595553792 }, { target := 163, numerator := 919633648874034708915159040 }, { target := 164, numerator := 840562344484865369457033216 }, { target := 165, numerator := 919633648874034708915159040 }, { target := 166, numerator := 840562344484865369457033216 }, { target := 239, numerator := 35370524956693642650583040 }, { target := 240, numerator := 32329320941725591132962816 }, { target := 241, numerator := 35370524956693642650583040 }, { target := 242, numerator := 32329320941725591132962816 }, { target := 244, numerator := 909527784600693668157849600 }, { target := 245, numerator := 831325395644372343419043840 }, { target := 246, numerator := 909527784600693668157849600 }, { target := 247, numerator := 831325395644372343419043840 }, { target := 258, numerator := 35370524956693642650583040 }, { target := 259, numerator := 32329320941725591132962816 }, { target := 260, numerator := 35370524956693642650583040 }, { target := 261, numerator := 32329320941725591132962816 }, { target := 289, numerator := 919633648874034708915159040 }, { target := 290, numerator := 840562344484865369457033216 }, { target := 291, numerator := 919633648874034708915159040 }, { target := 292, numerator := 840562344484865369457033216 }, { target := 303, numerator := 919633648874034708915159040 }, { target := 304, numerator := 840562344484865369457033216 }, { target := 305, numerator := 919633648874034708915159040 }, { target := 306, numerator := 840562344484865369457033216 }]

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
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3133309050849941077868150784 }, { target := 6, numerator := 115708934720546565312447774720 }, { target := 27, numerator := 115708906386347668094576492544 }, { target := 148, numerator := 3133337385048838295739432960 }, { target := 378, numerator := 30317592820023122271928320 }, { target := 379, numerator := 27710846521479078113968128 }, { target := 380, numerator := 30317592820023122271928320 }, { target := 381, numerator := 27710846521479078113968128 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent1
