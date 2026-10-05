import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 59; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent1

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
  [{ target := 411, numerator := 174765338798039830068461568 }, { target := 412, numerator := 199038302519989806466859008 }, { target := 413, numerator := 155346967820479848949743616 }, { target := 414, numerator := 2082620287343307974982500352 }, { target := 415, numerator := 184474524286819820627820544 }, { target := 416, numerator := 155346967820479848949743616 }, { target := 417, numerator := 184474524286819820627820544 }, { target := 418, numerator := 179619931542429825348141056 }, { target := 419, numerator := 6786720656657213400991924224 }, { target := 420, numerator := 179619931542429825348141056 }, { target := 421, numerator := 2082620287343307974982500352 }, { target := 422, numerator := 6786720656657213400991924224 }, { target := 423, numerator := 174765338798039830068461568 }, { target := 424, numerator := 179619931542429825348141056 }, { target := 425, numerator := 179619931542429825348141056 }, { target := 426, numerator := 199038302519989806466859008 }, { target := 627, numerator := 174255323217889908385382400 }, { target := 628, numerator := 198457451442596840105574400 }, { target := 629, numerator := 154893620638124363009228800 }, { target := 630, numerator := 2076542601679854741592473600 }, { target := 631, numerator := 183936174507772681073459200 }, { target := 632, numerator := 154893620638124363009228800 }, { target := 633, numerator := 183936174507772681073459200 }, { target := 634, numerator := 179095748862831294729420800 }, { target := 635, numerator := 6766915051628058108965683200 }, { target := 636, numerator := 179095748862831294729420800 }, { target := 637, numerator := 2076542601679854741592473600 }, { target := 638, numerator := 6766915051628058108965683200 }, { target := 639, numerator := 174255323217889908385382400 }, { target := 640, numerator := 179095748862831294729420800 }, { target := 641, numerator := 179095748862831294729420800 }, { target := 642, numerator := 198457451442596840105574400 }, { target := 723, numerator := 173065286864206757791531008 }, { target := 724, numerator := 197102132262013251929243648 }, { target := 725, numerator := 153835810545961562481360896 }, { target := 726, numerator := 2062361335131797197015744512 }, { target := 727, numerator := 182680025023329355446616064 }, { target := 728, numerator := 153835810545961562481360896 }, { target := 729, numerator := 182680025023329355446616064 }, { target := 730, numerator := 177872655943768056619073536 }, { target := 731, numerator := 6720701973226695760904454144 }, { target := 732, numerator := 177872655943768056619073536 }, { target := 733, numerator := 2062361335131797197015744512 }, { target := 734, numerator := 6720701973226695760904454144 }, { target := 735, numerator := 173065286864206757791531008 }, { target := 736, numerator := 177872655943768056619073536 }, { target := 737, numerator := 177872655943768056619073536 }, { target := 738, numerator := 197102132262013251929243648 }, { target := 758, numerator := 174255323217889908385382400 }, { target := 759, numerator := 198457451442596840105574400 }, { target := 760, numerator := 154893620638124363009228800 }, { target := 761, numerator := 2076542601679854741592473600 }, { target := 762, numerator := 183936174507772681073459200 }, { target := 763, numerator := 154893620638124363009228800 }, { target := 764, numerator := 183936174507772681073459200 }, { target := 765, numerator := 179095748862831294729420800 }, { target := 766, numerator := 6766915051628058108965683200 }, { target := 767, numerator := 179095748862831294729420800 }, { target := 768, numerator := 2076542601679854741592473600 }, { target := 769, numerator := 6766915051628058108965683200 }, { target := 770, numerator := 174255323217889908385382400 }, { target := 771, numerator := 179095748862831294729420800 }, { target := 772, numerator := 179095748862831294729420800 }, { target := 773, numerator := 198457451442596840105574400 }]

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
    Slot1.Left0.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left7.expected,
    Slot3.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 22127840276321486128545792 }, { target := 143, numerator := 331917604144822291928186880 }, { target := 144, numerator := 582699793943132468051705856 }, { target := 145, numerator := 22127840276321486128545792 }, { target := 146, numerator := 368797337938691435475763200 }, { target := 147, numerator := 22127840276321486128545792 }, { target := 148, numerator := 582699793943132468051705856 }, { target := 149, numerator := 579011820563745553696948224 }, { target := 150, numerator := 368797337938691435475763200 }, { target := 151, numerator := 8935959498254493481577742336 }, { target := 152, numerator := 571635873804971724987432960 }, { target := 153, numerator := 331917604144822291928186880 }, { target := 154, numerator := 582699793943132468051705856 }, { target := 155, numerator := 22127840276321486128545792 }, { target := 156, numerator := 571635873804971724987432960 }, { target := 157, numerator := 22127840276321486128545792 }, { target := 158, numerator := 582699793943132468051705856 }, { target := 159, numerator := 582699793943132468051705856 }, { target := 160, numerator := 22127840276321486128545792 }, { target := 357, numerator := 1000138124621307718498516992 }, { target := 358, numerator := 15002071869319615777477754880 }, { target := 359, numerator := 26336970615027769920460947456 }, { target := 360, numerator := 1000138124621307718498516992 }, { target := 361, numerator := 16668968743688461974975283200 }, { target := 362, numerator := 1000138124621307718498516992 }, { target := 363, numerator := 26336970615027769920460947456 }, { target := 364, numerator := 26170280927590885300711194624 }, { target := 365, numerator := 16668968743688461974975283200 }, { target := 366, numerator := 403889112659571433653651111936 }, { target := 367, numerator := 25836901552717116061211688960 }, { target := 368, numerator := 15002071869319615777477754880 }, { target := 369, numerator := 26336970615027769920460947456 }, { target := 370, numerator := 1000138124621307718498516992 }, { target := 371, numerator := 25836901552717116061211688960 }, { target := 372, numerator := 1000138124621307718498516992 }, { target := 373, numerator := 26336970615027769920460947456 }, { target := 374, numerator := 26336970615027769920460947456 }, { target := 375, numerator := 1000138124621307718498516992 }, { target := 411, numerator := 1237773575866859119905341440 }, { target := 413, numerator := 48279833898506455463116144640 }, { target := 416, numerator := 48279816189632144701946593280 }, { target := 423, numerator := 1237779478824962706961858560 }, { target := 669, numerator := 22245943249410402319073280 }, { target := 670, numerator := 333689148741156034786099200 }, { target := 671, numerator := 585809838901140594402263040 }, { target := 672, numerator := 22245943249410402319073280 }, { target := 673, numerator := 370765720823506705317888000 }, { target := 674, numerator := 22245943249410402319073280 }, { target := 675, numerator := 585809838901140594402263040 }, { target := 676, numerator := 582102181692905527349084160 }, { target := 677, numerator := 370765720823506705317888000 }, { target := 678, numerator := 8983653415553567469852426240 }, { target := 679, numerator := 574686867276435393242726400 }, { target := 680, numerator := 333689148741156034786099200 }, { target := 681, numerator := 585809838901140594402263040 }, { target := 682, numerator := 22245943249410402319073280 }, { target := 683, numerator := 574686867276435393242726400 }, { target := 684, numerator := 22245943249410402319073280 }, { target := 685, numerator := 585809838901140594402263040 }, { target := 686, numerator := 585809838901140594402263040 }, { target := 687, numerator := 22245943249410402319073280 }, { target := 774, numerator := 14016437068339462480190242816 }, { target := 777, numerator := 51195293099951895502808678400 }, { target := 779, numerator := 14016432345972979610545029120 }]

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
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 131590771187010771930316800 }, { target := 56, numerator := 98693078390258078947737600 }, { target := 57, numerator := 104176027189716861111500800 }, { target := 58, numerator := 134332245586740163012198400 }, { target := 59, numerator := 1798407206222480549714329600 }, { target := 60, numerator := 3144471136489611570918195200 }, { target := 61, numerator := 95951603990528687865856000 }, { target := 62, numerator := 1798407206222480549714329600 }, { target := 63, numerator := 101434552789987470029619200 }, { target := 64, numerator := 104176027189716861111500800 }, { target := 65, numerator := 104176027189716861111500800 }, { target := 66, numerator := 101434552789987470029619200 }, { target := 67, numerator := 3144471136489611570918195200 }, { target := 68, numerator := 101434552789987470029619200 }, { target := 69, numerator := 131590771187010771930316800 }, { target := 70, numerator := 134332245586740163012198400 }, { target := 100, numerator := 23079784965413869382428262400 }, { target := 101, numerator := 17309838724060402036821196800 }, { target := 102, numerator := 18271496430952646594422374400 }, { target := 103, numerator := 23560613818859991661228851200 }, { target := 104, numerator := 315423727860656214893186252800 }, { target := 105, numerator := 551510694902702253784275353600 }, { target := 106, numerator := 16829009870614279758020608000 }, { target := 107, numerator := 315423727860656214893186252800 }, { target := 108, numerator := 17790667577506524315621785600 }, { target := 109, numerator := 18271496430952646594422374400 }, { target := 110, numerator := 18271496430952646594422374400 }, { target := 111, numerator := 17790667577506524315621785600 }, { target := 112, numerator := 551510694902702253784275353600 }, { target := 113, numerator := 17790667577506524315621785600 }, { target := 114, numerator := 23079784965413869382428262400 }, { target := 115, numerator := 23560613818859991661228851200 }, { target := 315, numerator := 23079787732425480438861004800 }, { target := 316, numerator := 17309840799319110329145753600 }, { target := 317, numerator := 18271498621503505347431628800 }, { target := 318, numerator := 23560616643517677948003942400 }, { target := 319, numerator := 315423765676481565997767065600 }, { target := 320, numerator := 551510761022750542986949427200 }, { target := 321, numerator := 16829011888226912820002816000 }, { target := 322, numerator := 315423765676481565997767065600 }, { target := 323, numerator := 17790669710411307838288691200 }, { target := 324, numerator := 18271498621503505347431628800 }, { target := 325, numerator := 18271498621503505347431628800 }, { target := 326, numerator := 17790669710411307838288691200 }, { target := 327, numerator := 551510761022750542986949427200 }, { target := 328, numerator := 17790669710411307838288691200 }, { target := 329, numerator := 23079787732425480438861004800 }, { target := 330, numerator := 23560616643517677948003942400 }, { target := 627, numerator := 1237773575866859119905341440 }, { target := 629, numerator := 48279833898506455463116144640 }, { target := 632, numerator := 48279816189632144701946593280 }, { target := 639, numerator := 1237779478824962706961858560 }, { target := 723, numerator := 1237773575866859119905341440 }, { target := 725, numerator := 48279833898506455463116144640 }, { target := 728, numerator := 48279816189632144701946593280 }, { target := 735, numerator := 1237779478824962706961858560 }, { target := 758, numerator := 1237773575866859119905341440 }, { target := 760, numerator := 48279833898506455463116144640 }, { target := 763, numerator := 48279816189632144701946593280 }, { target := 770, numerator := 1237779478824962706961858560 }]

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
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 12785973273066227802046464 }, { target := 143, numerator := 1511219951942962915011723264 }, { target := 145, numerator := 14341176102428335121790664704 }, { target := 153, numerator := 1511220988419395556567154688 }, { target := 160, numerator := 12785973273066227802046464 }, { target := 282, numerator := 309750513808797970301190144 }, { target := 283, numerator := 36610522061585972553993682944 }, { target := 285, numerator := 347426556545925150853702877184 }, { target := 293, numerator := 36610547171063421386513973248 }, { target := 300, numerator := 309750513808797970301190144 }, { target := 357, numerator := 234684477173376890947239936 }, { target := 358, numerator := 27738198472759545117473243136 }, { target := 360, numerator := 263229974267152344654802845696 }, { target := 368, numerator := 27738217497117292635055194112 }, { target := 375, numerator := 234684477173376890947239936 }, { target := 392, numerator := 261493775971741562145079296 }, { target := 393, numerator := 30906885468768983487659114496 }, { target := 395, numerator := 293300182223856918297267142656 }, { target := 403, numerator := 30906906666383767189147615232 }, { target := 410, numerator := 261493775971741562145079296 }, { target := 498, numerator := 12785973273066227802046464 }, { target := 499, numerator := 1511219951942962915011723264 }, { target := 501, numerator := 14341176102428335121790664704 }, { target := 509, numerator := 1511220988419395556567154688 }, { target := 516, numerator := 12785973273066227802046464 }, { target := 573, numerator := 261493775971741562145079296 }, { target := 574, numerator := 30906885468768983487659114496 }, { target := 576, numerator := 293300182223856918297267142656 }, { target := 584, numerator := 30906906666383767189147615232 }, { target := 591, numerator := 261493775971741562145079296 }, { target := 608, numerator := 261081325220997490280497152 }, { target := 609, numerator := 30858136438061145974271639552 }, { target := 611, numerator := 292837563639907617164306153472 }, { target := 619, numerator := 30858157602241206042161577984 }, { target := 626, numerator := 261081325220997490280497152 }, { target := 653, numerator := 131588004175399715497574400 }, { target := 654, numerator := 98691003131549786623180800 }, { target := 655, numerator := 104173836638858108102246400 }, { target := 656, numerator := 134329420929053876237107200 }, { target := 657, numerator := 1798369390397129445133516800 }, { target := 658, numerator := 3144405016441322368244121600 }, { target := 659, numerator := 95949586377895625883648000 }, { target := 660, numerator := 1798369390397129445133516800 }, { target := 661, numerator := 101432419885203947362713600 }, { target := 662, numerator := 104173836638858108102246400 }, { target := 663, numerator := 104173836638858108102246400 }, { target := 664, numerator := 101432419885203947362713600 }, { target := 665, numerator := 3144405016441322368244121600 }, { target := 666, numerator := 101432419885203947362713600 }, { target := 667, numerator := 131588004175399715497574400 }, { target := 668, numerator := 134329420929053876237107200 }, { target := 669, numerator := 12785973273066227802046464 }, { target := 670, numerator := 1511219951942962915011723264 }, { target := 672, numerator := 14341176102428335121790664704 }, { target := 680, numerator := 1511220988419395556567154688 }, { target := 687, numerator := 12785973273066227802046464 }, { target := 704, numerator := 309750513808797970301190144 }, { target := 705, numerator := 36610522061585972553993682944 }, { target := 707, numerator := 347426556545925150853702877184 }, { target := 715, numerator := 36610547171063421386513973248 }, { target := 722, numerator := 309750513808797970301190144 }]

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
    Slot5.Left9.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 12785973273066227802046464 }, { target := 12, numerator := 309750513808797970301190144 }, { target := 13, numerator := 234684477173376890947239936 }, { target := 14, numerator := 261493775971741562145079296 }, { target := 15, numerator := 12785973273066227802046464 }, { target := 16, numerator := 261493775971741562145079296 }, { target := 17, numerator := 261081325220997490280497152 }, { target := 18, numerator := 12785973273066227802046464 }, { target := 19, numerator := 309750513808797970301190144 }, { target := 20, numerator := 12785973273066227802046464 }, { target := 31, numerator := 1511219951942962915011723264 }, { target := 32, numerator := 36610522061585972553993682944 }, { target := 33, numerator := 27738198472759545117473243136 }, { target := 34, numerator := 30906885468768983487659114496 }, { target := 35, numerator := 1511219951942962915011723264 }, { target := 36, numerator := 30906885468768983487659114496 }, { target := 37, numerator := 30858136438061145974271639552 }, { target := 38, numerator := 1511219951942962915011723264 }, { target := 39, numerator := 36610522061585972553993682944 }, { target := 40, numerator := 1511219951942962915011723264 }, { target := 55, numerator := 126327140339530341053104128 }, { target := 56, numerator := 22156593566797314607131131904 }, { target := 61, numerator := 22156596223128461221306564608 }, { target := 69, numerator := 126324484008383726877671424 }, { target := 76, numerator := 14341176102428335121790664704 }, { target := 77, numerator := 347426556545925150853702877184 }, { target := 78, numerator := 263229974267152344654802845696 }, { target := 79, numerator := 293300182223856918297267142656 }, { target := 80, numerator := 14341176102428335121790664704 }, { target := 81, numerator := 293300182223856918297267142656 }, { target := 82, numerator := 292837563639907617164306153472 }, { target := 83, numerator := 14341176102428335121790664704 }, { target := 84, numerator := 347426556545925150853702877184 }, { target := 85, numerator := 14341176102428335121790664704 }, { target := 100, numerator := 94745355254647755789828096 }, { target := 101, numerator := 16617445175097985955348348928 }, { target := 106, numerator := 16617447167346345915979923456 }, { target := 114, numerator := 94743363006287795158253568 }, { target := 305, numerator := 1511220988419395556567154688 }, { target := 306, numerator := 36610547171063421386513973248 }, { target := 307, numerator := 27738217497117292635055194112 }, { target := 308, numerator := 30906906666383767189147615232 }, { target := 309, numerator := 1511220988419395556567154688 }, { target := 310, numerator := 30906906666383767189147615232 }, { target := 311, numerator := 30858157602241206042161577984 }, { target := 312, numerator := 1511220988419395556567154688 }, { target := 313, numerator := 36610547171063421386513973248 }, { target := 314, numerator := 1511220988419395556567154688 }, { target := 643, numerator := 12785973273066227802046464 }, { target := 644, numerator := 309750513808797970301190144 }, { target := 645, numerator := 234684477173376890947239936 }, { target := 646, numerator := 261493775971741562145079296 }, { target := 647, numerator := 12785973273066227802046464 }, { target := 648, numerator := 261493775971741562145079296 }, { target := 649, numerator := 261081325220997490280497152 }, { target := 650, numerator := 12785973273066227802046464 }, { target := 651, numerator := 309750513808797970301190144 }, { target := 652, numerator := 12785973273066227802046464 }, { target := 739, numerator := 12785973273066227802046464 }, { target := 740, numerator := 1511219951942962915011723264 }, { target := 742, numerator := 14341176102428335121790664704 }, { target := 750, numerator := 1511220988419395556567154688 }, { target := 757, numerator := 12785973273066227802046464 }]

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
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot7.Left10.expected,
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
  [{ target := 2, numerator := 1237773575866859119905341440 }, { target := 3, numerator := 1237773575866859119905341440 }, { target := 4, numerator := 1237773575866859119905341440 }, { target := 5, numerator := 1237773575866859119905341440 }, { target := 22, numerator := 48279833898506455463116144640 }, { target := 23, numerator := 48279833898506455463116144640 }, { target := 24, numerator := 48279833898506455463116144640 }, { target := 25, numerator := 48279833898506455463116144640 }, { target := 126, numerator := 100008986102128186667040768 }, { target := 127, numerator := 17540636573714540730645479424 }, { target := 132, numerator := 17540638676643365133534363648 }, { target := 140, numerator := 100006883173303783778156544 }, { target := 195, numerator := 128958955763270556491710464 }, { target := 196, numerator := 22618189266105591994779697152 }, { target := 201, numerator := 22618191977776970830083784704 }, { target := 209, numerator := 128956244091891721187622912 }, { target := 240, numerator := 1726470917973581327725756416 }, { target := 241, numerator := 302806778746229966297458802688 }, { target := 246, numerator := 302806815049422303357856382976 }, { target := 254, numerator := 1726434614781244267328176128 }, { target := 266, numerator := 3018692291030027108081467392 }, { target := 267, numerator := 529450267106594163632904339456 }, { target := 272, numerator := 529450330581840521267471450112 }, { target := 280, numerator := 3018628815783669473514356736 }, { target := 315, numerator := 92113539830907540351221760 }, { target := 316, numerator := 16155849475789708567699783680 }, { target := 321, numerator := 16155851412697836307202703360 }, { target := 329, numerator := 92111602922779800848302080 }, { target := 341, numerator := 1726470917973581327725756416 }, { target := 342, numerator := 302806778746229966297458802688 }, { target := 347, numerator := 302806815049422303357856382976 }, { target := 355, numerator := 1726434614781244267328176128 }, { target := 376, numerator := 97377170678387971228434432 }, { target := 377, numerator := 17079040874406263342996914176 }, { target := 382, numerator := 17079042921994855524757143552 }, { target := 390, numerator := 97375123089795789468205056 }, { target := 456, numerator := 100008986102128186667040768 }, { target := 457, numerator := 17540636573714540730645479424 }, { target := 462, numerator := 17540638676643365133534363648 }, { target := 470, numerator := 100006883173303783778156544 }, { target := 482, numerator := 100008986102128186667040768 }, { target := 483, numerator := 17540636573714540730645479424 }, { target := 488, numerator := 17540638676643365133534363648 }, { target := 496, numerator := 100006883173303783778156544 }, { target := 531, numerator := 97377170678387971228434432 }, { target := 532, numerator := 17079040874406263342996914176 }, { target := 537, numerator := 17079042921994855524757143552 }, { target := 545, numerator := 97375123089795789468205056 }, { target := 557, numerator := 3018692291030027108081467392 }, { target := 558, numerator := 529450267106594163632904339456 }, { target := 563, numerator := 529450330581840521267471450112 }, { target := 571, numerator := 3018628815783669473514356736 }, { target := 592, numerator := 97377170678387971228434432 }, { target := 593, numerator := 17079040874406263342996914176 }, { target := 598, numerator := 17079042921994855524757143552 }, { target := 606, numerator := 97375123089795789468205056 }, { target := 653, numerator := 126327140339530341053104128 }, { target := 654, numerator := 22156593566797314607131131904 }, { target := 659, numerator := 22156596223128461221306564608 }, { target := 667, numerator := 126324484008383726877671424 }, { target := 688, numerator := 128958955763270556491710464 }, { target := 689, numerator := 22618189266105591994779697152 }, { target := 694, numerator := 22618191977776970830083784704 }, { target := 702, numerator := 128956244091891721187622912 }]

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
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
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
  [{ target := 11, numerator := 22127840276321486128545792 }, { target := 13, numerator := 1000138124621307718498516992 }, { target := 18, numerator := 22245943249410402319073280 }, { target := 31, numerator := 331917604144822291928186880 }, { target := 33, numerator := 15002071869319615777477754880 }, { target := 38, numerator := 333689148741156034786099200 }, { target := 45, numerator := 582699793943132468051705856 }, { target := 47, numerator := 26336970615027769920460947456 }, { target := 52, numerator := 585809838901140594402263040 }, { target := 72, numerator := 48279816189632144701946593280 }, { target := 73, numerator := 48279816189632144701946593280 }, { target := 74, numerator := 48279816189632144701946593280 }, { target := 75, numerator := 48279816189632144701946593280 }, { target := 76, numerator := 22127840276321486128545792 }, { target := 78, numerator := 1000138124621307718498516992 }, { target := 83, numerator := 22245943249410402319073280 }, { target := 90, numerator := 368797337938691435475763200 }, { target := 92, numerator := 16668968743688461974975283200 }, { target := 97, numerator := 370765720823506705317888000 }, { target := 116, numerator := 22127840276321486128545792 }, { target := 118, numerator := 1000138124621307718498516992 }, { target := 123, numerator := 22245943249410402319073280 }, { target := 171, numerator := 582699793943132468051705856 }, { target := 173, numerator := 26336970615027769920460947456 }, { target := 178, numerator := 585809838901140594402263040 }, { target := 185, numerator := 579011820563745553696948224 }, { target := 187, numerator := 26170280927590885300711194624 }, { target := 192, numerator := 582102181692905527349084160 }, { target := 216, numerator := 368797337938691435475763200 }, { target := 218, numerator := 16668968743688461974975283200 }, { target := 223, numerator := 370765720823506705317888000 }, { target := 230, numerator := 8935959498254493481577742336 }, { target := 232, numerator := 403889112659571433653651111936 }, { target := 237, numerator := 8983653415553567469852426240 }, { target := 256, numerator := 571635873804971724987432960 }, { target := 258, numerator := 25836901552717116061211688960 }, { target := 263, numerator := 574686867276435393242726400 }, { target := 301, numerator := 1237779478824962706961858560 }, { target := 302, numerator := 1237779478824962706961858560 }, { target := 303, numerator := 1237779478824962706961858560 }, { target := 304, numerator := 1237779478824962706961858560 }, { target := 305, numerator := 331917604144822291928186880 }, { target := 307, numerator := 15002071869319615777477754880 }, { target := 312, numerator := 333689148741156034786099200 }, { target := 331, numerator := 582699793943132468051705856 }, { target := 333, numerator := 26336970615027769920460947456 }, { target := 338, numerator := 585809838901140594402263040 }, { target := 432, numerator := 22127840276321486128545792 }, { target := 434, numerator := 1000138124621307718498516992 }, { target := 439, numerator := 22245943249410402319073280 }, { target := 446, numerator := 571635873804971724987432960 }, { target := 448, numerator := 25836901552717116061211688960 }, { target := 453, numerator := 574686867276435393242726400 }, { target := 472, numerator := 22127840276321486128545792 }, { target := 474, numerator := 1000138124621307718498516992 }, { target := 479, numerator := 22245943249410402319073280 }, { target := 521, numerator := 582699793943132468051705856 }, { target := 523, numerator := 26336970615027769920460947456 }, { target := 528, numerator := 585809838901140594402263040 }, { target := 547, numerator := 582699793943132468051705856 }, { target := 549, numerator := 26336970615027769920460947456 }, { target := 554, numerator := 585809838901140594402263040 }]

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
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14016437068339462480190242816 }, { target := 2, numerator := 174765338798039830068461568 }, { target := 3, numerator := 174255323217889908385382400 }, { target := 4, numerator := 173065286864206757791531008 }, { target := 5, numerator := 174255323217889908385382400 }, { target := 7, numerator := 199038302519989806466859008 }, { target := 8, numerator := 198457451442596840105574400 }, { target := 9, numerator := 197102132262013251929243648 }, { target := 10, numerator := 198457451442596840105574400 }, { target := 21, numerator := 51195293099951895502808678400 }, { target := 22, numerator := 155346967820479848949743616 }, { target := 23, numerator := 154893620638124363009228800 }, { target := 24, numerator := 153835810545961562481360896 }, { target := 25, numerator := 154893620638124363009228800 }, { target := 27, numerator := 2082620287343307974982500352 }, { target := 28, numerator := 2076542601679854741592473600 }, { target := 29, numerator := 2062361335131797197015744512 }, { target := 30, numerator := 2076542601679854741592473600 }, { target := 41, numerator := 184474524286819820627820544 }, { target := 42, numerator := 183936174507772681073459200 }, { target := 43, numerator := 182680025023329355446616064 }, { target := 44, numerator := 183936174507772681073459200 }, { target := 71, numerator := 14016432345972979610545029120 }, { target := 72, numerator := 155346967820479848949743616 }, { target := 73, numerator := 154893620638124363009228800 }, { target := 74, numerator := 153835810545961562481360896 }, { target := 75, numerator := 154893620638124363009228800 }, { target := 86, numerator := 184474524286819820627820544 }, { target := 87, numerator := 183936174507772681073459200 }, { target := 88, numerator := 182680025023329355446616064 }, { target := 89, numerator := 183936174507772681073459200 }, { target := 162, numerator := 179619931542429825348141056 }, { target := 163, numerator := 179095748862831294729420800 }, { target := 164, numerator := 177872655943768056619073536 }, { target := 165, numerator := 179095748862831294729420800 }, { target := 167, numerator := 6786720656657213400991924224 }, { target := 168, numerator := 6766915051628058108965683200 }, { target := 169, numerator := 6720701973226695760904454144 }, { target := 170, numerator := 6766915051628058108965683200 }, { target := 181, numerator := 179619931542429825348141056 }, { target := 182, numerator := 179095748862831294729420800 }, { target := 183, numerator := 177872655943768056619073536 }, { target := 184, numerator := 179095748862831294729420800 }, { target := 212, numerator := 2082620287343307974982500352 }, { target := 213, numerator := 2076542601679854741592473600 }, { target := 214, numerator := 2062361335131797197015744512 }, { target := 215, numerator := 2076542601679854741592473600 }, { target := 226, numerator := 6786720656657213400991924224 }, { target := 227, numerator := 6766915051628058108965683200 }, { target := 228, numerator := 6720701973226695760904454144 }, { target := 229, numerator := 6766915051628058108965683200 }, { target := 301, numerator := 174765338798039830068461568 }, { target := 302, numerator := 174255323217889908385382400 }, { target := 303, numerator := 173065286864206757791531008 }, { target := 304, numerator := 174255323217889908385382400 }, { target := 428, numerator := 179619931542429825348141056 }, { target := 429, numerator := 179095748862831294729420800 }, { target := 430, numerator := 177872655943768056619073536 }, { target := 431, numerator := 179095748862831294729420800 }, { target := 643, numerator := 22127840276321486128545792 }, { target := 645, numerator := 1000138124621307718498516992 }, { target := 650, numerator := 22245943249410402319073280 }]

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
    Slot11.Left14.expected,
    Slot11.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 442, numerator := 179619931542429825348141056 }, { target := 443, numerator := 179095748862831294729420800 }, { target := 444, numerator := 177872655943768056619073536 }, { target := 445, numerator := 179095748862831294729420800 }, { target := 517, numerator := 199038302519989806466859008 }, { target := 518, numerator := 198457451442596840105574400 }, { target := 519, numerator := 197102132262013251929243648 }, { target := 520, numerator := 198457451442596840105574400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent1
