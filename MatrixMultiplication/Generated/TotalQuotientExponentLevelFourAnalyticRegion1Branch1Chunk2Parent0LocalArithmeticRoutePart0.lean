import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 9; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 149906801632214017663565824 }, { target := 3, numerator := 149906801632214017663565824 }, { target := 4, numerator := 149906801632214017663565824 }, { target := 5, numerator := 149906801632214017663565824 }, { target := 7, numerator := 169249614746048084458864640 }, { target := 8, numerator := 169249614746048084458864640 }, { target := 9, numerator := 169249614746048084458864640 }, { target := 10, numerator := 169249614746048084458864640 }, { target := 22, numerator := 145071098353755500964741120 }, { target := 23, numerator := 145071098353755500964741120 }, { target := 24, numerator := 145071098353755500964741120 }, { target := 25, numerator := 145071098353755500964741120 }, { target := 27, numerator := 1910102794991114096035758080 }, { target := 28, numerator := 1910102794991114096035758080 }, { target := 29, numerator := 1910102794991114096035758080 }, { target := 30, numerator := 1910102794991114096035758080 }, { target := 41, numerator := 169249614746048084458864640 }, { target := 42, numerator := 169249614746048084458864640 }, { target := 43, numerator := 169249614746048084458864640 }, { target := 44, numerator := 169249614746048084458864640 }, { target := 72, numerator := 145071098353755500964741120 }, { target := 73, numerator := 145071098353755500964741120 }, { target := 74, numerator := 145071098353755500964741120 }, { target := 75, numerator := 145071098353755500964741120 }, { target := 86, numerator := 169249614746048084458864640 }, { target := 87, numerator := 169249614746048084458864640 }, { target := 88, numerator := 169249614746048084458864640 }, { target := 89, numerator := 169249614746048084458864640 }, { target := 162, numerator := 169249614746048084458864640 }, { target := 163, numerator := 169249614746048084458864640 }, { target := 164, numerator := 169249614746048084458864640 }, { target := 165, numerator := 169249614746048084458864640 }, { target := 167, numerator := 7016605457043307729994645504 }, { target := 168, numerator := 7016605457043307729994645504 }, { target := 169, numerator := 7016605457043307729994645504 }, { target := 170, numerator := 7016605457043307729994645504 }, { target := 181, numerator := 174085318024506601157689344 }, { target := 182, numerator := 174085318024506601157689344 }, { target := 183, numerator := 174085318024506601157689344 }, { target := 184, numerator := 174085318024506601157689344 }, { target := 212, numerator := 1910102794991114096035758080 }, { target := 213, numerator := 1910102794991114096035758080 }, { target := 214, numerator := 1910102794991114096035758080 }, { target := 215, numerator := 1910102794991114096035758080 }, { target := 226, numerator := 7016605457043307729994645504 }, { target := 227, numerator := 7016605457043307729994645504 }, { target := 228, numerator := 7016605457043307729994645504 }, { target := 229, numerator := 7016605457043307729994645504 }, { target := 301, numerator := 149906801632214017663565824 }, { target := 302, numerator := 149906801632214017663565824 }, { target := 303, numerator := 149906801632214017663565824 }, { target := 304, numerator := 149906801632214017663565824 }, { target := 428, numerator := 169249614746048084458864640 }, { target := 429, numerator := 169249614746048084458864640 }, { target := 430, numerator := 169249614746048084458864640 }, { target := 431, numerator := 169249614746048084458864640 }, { target := 442, numerator := 174085318024506601157689344 }, { target := 443, numerator := 174085318024506601157689344 }, { target := 444, numerator := 174085318024506601157689344 }, { target := 445, numerator := 174085318024506601157689344 }, { target := 517, numerator := 169249614746048084458864640 }, { target := 518, numerator := 169249614746048084458864640 }, { target := 519, numerator := 169249614746048084458864640 }, { target := 520, numerator := 169249614746048084458864640 }]

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
    Slot1.Left15.expected,
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 22127840276321486128545792 }, { target := 13, numerator := 1000138124621307718498516992 }, { target := 18, numerator := 22245943249410402319073280 }, { target := 31, numerator := 320853684006661548863913984 }, { target := 33, numerator := 14502002807008961918228496384 }, { target := 38, numerator := 322566177116450833626562560 }, { target := 45, numerator := 567947900425584810632675328 }, { target := 47, numerator := 25670211865280231441461936128 }, { target := 52, numerator := 570979210068200326189547520 }, { target := 55, numerator := 116298594441052749274546176 }, { target := 56, numerator := 23066062922489076304891084800 }, { target := 61, numerator := 23066062922489076304891084800 }, { target := 69, numerator := 116298594441052749274546176 }, { target := 76, numerator := 18439866896934571773788160 }, { target := 78, numerator := 833448437184423098748764160 }, { target := 83, numerator := 18538286041175335265894400 }, { target := 90, numerator := 354045444421143778056732672 }, { target := 92, numerator := 16002209993940923495976271872 }, { target := 97, numerator := 355935091990566437105172480 }, { target := 116, numerator := 18439866896934571773788160 }, { target := 118, numerator := 833448437184423098748764160 }, { target := 123, numerator := 18538286041175335265894400 }, { target := 171, numerator := 564259927046197896277917696 }, { target := 173, numerator := 25503522177843346821712183296 }, { target := 178, numerator := 567271552859965259136368640 }, { target := 185, numerator := 590075740701906296761221120 }, { target := 187, numerator := 26670349989901539159960453120 }, { target := 192, numerator := 593225153317610728508620800 }, { target := 216, numerator := 354045444421143778056732672 }, { target := 218, numerator := 16002209993940923495976271872 }, { target := 223, numerator := 355935091990566437105172480 }, { target := 230, numerator := 9039222752877327083510956032 }, { target := 232, numerator := 408556423907804203006644191232 }, { target := 237, numerator := 9087467817384149347341434880 }, { target := 256, numerator := 579011820563745553696948224 }, { target := 258, numerator := 26170280927590885300711194624 }, { target := 263, numerator := 582102181692905527349084160 }, { target := 305, numerator := 320853684006661548863913984 }, { target := 307, numerator := 14502002807008961918228496384 }, { target := 312, numerator := 322566177116450833626562560 }, { target := 331, numerator := 564259927046197896277917696 }, { target := 333, numerator := 25503522177843346821712183296 }, { target := 338, numerator := 567271552859965259136368640 }, { target := 432, numerator := 18439866896934571773788160 }, { target := 434, numerator := 833448437184423098748764160 }, { target := 439, numerator := 18538286041175335265894400 }, { target := 446, numerator := 579011820563745553696948224 }, { target := 448, numerator := 26170280927590885300711194624 }, { target := 453, numerator := 582102181692905527349084160 }, { target := 472, numerator := 18439866896934571773788160 }, { target := 474, numerator := 833448437184423098748764160 }, { target := 479, numerator := 18538286041175335265894400 }, { target := 521, numerator := 564259927046197896277917696 }, { target := 523, numerator := 25503522177843346821712183296 }, { target := 528, numerator := 567271552859965259136368640 }, { target := 547, numerator := 590075740701906296761221120 }, { target := 549, numerator := 26670349989901539159960453120 }, { target := 554, numerator := 593225153317610728508620800 }, { target := 643, numerator := 22127840276321486128545792 }, { target := 645, numerator := 1000138124621307718498516992 }, { target := 650, numerator := 22245943249410402319073280 }]

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
    Slot2.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 100, numerator := 86605336285890345204449280 }, { target := 101, numerator := 17176855367811014269599744000 }, { target := 106, numerator := 17176855367811014269599744000 }, { target := 114, numerator := 86605336285890345204449280 }, { target := 126, numerator := 91554212645084079216132096 }, { target := 127, numerator := 18158389960257357942148300800 }, { target := 132, numerator := 18158389960257357942148300800 }, { target := 140, numerator := 91554212645084079216132096 }, { target := 195, numerator := 118773032620649616280387584 }, { target := 196, numerator := 23556830218712248141165363200 }, { target := 201, numerator := 23556830218712248141165363200 }, { target := 209, numerator := 118773032620649616280387584 }, { target := 240, numerator := 1591063749480785484756025344 }, { target := 241, numerator := 315563371471499490724361011200 }, { target := 246, numerator := 315563371471499490724361011200 }, { target := 254, numerator := 1591063749480785484756025344 }, { target := 266, numerator := 2877771602871156327793557504 }, { target := 267, numerator := 570762365507548845586985779200 }, { target := 272, numerator := 570762365507548845586985779200 }, { target := 280, numerator := 2877771602871156327793557504 }, { target := 315, numerator := 86605336285890345204449280 }, { target := 316, numerator := 17176855367811014269599744000 }, { target := 321, numerator := 17176855367811014269599744000 }, { target := 329, numerator := 86605336285890345204449280 }, { target := 341, numerator := 1591063749480785484756025344 }, { target := 342, numerator := 315563371471499490724361011200 }, { target := 347, numerator := 315563371471499490724361011200 }, { target := 355, numerator := 1591063749480785484756025344 }, { target := 376, numerator := 94028650824680946221973504 }, { target := 377, numerator := 18649157256480529778422579200 }, { target := 382, numerator := 18649157256480529778422579200 }, { target := 390, numerator := 94028650824680946221973504 }, { target := 456, numerator := 94028650824680946221973504 }, { target := 457, numerator := 18649157256480529778422579200 }, { target := 462, numerator := 18649157256480529778422579200 }, { target := 470, numerator := 94028650824680946221973504 }, { target := 482, numerator := 91554212645084079216132096 }, { target := 483, numerator := 18158389960257357942148300800 }, { target := 488, numerator := 18158389960257357942148300800 }, { target := 496, numerator := 91554212645084079216132096 }, { target := 531, numerator := 91554212645084079216132096 }, { target := 532, numerator := 18158389960257357942148300800 }, { target := 537, numerator := 18158389960257357942148300800 }, { target := 545, numerator := 91554212645084079216132096 }, { target := 557, numerator := 2877771602871156327793557504 }, { target := 558, numerator := 570762365507548845586985779200 }, { target := 563, numerator := 570762365507548845586985779200 }, { target := 571, numerator := 2877771602871156327793557504 }, { target := 592, numerator := 91554212645084079216132096 }, { target := 593, numerator := 18158389960257357942148300800 }, { target := 598, numerator := 18158389960257357942148300800 }, { target := 606, numerator := 91554212645084079216132096 }, { target := 653, numerator := 116298594441052749274546176 }, { target := 654, numerator := 23066062922489076304891084800 }, { target := 659, numerator := 23066062922489076304891084800 }, { target := 667, numerator := 116298594441052749274546176 }, { target := 688, numerator := 118773032620649616280387584 }, { target := 689, numerator := 23556830218712248141165363200 }, { target := 694, numerator := 23556830218712248141165363200 }, { target := 702, numerator := 118773032620649616280387584 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 8324120933377545731047424 }, { target := 143, numerator := 1364163103094846746662010880 }, { target := 145, numerator := 14044587334751521393533255680 }, { target := 153, numerator := 1364163103094846746662010880 }, { target := 160, numerator := 8324120933377545731047424 }, { target := 282, numerator := 204075222882804346954711040 }, { target := 283, numerator := 33443998656518823466552524800 }, { target := 285, numerator := 344318915303585685776944332800 }, { target := 293, numerator := 33443998656518823466552524800 }, { target := 300, numerator := 204075222882804346954711040 }, { target := 357, numerator := 150908256921231635511246848 }, { target := 358, numerator := 24730956901267866826582261760 }, { target := 360, numerator := 254614776842914678166635151360 }, { target := 368, numerator := 24730956901267866826582261760 }, { target := 375, numerator := 150908256921231635511246848 }, { target := 392, numerator := 168362058878313586237636608 }, { target := 393, numerator := 27591298891628029359905832960 }, { target := 395, numerator := 284063105125458190765979074560 }, { target := 403, numerator := 27591298891628029359905832960 }, { target := 410, numerator := 168362058878313586237636608 }, { target := 411, numerator := 1213061510460664579767664640 }, { target := 413, numerator := 48497974118109420763343749120 }, { target := 416, numerator := 48497962266076353404956835840 }, { target := 423, numerator := 1213061510460664579767664640 }, { target := 498, numerator := 8324120933377545731047424 }, { target := 499, numerator := 1364163103094846746662010880 }, { target := 501, numerator := 14044587334751521393533255680 }, { target := 509, numerator := 1364163103094846746662010880 }, { target := 516, numerator := 8324120933377545731047424 }, { target := 573, numerator := 168093538848204633149538304 }, { target := 574, numerator := 27547293630237873013239316480 }, { target := 576, numerator := 283610053921111367495219937280 }, { target := 584, numerator := 27547293630237873013239316480 }, { target := 591, numerator := 168093538848204633149538304 }, { target := 608, numerator := 171047259179403117118619648 }, { target := 609, numerator := 28031351505529592826570997760 }, { target := 611, numerator := 288593617168926423473570447360 }, { target := 619, numerator := 28031351505529592826570997760 }, { target := 626, numerator := 171047259179403117118619648 }, { target := 627, numerator := 1209521447686946687025152000 }, { target := 629, numerator := 48356443065235560586018816000 }, { target := 632, numerator := 48356431247790138365837312000 }, { target := 639, numerator := 1209521447686946687025152000 }, { target := 669, numerator := 8324120933377545731047424 }, { target := 670, numerator := 1364163103094846746662010880 }, { target := 672, numerator := 14044587334751521393533255680 }, { target := 680, numerator := 1364163103094846746662010880 }, { target := 687, numerator := 8324120933377545731047424 }, { target := 704, numerator := 204075222882804346954711040 }, { target := 705, numerator := 33443998656518823466552524800 }, { target := 707, numerator := 344318915303585685776944332800 }, { target := 715, numerator := 33443998656518823466552524800 }, { target := 722, numerator := 204075222882804346954711040 }, { target := 723, numerator := 1201261301214938270625955840 }, { target := 725, numerator := 48026203941863220172260638720 }, { target := 728, numerator := 48026192205122303274558423040 }, { target := 735, numerator := 1201261301214938270625955840 }, { target := 739, numerator := 8324120933377545731047424 }, { target := 740, numerator := 1364163103094846746662010880 }, { target := 742, numerator := 14044587334751521393533255680 }, { target := 750, numerator := 1364163103094846746662010880 }, { target := 757, numerator := 8324120933377545731047424 }]

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
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14040672253129549499426930688 }, { target := 2, numerator := 1213061510460664579767664640 }, { target := 3, numerator := 1209521447686946687025152000 }, { target := 4, numerator := 1201261301214938270625955840 }, { target := 5, numerator := 1209521447686946687025152000 }, { target := 11, numerator := 8324120933377545731047424 }, { target := 12, numerator := 204075222882804346954711040 }, { target := 13, numerator := 150908256921231635511246848 }, { target := 14, numerator := 168362058878313586237636608 }, { target := 15, numerator := 8324120933377545731047424 }, { target := 16, numerator := 168093538848204633149538304 }, { target := 17, numerator := 171047259179403117118619648 }, { target := 18, numerator := 8324120933377545731047424 }, { target := 19, numerator := 204075222882804346954711040 }, { target := 20, numerator := 8324120933377545731047424 }, { target := 21, numerator := 51146808563272272855399661568 }, { target := 22, numerator := 48497974118109420763343749120 }, { target := 23, numerator := 48356443065235560586018816000 }, { target := 24, numerator := 48026203941863220172260638720 }, { target := 25, numerator := 48356443065235560586018816000 }, { target := 31, numerator := 1364163103094846746662010880 }, { target := 32, numerator := 33443998656518823466552524800 }, { target := 33, numerator := 24730956901267866826582261760 }, { target := 34, numerator := 27591298891628029359905832960 }, { target := 35, numerator := 1364163103094846746662010880 }, { target := 36, numerator := 27547293630237873013239316480 }, { target := 37, numerator := 28031351505529592826570997760 }, { target := 38, numerator := 1364163103094846746662010880 }, { target := 39, numerator := 33443998656518823466552524800 }, { target := 40, numerator := 1364163103094846746662010880 }, { target := 71, numerator := 14040681697862515238717358080 }, { target := 72, numerator := 48497962266076353404956835840 }, { target := 73, numerator := 48356431247790138365837312000 }, { target := 74, numerator := 48026192205122303274558423040 }, { target := 75, numerator := 48356431247790138365837312000 }, { target := 76, numerator := 14044587334751521393533255680 }, { target := 77, numerator := 344318915303585685776944332800 }, { target := 78, numerator := 254614776842914678166635151360 }, { target := 79, numerator := 284063105125458190765979074560 }, { target := 80, numerator := 14044587334751521393533255680 }, { target := 81, numerator := 283610053921111367495219937280 }, { target := 82, numerator := 288593617168926423473570447360 }, { target := 83, numerator := 14044587334751521393533255680 }, { target := 84, numerator := 344318915303585685776944332800 }, { target := 85, numerator := 14044587334751521393533255680 }, { target := 301, numerator := 1213061510460664579767664640 }, { target := 302, numerator := 1209521447686946687025152000 }, { target := 303, numerator := 1201261301214938270625955840 }, { target := 304, numerator := 1209521447686946687025152000 }, { target := 758, numerator := 1209521447686946687025152000 }, { target := 760, numerator := 48356443065235560586018816000 }, { target := 763, numerator := 48356431247790138365837312000 }, { target := 770, numerator := 1209521447686946687025152000 }, { target := 774, numerator := 14040672253129549499426930688 }, { target := 777, numerator := 51146808563272272855399661568 }, { target := 779, numerator := 14040681697862515238717358080 }]

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
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 109457500650402587552514048 }, { target := 56, numerator := 81510904739661501368893440 }, { target := 57, numerator := 86168670724785015732830208 }, { target := 58, numerator := 111786383642964344734482432 }, { target := 59, numerator := 1497471764217209868005670912 }, { target := 60, numerator := 2708490920349323602629230592 }, { target := 61, numerator := 81510904739661501368893440 }, { target := 62, numerator := 1497471764217209868005670912 }, { target := 63, numerator := 88497553717346772914798592 }, { target := 64, numerator := 88497553717346772914798592 }, { target := 65, numerator := 86168670724785015732830208 }, { target := 66, numerator := 86168670724785015732830208 }, { target := 67, numerator := 2708490920349323602629230592 }, { target := 68, numerator := 86168670724785015732830208 }, { target := 69, numerator := 109457500650402587552514048 }, { target := 70, numerator := 111786383642964344734482432 }, { target := 100, numerator := 21709235691754424757544550400 }, { target := 101, numerator := 16166452110880954606682112000 }, { target := 102, numerator := 17090249374359866298492518400 }, { target := 103, numerator := 22171134323493880603449753600 }, { target := 104, numerator := 297000820208470108917045657600 }, { target := 105, numerator := 537188108712987148787751321600 }, { target := 106, numerator := 16166452110880954606682112000 }, { target := 107, numerator := 297000820208470108917045657600 }, { target := 108, numerator := 17552148006099322144397721600 }, { target := 109, numerator := 17552148006099322144397721600 }, { target := 110, numerator := 17090249374359866298492518400 }, { target := 111, numerator := 17090249374359866298492518400 }, { target := 112, numerator := 537188108712987148787751321600 }, { target := 113, numerator := 17090249374359866298492518400 }, { target := 114, numerator := 21709235691754424757544550400 }, { target := 115, numerator := 22171134323493880603449753600 }, { target := 305, numerator := 1364163103094846746662010880 }, { target := 306, numerator := 33443998656518823466552524800 }, { target := 307, numerator := 24730956901267866826582261760 }, { target := 308, numerator := 27591298891628029359905832960 }, { target := 309, numerator := 1364163103094846746662010880 }, { target := 310, numerator := 27547293630237873013239316480 }, { target := 311, numerator := 28031351505529592826570997760 }, { target := 312, numerator := 1364163103094846746662010880 }, { target := 313, numerator := 33443998656518823466552524800 }, { target := 314, numerator := 1364163103094846746662010880 }, { target := 643, numerator := 8324120933377545731047424 }, { target := 644, numerator := 204075222882804346954711040 }, { target := 645, numerator := 150908256921231635511246848 }, { target := 646, numerator := 168362058878313586237636608 }, { target := 647, numerator := 8324120933377545731047424 }, { target := 648, numerator := 168093538848204633149538304 }, { target := 649, numerator := 171047259179403117118619648 }, { target := 650, numerator := 8324120933377545731047424 }, { target := 651, numerator := 204075222882804346954711040 }, { target := 652, numerator := 8324120933377545731047424 }]

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
    Slot9.Left14.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 22127840276321486128545792 }, { target := 143, numerator := 320853684006661548863913984 }, { target := 144, numerator := 567947900425584810632675328 }, { target := 145, numerator := 18439866896934571773788160 }, { target := 146, numerator := 354045444421143778056732672 }, { target := 147, numerator := 18439866896934571773788160 }, { target := 148, numerator := 564259927046197896277917696 }, { target := 149, numerator := 590075740701906296761221120 }, { target := 150, numerator := 354045444421143778056732672 }, { target := 151, numerator := 9039222752877327083510956032 }, { target := 152, numerator := 579011820563745553696948224 }, { target := 153, numerator := 320853684006661548863913984 }, { target := 154, numerator := 564259927046197896277917696 }, { target := 155, numerator := 18439866896934571773788160 }, { target := 156, numerator := 579011820563745553696948224 }, { target := 157, numerator := 18439866896934571773788160 }, { target := 158, numerator := 564259927046197896277917696 }, { target := 159, numerator := 590075740701906296761221120 }, { target := 160, numerator := 22127840276321486128545792 }, { target := 315, numerator := 21709235691754424757544550400 }, { target := 316, numerator := 16166452110880954606682112000 }, { target := 317, numerator := 17090249374359866298492518400 }, { target := 318, numerator := 22171134323493880603449753600 }, { target := 319, numerator := 297000820208470108917045657600 }, { target := 320, numerator := 537188108712987148787751321600 }, { target := 321, numerator := 16166452110880954606682112000 }, { target := 322, numerator := 297000820208470108917045657600 }, { target := 323, numerator := 17552148006099322144397721600 }, { target := 324, numerator := 17552148006099322144397721600 }, { target := 325, numerator := 17090249374359866298492518400 }, { target := 326, numerator := 17090249374359866298492518400 }, { target := 327, numerator := 537188108712987148787751321600 }, { target := 328, numerator := 17090249374359866298492518400 }, { target := 329, numerator := 21709235691754424757544550400 }, { target := 330, numerator := 22171134323493880603449753600 }, { target := 653, numerator := 109457500650402587552514048 }, { target := 654, numerator := 81510904739661501368893440 }, { target := 655, numerator := 86168670724785015732830208 }, { target := 656, numerator := 111786383642964344734482432 }, { target := 657, numerator := 1497471764217209868005670912 }, { target := 658, numerator := 2708490920349323602629230592 }, { target := 659, numerator := 81510904739661501368893440 }, { target := 660, numerator := 1497471764217209868005670912 }, { target := 661, numerator := 88497553717346772914798592 }, { target := 662, numerator := 88497553717346772914798592 }, { target := 663, numerator := 86168670724785015732830208 }, { target := 664, numerator := 86168670724785015732830208 }, { target := 665, numerator := 2708490920349323602629230592 }, { target := 666, numerator := 86168670724785015732830208 }, { target := 667, numerator := 109457500650402587552514048 }, { target := 668, numerator := 111786383642964344734482432 }]

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
    Slot10.Left2.expected,
    Slot10.Left7.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 357, numerator := 1000138124621307718498516992 }, { target := 358, numerator := 14502002807008961918228496384 }, { target := 359, numerator := 25670211865280231441461936128 }, { target := 360, numerator := 833448437184423098748764160 }, { target := 361, numerator := 16002209993940923495976271872 }, { target := 362, numerator := 833448437184423098748764160 }, { target := 363, numerator := 25503522177843346821712183296 }, { target := 364, numerator := 26670349989901539159960453120 }, { target := 365, numerator := 16002209993940923495976271872 }, { target := 366, numerator := 408556423907804203006644191232 }, { target := 367, numerator := 26170280927590885300711194624 }, { target := 368, numerator := 14502002807008961918228496384 }, { target := 369, numerator := 25503522177843346821712183296 }, { target := 370, numerator := 833448437184423098748764160 }, { target := 371, numerator := 26170280927590885300711194624 }, { target := 372, numerator := 833448437184423098748764160 }, { target := 373, numerator := 25503522177843346821712183296 }, { target := 374, numerator := 26670349989901539159960453120 }, { target := 375, numerator := 1000138124621307718498516992 }, { target := 411, numerator := 149906801632214017663565824 }, { target := 412, numerator := 169249614746048084458864640 }, { target := 413, numerator := 145071098353755500964741120 }, { target := 414, numerator := 1910102794991114096035758080 }, { target := 415, numerator := 169249614746048084458864640 }, { target := 416, numerator := 145071098353755500964741120 }, { target := 417, numerator := 169249614746048084458864640 }, { target := 418, numerator := 169249614746048084458864640 }, { target := 419, numerator := 7016605457043307729994645504 }, { target := 420, numerator := 174085318024506601157689344 }, { target := 421, numerator := 1910102794991114096035758080 }, { target := 422, numerator := 7016605457043307729994645504 }, { target := 423, numerator := 149906801632214017663565824 }, { target := 424, numerator := 169249614746048084458864640 }, { target := 425, numerator := 174085318024506601157689344 }, { target := 426, numerator := 169249614746048084458864640 }, { target := 669, numerator := 22245943249410402319073280 }, { target := 670, numerator := 322566177116450833626562560 }, { target := 671, numerator := 570979210068200326189547520 }, { target := 672, numerator := 18538286041175335265894400 }, { target := 673, numerator := 355935091990566437105172480 }, { target := 674, numerator := 18538286041175335265894400 }, { target := 675, numerator := 567271552859965259136368640 }, { target := 676, numerator := 593225153317610728508620800 }, { target := 677, numerator := 355935091990566437105172480 }, { target := 678, numerator := 9087467817384149347341434880 }, { target := 679, numerator := 582102181692905527349084160 }, { target := 680, numerator := 322566177116450833626562560 }, { target := 681, numerator := 567271552859965259136368640 }, { target := 682, numerator := 18538286041175335265894400 }, { target := 683, numerator := 582102181692905527349084160 }, { target := 684, numerator := 18538286041175335265894400 }, { target := 685, numerator := 567271552859965259136368640 }, { target := 686, numerator := 593225153317610728508620800 }, { target := 687, numerator := 22245943249410402319073280 }]

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
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 627, numerator := 149906801632214017663565824 }, { target := 628, numerator := 169249614746048084458864640 }, { target := 629, numerator := 145071098353755500964741120 }, { target := 630, numerator := 1910102794991114096035758080 }, { target := 631, numerator := 169249614746048084458864640 }, { target := 632, numerator := 145071098353755500964741120 }, { target := 633, numerator := 169249614746048084458864640 }, { target := 634, numerator := 169249614746048084458864640 }, { target := 635, numerator := 7016605457043307729994645504 }, { target := 636, numerator := 174085318024506601157689344 }, { target := 637, numerator := 1910102794991114096035758080 }, { target := 638, numerator := 7016605457043307729994645504 }, { target := 639, numerator := 149906801632214017663565824 }, { target := 640, numerator := 169249614746048084458864640 }, { target := 641, numerator := 174085318024506601157689344 }, { target := 642, numerator := 169249614746048084458864640 }, { target := 723, numerator := 149906801632214017663565824 }, { target := 724, numerator := 169249614746048084458864640 }, { target := 725, numerator := 145071098353755500964741120 }, { target := 726, numerator := 1910102794991114096035758080 }, { target := 727, numerator := 169249614746048084458864640 }, { target := 728, numerator := 145071098353755500964741120 }, { target := 729, numerator := 169249614746048084458864640 }, { target := 730, numerator := 169249614746048084458864640 }, { target := 731, numerator := 7016605457043307729994645504 }, { target := 732, numerator := 174085318024506601157689344 }, { target := 733, numerator := 1910102794991114096035758080 }, { target := 734, numerator := 7016605457043307729994645504 }, { target := 735, numerator := 149906801632214017663565824 }, { target := 736, numerator := 169249614746048084458864640 }, { target := 737, numerator := 174085318024506601157689344 }, { target := 738, numerator := 169249614746048084458864640 }, { target := 758, numerator := 149906801632214017663565824 }, { target := 759, numerator := 169249614746048084458864640 }, { target := 760, numerator := 145071098353755500964741120 }, { target := 761, numerator := 1910102794991114096035758080 }, { target := 762, numerator := 169249614746048084458864640 }, { target := 763, numerator := 145071098353755500964741120 }, { target := 764, numerator := 169249614746048084458864640 }, { target := 765, numerator := 169249614746048084458864640 }, { target := 766, numerator := 7016605457043307729994645504 }, { target := 767, numerator := 174085318024506601157689344 }, { target := 768, numerator := 1910102794991114096035758080 }, { target := 769, numerator := 7016605457043307729994645504 }, { target := 770, numerator := 149906801632214017663565824 }, { target := 771, numerator := 169249614746048084458864640 }, { target := 772, numerator := 174085318024506601157689344 }, { target := 773, numerator := 169249614746048084458864640 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0
