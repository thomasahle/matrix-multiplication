import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1

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
  [{ target := 80, numerator := 142294346861828149579087872 }, { target := 81, numerator := 162057450592637614798405632 }, { target := 82, numerator := 126483863877180577403633664 }, { target := 83, numerator := 1695674300103452115817463808 }, { target := 84, numerator := 150199588354151935666814976 }, { target := 85, numerator := 126483863877180577403633664 }, { target := 86, numerator := 150199588354151935666814976 }, { target := 87, numerator := 146246967607990042622951424 }, { target := 88, numerator := 5525763803134326475321245696 }, { target := 89, numerator := 146246967607990042622951424 }, { target := 90, numerator := 1695674300103452115817463808 }, { target := 91, numerator := 5525763803134326475321245696 }, { target := 92, numerator := 142294346861828149579087872 }, { target := 93, numerator := 146246967607990042622951424 }, { target := 94, numerator := 146246967607990042622951424 }, { target := 95, numerator := 162057450592637614798405632 }, { target := 115, numerator := 160654907747225330169937920 }, { target := 116, numerator := 182968089378784403804651520 }, { target := 117, numerator := 142804362441978071262167040 }, { target := 118, numerator := 1914470983987768517858426880 }, { target := 119, numerator := 169580180399848959623823360 }, { target := 120, numerator := 142804362441978071262167040 }, { target := 121, numerator := 169580180399848959623823360 }, { target := 122, numerator := 165117544073537144896880640 }, { target := 123, numerator := 6238765584183916988265922560 }, { target := 124, numerator := 165117544073537144896880640 }, { target := 125, numerator := 1914470983987768517858426880 }, { target := 126, numerator := 6238765584183916988265922560 }, { target := 127, numerator := 160654907747225330169937920 }, { target := 128, numerator := 165117544073537144896880640 }, { target := 129, numerator := 165117544073537144896880640 }, { target := 130, numerator := 182968089378784403804651520 }, { target := 176, numerator := 137704206640478854431375360 }, { target := 177, numerator := 156829790896100917546844160 }, { target := 178, numerator := 122403739235981203939000320 }, { target := 179, numerator := 1640975129132373015307223040 }, { target := 180, numerator := 145354440342727679677562880 }, { target := 181, numerator := 122403739235981203939000320 }, { target := 182, numerator := 145354440342727679677562880 }, { target := 183, numerator := 141529323491603267054469120 }, { target := 184, numerator := 5347513357871928847085076480 }, { target := 185, numerator := 141529323491603267054469120 }, { target := 186, numerator := 1640975129132373015307223040 }, { target := 187, numerator := 5347513357871928847085076480 }, { target := 188, numerator := 137704206640478854431375360 }, { target := 189, numerator := 141529323491603267054469120 }, { target := 190, numerator := 141529323491603267054469120 }, { target := 191, numerator := 156829790896100917546844160 }, { target := 211, numerator := 1813105387432971583346442240 }, { target := 212, numerator := 2064925580131995414366781440 }, { target := 213, numerator := 1611649233273752518530170880 }, { target := 214, numerator := 21606172533576244701545103360 }, { target := 215, numerator := 1913833464512581115754577920 }, { target := 216, numerator := 1611649233273752518530170880 }, { target := 217, numerator := 1913833464512581115754577920 }, { target := 218, numerator := 1863469425972776349550510080 }, { target := 219, numerator := 70408925878647063153286840320 }, { target := 220, numerator := 1863469425972776349550510080 }, { target := 221, numerator := 21606172533576244701545103360 }, { target := 222, numerator := 70408925878647063153286840320 }, { target := 223, numerator := 1813105387432971583346442240 }, { target := 224, numerator := 1863469425972776349550510080 }, { target := 225, numerator := 1863469425972776349550510080 }, { target := 226, numerator := 2064925580131995414366781440 }]

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
  [{ target := 237, numerator := 160654907747225330169937920 }, { target := 238, numerator := 182968089378784403804651520 }, { target := 239, numerator := 142804362441978071262167040 }, { target := 240, numerator := 1914470983987768517858426880 }, { target := 241, numerator := 169580180399848959623823360 }, { target := 242, numerator := 142804362441978071262167040 }, { target := 243, numerator := 169580180399848959623823360 }, { target := 244, numerator := 165117544073537144896880640 }, { target := 245, numerator := 6238765584183916988265922560 }, { target := 246, numerator := 165117544073537144896880640 }, { target := 247, numerator := 1914470983987768517858426880 }, { target := 248, numerator := 6238765584183916988265922560 }, { target := 249, numerator := 160654907747225330169937920 }, { target := 250, numerator := 165117544073537144896880640 }, { target := 251, numerator := 165117544073537144896880640 }, { target := 252, numerator := 182968089378784403804651520 }, { target := 286, numerator := 137704206640478854431375360 }, { target := 287, numerator := 156829790896100917546844160 }, { target := 288, numerator := 122403739235981203939000320 }, { target := 289, numerator := 1640975129132373015307223040 }, { target := 290, numerator := 145354440342727679677562880 }, { target := 291, numerator := 122403739235981203939000320 }, { target := 292, numerator := 145354440342727679677562880 }, { target := 293, numerator := 141529323491603267054469120 }, { target := 294, numerator := 5347513357871928847085076480 }, { target := 295, numerator := 141529323491603267054469120 }, { target := 296, numerator := 1640975129132373015307223040 }, { target := 297, numerator := 5347513357871928847085076480 }, { target := 298, numerator := 137704206640478854431375360 }, { target := 299, numerator := 141529323491603267054469120 }, { target := 300, numerator := 141529323491603267054469120 }, { target := 301, numerator := 156829790896100917546844160 }, { target := 312, numerator := 160654907747225330169937920 }, { target := 313, numerator := 182968089378784403804651520 }, { target := 314, numerator := 142804362441978071262167040 }, { target := 315, numerator := 1914470983987768517858426880 }, { target := 316, numerator := 169580180399848959623823360 }, { target := 317, numerator := 142804362441978071262167040 }, { target := 318, numerator := 169580180399848959623823360 }, { target := 319, numerator := 165117544073537144896880640 }, { target := 320, numerator := 6238765584183916988265922560 }, { target := 321, numerator := 165117544073537144896880640 }, { target := 322, numerator := 1914470983987768517858426880 }, { target := 323, numerator := 6238765584183916988265922560 }, { target := 324, numerator := 160654907747225330169937920 }, { target := 325, numerator := 165117544073537144896880640 }, { target := 326, numerator := 165117544073537144896880640 }, { target := 327, numerator := 182968089378784403804651520 }, { target := 392, numerator := 160654907747225330169937920 }, { target := 393, numerator := 182968089378784403804651520 }, { target := 394, numerator := 142804362441978071262167040 }, { target := 395, numerator := 1914470983987768517858426880 }, { target := 396, numerator := 169580180399848959623823360 }, { target := 397, numerator := 142804362441978071262167040 }, { target := 398, numerator := 169580180399848959623823360 }, { target := 399, numerator := 165117544073537144896880640 }, { target := 400, numerator := 6238765584183916988265922560 }, { target := 401, numerator := 165117544073537144896880640 }, { target := 402, numerator := 1914470983987768517858426880 }, { target := 403, numerator := 6238765584183916988265922560 }, { target := 404, numerator := 160654907747225330169937920 }, { target := 405, numerator := 165117544073537144896880640 }, { target := 406, numerator := 165117544073537144896880640 }, { target := 407, numerator := 182968089378784403804651520 }]

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
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 427, numerator := 6660293461177827259330854912 }, { target := 428, numerator := 7585334219674747712015695872 }, { target := 429, numerator := 5920260854380290897182982144 }, { target := 430, numerator := 79368497079035774840359354368 }, { target := 431, numerator := 7030309764576595440404791296 }, { target := 432, numerator := 5920260854380290897182982144 }, { target := 433, numerator := 7030309764576595440404791296 }, { target := 434, numerator := 6845301612877211349867823104 }, { target := 435, numerator := 258641396075738958570681532416 }, { target := 436, numerator := 6845301612877211349867823104 }, { target := 437, numerator := 79368497079035774840359354368 }, { target := 438, numerator := 258641396075738958570681532416 }, { target := 439, numerator := 6660293461177827259330854912 }, { target := 440, numerator := 6845301612877211349867823104 }, { target := 441, numerator := 6845301612877211349867823104 }, { target := 442, numerator := 7585334219674747712015695872 }, { target := 453, numerator := 165245047968574625317650432 }, { target := 454, numerator := 188195749075321101056212992 }, { target := 455, numerator := 146884487083177444726800384 }, { target := 456, numerator := 1969170154958847618368667648 }, { target := 457, numerator := 174425328411273215613075456 }, { target := 458, numerator := 146884487083177444726800384 }, { target := 459, numerator := 174425328411273215613075456 }, { target := 460, numerator := 169835188189923920465362944 }, { target := 461, numerator := 6417016029446314616502091776 }, { target := 462, numerator := 169835188189923920465362944 }, { target := 463, numerator := 1969170154958847618368667648 }, { target := 464, numerator := 6417016029446314616502091776 }, { target := 465, numerator := 165245047968574625317650432 }, { target := 466, numerator := 169835188189923920465362944 }, { target := 467, numerator := 169835188189923920465362944 }, { target := 468, numerator := 188195749075321101056212992 }, { target := 502, numerator := 1813105387432971583346442240 }, { target := 503, numerator := 2064925580131995414366781440 }, { target := 504, numerator := 1611649233273752518530170880 }, { target := 505, numerator := 21606172533576244701545103360 }, { target := 506, numerator := 1913833464512581115754577920 }, { target := 507, numerator := 1611649233273752518530170880 }, { target := 508, numerator := 1913833464512581115754577920 }, { target := 509, numerator := 1863469425972776349550510080 }, { target := 510, numerator := 70408925878647063153286840320 }, { target := 511, numerator := 1863469425972776349550510080 }, { target := 512, numerator := 21606172533576244701545103360 }, { target := 513, numerator := 70408925878647063153286840320 }, { target := 514, numerator := 1813105387432971583346442240 }, { target := 515, numerator := 1863469425972776349550510080 }, { target := 516, numerator := 1863469425972776349550510080 }, { target := 517, numerator := 2064925580131995414366781440 }, { target := 528, numerator := 6660293461177827259330854912 }, { target := 529, numerator := 7585334219674747712015695872 }, { target := 530, numerator := 5920260854380290897182982144 }, { target := 531, numerator := 79368497079035774840359354368 }, { target := 532, numerator := 7030309764576595440404791296 }, { target := 533, numerator := 5920260854380290897182982144 }, { target := 534, numerator := 7030309764576595440404791296 }, { target := 535, numerator := 6845301612877211349867823104 }, { target := 536, numerator := 258641396075738958570681532416 }, { target := 537, numerator := 6845301612877211349867823104 }, { target := 538, numerator := 79368497079035774840359354368 }, { target := 539, numerator := 258641396075738958570681532416 }, { target := 540, numerator := 6660293461177827259330854912 }, { target := 541, numerator := 6845301612877211349867823104 }, { target := 542, numerator := 6845301612877211349867823104 }, { target := 543, numerator := 7585334219674747712015695872 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 573, numerator := 142294346861828149579087872 }, { target := 574, numerator := 162057450592637614798405632 }, { target := 575, numerator := 126483863877180577403633664 }, { target := 576, numerator := 1695674300103452115817463808 }, { target := 577, numerator := 150199588354151935666814976 }, { target := 578, numerator := 126483863877180577403633664 }, { target := 579, numerator := 150199588354151935666814976 }, { target := 580, numerator := 146246967607990042622951424 }, { target := 581, numerator := 5525763803134326475321245696 }, { target := 582, numerator := 146246967607990042622951424 }, { target := 583, numerator := 1695674300103452115817463808 }, { target := 584, numerator := 5525763803134326475321245696 }, { target := 585, numerator := 142294346861828149579087872 }, { target := 586, numerator := 146246967607990042622951424 }, { target := 587, numerator := 146246967607990042622951424 }, { target := 588, numerator := 162057450592637614798405632 }, { target := 642, numerator := 160654907747225330169937920 }, { target := 643, numerator := 182968089378784403804651520 }, { target := 644, numerator := 142804362441978071262167040 }, { target := 645, numerator := 1914470983987768517858426880 }, { target := 646, numerator := 169580180399848959623823360 }, { target := 647, numerator := 142804362441978071262167040 }, { target := 648, numerator := 169580180399848959623823360 }, { target := 649, numerator := 165117544073537144896880640 }, { target := 650, numerator := 6238765584183916988265922560 }, { target := 651, numerator := 165117544073537144896880640 }, { target := 652, numerator := 1914470983987768517858426880 }, { target := 653, numerator := 6238765584183916988265922560 }, { target := 654, numerator := 160654907747225330169937920 }, { target := 655, numerator := 165117544073537144896880640 }, { target := 656, numerator := 165117544073537144896880640 }, { target := 657, numerator := 182968089378784403804651520 }, { target := 668, numerator := 165245047968574625317650432 }, { target := 669, numerator := 188195749075321101056212992 }, { target := 670, numerator := 146884487083177444726800384 }, { target := 671, numerator := 1969170154958847618368667648 }, { target := 672, numerator := 174425328411273215613075456 }, { target := 673, numerator := 146884487083177444726800384 }, { target := 674, numerator := 174425328411273215613075456 }, { target := 675, numerator := 169835188189923920465362944 }, { target := 676, numerator := 6417016029446314616502091776 }, { target := 677, numerator := 169835188189923920465362944 }, { target := 678, numerator := 1969170154958847618368667648 }, { target := 679, numerator := 6417016029446314616502091776 }, { target := 680, numerator := 165245047968574625317650432 }, { target := 681, numerator := 169835188189923920465362944 }, { target := 682, numerator := 169835188189923920465362944 }, { target := 683, numerator := 188195749075321101056212992 }, { target := 713, numerator := 160654907747225330169937920 }, { target := 714, numerator := 182968089378784403804651520 }, { target := 715, numerator := 142804362441978071262167040 }, { target := 716, numerator := 1914470983987768517858426880 }, { target := 717, numerator := 169580180399848959623823360 }, { target := 718, numerator := 142804362441978071262167040 }, { target := 719, numerator := 169580180399848959623823360 }, { target := 720, numerator := 165117544073537144896880640 }, { target := 721, numerator := 6238765584183916988265922560 }, { target := 722, numerator := 165117544073537144896880640 }, { target := 723, numerator := 1914470983987768517858426880 }, { target := 724, numerator := 6238765584183916988265922560 }, { target := 725, numerator := 160654907747225330169937920 }, { target := 726, numerator := 165117544073537144896880640 }, { target := 727, numerator := 165117544073537144896880640 }, { target := 728, numerator := 182968089378784403804651520 }]

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 3018187864813331520392527872 }, { target := 134, numerator := 11023986453651750935907532800 }, { target := 136, numerator := 3018186847936564457153495040 }, { target := 227, numerator := 43763724039793307045691654144 }, { target := 230, numerator := 159847803577950388570659225600 }, { target := 232, numerator := 43763709295080184628725678080 }, { target := 253, numerator := 77466821863542175690074882048 }, { target := 256, numerator := 282948985643728274021626675200 }, { target := 258, numerator := 77466795763705154400273039360 }, { target := 263, numerator := 23636914807365072364721143808 }, { target := 265, numerator := 23636920442845386882989162496 }, { target := 302, numerator := 2515156554011109600327106560 }, { target := 305, numerator := 9186655378043125779922944000 }, { target := 307, numerator := 2515155706613803714294579200 }, { target := 328, numerator := 48291005837013304326280445952 }, { target := 331, numerator := 176383783258428014974520524800 }, { target := 333, numerator := 48290989566985031314455920640 }, { target := 338, numerator := 17601957835271862399260426240 }, { target := 340, numerator := 17601962031906139168183418880 }, { target := 342, numerator := 2515156554011109600327106560 }, { target := 345, numerator := 9186655378043125779922944000 }, { target := 347, numerator := 2515155706613803714294579200 }, { target := 352, numerator := 18607783997287397393503879168 }, { target := 354, numerator := 18607788433729347120651042816 }, { target := 443, numerator := 76963790552739953770009460736 }, { target := 446, numerator := 281111654568119648865642086400 }, { target := 448, numerator := 76963764622382393657414123520 }, { target := 469, numerator := 80485009728355507210467409920 }, { target := 472, numerator := 293972972097380024957534208000 }, { target := 474, numerator := 80484982611641718857426534400 }, { target := 518, numerator := 48291005837013304326280445952 }, { target := 521, numerator := 176383783258428014974520524800 }, { target := 523, numerator := 48290989566985031314455920640 }, { target := 544, numerator := 1232929742776245926080347635712 }, { target := 547, numerator := 4503298466316740257318227148800 }, { target := 549, numerator := 1232929327382086580747202723840 }, { target := 558, numerator := 78975915795948841450271145984 }, { target := 561, numerator := 288460978870554149489580441600 }, { target := 563, numerator := 78975889187673436628849786880 }, { target := 589, numerator := 43763724039793307045691654144 }, { target := 592, numerator := 159847803577950388570659225600 }, { target := 594, numerator := 43763709295080184628725678080 }, { target := 603, numerator := 76963790552739953770009460736 }, { target := 606, numerator := 281111654568119648865642086400 }, { target := 608, numerator := 76963764622382393657414123520 }, { target := 658, numerator := 2515156554011109600327106560 }, { target := 661, numerator := 9186655378043125779922944000 }, { target := 663, numerator := 2515155706613803714294579200 }, { target := 684, numerator := 78975915795948841450271145984 }, { target := 687, numerator := 288460978870554149489580441600 }, { target := 689, numerator := 78975889187673436628849786880 }, { target := 698, numerator := 2515156554011109600327106560 }, { target := 701, numerator := 9186655378043125779922944000 }, { target := 703, numerator := 2515155706613803714294579200 }, { target := 729, numerator := 76963790552739953770009460736 }, { target := 732, numerator := 281111654568119648865642086400 }, { target := 734, numerator := 76963764622382393657414123520 }, { target := 743, numerator := 80485009728355507210467409920 }, { target := 746, numerator := 293972972097380024957534208000 }, { target := 748, numerator := 80484982611641718857426534400 }, { target := 763, numerator := 3018187864813331520392527872 }, { target := 766, numerator := 11023986453651750935907532800 }, { target := 768, numerator := 3018186847936564457153495040 }]

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
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2591491265470200054093447168 }, { target := 27, numerator := 38872368982053000811401707520 }, { target := 28, numerator := 68242603324048601424460775424 }, { target := 29, numerator := 2591491265470200054093447168 }, { target := 30, numerator := 43191521091170000901557452800 }, { target := 31, numerator := 2591491265470200054093447168 }, { target := 32, numerator := 68242603324048601424460775424 }, { target := 33, numerator := 67810688113136901415445200896 }, { target := 34, numerator := 43191521091170000901557452800 }, { target := 35, numerator := 1046530556039049121844737081344 }, { target := 36, numerator := 66946857691313501397414051840 }, { target := 37, numerator := 38872368982053000811401707520 }, { target := 38, numerator := 68242603324048601424460775424 }, { target := 39, numerator := 2591491265470200054093447168 }, { target := 40, numerator := 66946857691313501397414051840 }, { target := 41, numerator := 2591491265470200054093447168 }, { target := 42, numerator := 68242603324048601424460775424 }, { target := 43, numerator := 68242603324048601424460775424 }, { target := 44, numerator := 2591491265470200054093447168 }, { target := 356, numerator := 1798881619586568211962789888 }, { target := 479, numerator := 24139827888372839861842870272 }, { target := 481, numerator := 24139833643756990859222974464 }, { target := 554, numerator := 323373111087994500649270116352 }, { target := 556, numerator := 323373188186161356718341095424 }, { target := 568, numerator := 584887913212033599152567877632 }, { target := 570, numerator := 584888052660195424359923318784 }, { target := 572, numerator := 44101613899541672293281300480 }, { target := 599, numerator := 17601957835271862399260426240 }, { target := 601, numerator := 17601962031906139168183418880 }, { target := 613, numerator := 323373111087994500649270116352 }, { target := 615, numerator := 323373188186161356718341095424 }, { target := 617, numerator := 32611982909924236616873803776 }, { target := 618, numerator := 19110697078295164890625605632 }, { target := 620, numerator := 19110701634640951096884854784 }, { target := 622, numerator := 36383831467121879641957072896 }, { target := 694, numerator := 19110697078295164890625605632 }, { target := 696, numerator := 19110701634640951096884854784 }, { target := 708, numerator := 18607783997287397393503879168 }, { target := 710, numerator := 18607788433729347120651042816 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 739, numerator := 18607783997287397393503879168 }, { target := 741, numerator := 18607788433729347120651042816 }, { target := 753, numerator := 584887913212033599152567877632 }, { target := 755, numerator := 584888052660195424359923318784 }, { target := 757, numerator := 36325803027780377441571176448 }, { target := 758, numerator := 18607783997287397393503879168 }, { target := 760, numerator := 18607788433729347120651042816 }, { target := 762, numerator := 36964115860536901645816037376 }, { target := 773, numerator := 23636914807365072364721143808 }, { target := 775, numerator := 23636920442845386882989162496 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 778, numerator := 24139827888372839861842870272 }, { target := 780, numerator := 24139833643756990859222974464 }, { target := 782, numerator := 44101613899541672293281300480 }, { target := 783, numerator := 1798881619586568211962789888 }]

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
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 38045554928056743311313993728 }, { target := 82, numerator := 1483981487661570412649610477568 }, { target := 85, numerator := 1483980943342348027999012519936 }, { target := 92, numerator := 38045736367797538194846646272 }, { target := 131, numerator := 28121916925968042889805037568 }, { target := 134, numerator := 101153698895309730621794811904 }, { target := 136, numerator := 28121926307592630000706125824 }, { target := 157, numerator := 9440182439900839423506382848 }, { target := 158, numerator := 141602736598512591352595742720 }, { target := 159, numerator := 248591470917388771485668081664 }, { target := 160, numerator := 9440182439900839423506382848 }, { target := 161, numerator := 157336373998347323725106380800 }, { target := 162, numerator := 9440182439900839423506382848 }, { target := 163, numerator := 248591470917388771485668081664 }, { target := 164, numerator := 247018107177405298248417017856 }, { target := 165, numerator := 157336373998347323725106380800 }, { target := 166, numerator := 3812260341979955653859327606784 }, { target := 167, numerator := 243871379697438351773914890240 }, { target := 168, numerator := 141602736598512591352595742720 }, { target := 169, numerator := 248591470917388771485668081664 }, { target := 170, numerator := 9440182439900839423506382848 }, { target := 171, numerator := 243871379697438351773914890240 }, { target := 172, numerator := 9440182439900839423506382848 }, { target := 173, numerator := 248591470917388771485668081664 }, { target := 174, numerator := 248591470917388771485668081664 }, { target := 175, numerator := 9440182439900839423506382848 }, { target := 176, numerator := 1521054227092994201490999476224 }, { target := 178, numerator := 59329304540404919334279990738944 }, { target := 181, numerator := 59329282778623400790056436236288 }, { target := 188, numerator := 1521061481020167049565517643776 }, { target := 227, numerator := 4608640571868549813136166748160 }, { target := 230, numerator := 16577143085613177734359920148480 }, { target := 232, numerator := 4608642109336134829497783418880 }, { target := 267, numerator := 2591493008687515019646074880 }, { target := 268, numerator := 38872395130312725294691123200 }, { target := 269, numerator := 68242649228771228850679971840 }, { target := 270, numerator := 2591493008687515019646074880 }, { target := 271, numerator := 43191550144791916994101248000 }, { target := 272, numerator := 2591493008687515019646074880 }, { target := 273, numerator := 68242649228771228850679971840 }, { target := 274, numerator := 67810733727323309680738959360 }, { target := 275, numerator := 43191550144791916994101248000 }, { target := 276, numerator := 1046531260008308148767073239040 }, { target := 277, numerator := 66946902724427471340856934400 }, { target := 278, numerator := 38872395130312725294691123200 }, { target := 279, numerator := 68242649228771228850679971840 }, { target := 280, numerator := 2591493008687515019646074880 }, { target := 281, numerator := 66946902724427471340856934400 }, { target := 282, numerator := 2591493008687515019646074880 }, { target := 283, numerator := 68242649228771228850679971840 }, { target := 284, numerator := 68242649228771228850679971840 }, { target := 285, numerator := 2591493008687515019646074880 }, { target := 286, numerator := 1521053855374683806751908691968 }, { target := 288, numerator := 59329290041389402443102979883008 }, { target := 291, numerator := 59329268279613202087089396514816 }, { target := 298, numerator := 1521061109300083925423103148032 }, { target := 302, numerator := 47447739100437156240283150581760 }, { target := 305, numerator := 170668106547065345044028619489280 }, { target := 307, numerator := 47447754929261233892006486343680 }, { target := 573, numerator := 38045554928056743311313993728 }, { target := 575, numerator := 1483981487661570412649610477568 }, { target := 578, numerator := 1483980943342348027999012519936 }, { target := 585, numerator := 38045736367797538194846646272 }]

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
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 22282912738143405105657937920 }, { target := 11, numerator := 16712184553607553829243453440 }, { target := 12, numerator := 17640639251030195708645867520 }, { target := 13, numerator := 22747140086854726045359144960 }, { target := 14, numerator := 304533140754626536443991818240 }, { target := 15, numerator := 532468768971885117837284474880 }, { target := 16, numerator := 16247957204896232889542246400 }, { target := 17, numerator := 304533140754626536443991818240 }, { target := 18, numerator := 17176411902318874768944660480 }, { target := 19, numerator := 17640639251030195708645867520 }, { target := 20, numerator := 17640639251030195708645867520 }, { target := 21, numerator := 17176411902318874768944660480 }, { target := 22, numerator := 532468768971885117837284474880 }, { target := 23, numerator := 17176411902318874768944660480 }, { target := 24, numerator := 22282912738143405105657937920 }, { target := 25, numerator := 22747140086854726045359144960 }, { target := 26, numerator := 24753298025667961505181597696 }, { target := 27, numerator := 2925680904681648177786069712896 }, { target := 29, numerator := 27764128590022049691598697005056 }, { target := 37, numerator := 2925682911271955057484635308032 }, { target := 44, numerator := 24753298025667961505181597696 }, { target := 141, numerator := 22282928676130284790710534144 }, { target := 142, numerator := 16712196507097713593032900608 }, { target := 143, numerator := 17640651868603142125979172864 }, { target := 144, numerator := 22747156356882999057183670272 }, { target := 145, numerator := 304533358573780558806377299968 }, { target := 146, numerator := 532469149823363263644687138816 }, { target := 147, numerator := 16247968826344999326559764480 }, { target := 148, numerator := 304533358573780558806377299968 }, { target := 149, numerator := 17176424187850427859506036736 }, { target := 150, numerator := 17640651868603142125979172864 }, { target := 151, numerator := 17640651868603142125979172864 }, { target := 152, numerator := 17176424187850427859506036736 }, { target := 153, numerator := 532469149823363263644687138816 }, { target := 154, numerator := 17176424187850427859506036736 }, { target := 155, numerator := 22282928676130284790710534144 }, { target := 156, numerator := 22747156356882999057183670272 }, { target := 157, numerator := 88725593671679803690667999232 }, { target := 158, numerator := 10486795532967034229403924037632 }, { target := 160, numerator := 99517599205251388217543834468352 }, { target := 168, numerator := 10486802725378972595146765369344 }, { target := 175, numerator := 88725593671679803690667999232 }, { target := 263, numerator := 41236759770764430141586145280 }, { target := 265, numerator := 41236749939155930862520893440 }, { target := 267, numerator := 24760491291901740388303503360 }, { target := 268, numerator := 2926531102568032259144008335360 }, { target := 270, numerator := 27772196798488243006832860200960 }, { target := 278, numerator := 2926533109741450863370693509120 }, { target := 285, numerator := 24760491291901740388303503360 }, { target := 338, numerator := 8178686080975205790639980544000 }, { target := 340, numerator := 8178684131024723899016282112000 }, { target := 356, numerator := 15105938961968801197087260672 }, { target := 589, numerator := 4608640571868549813136166748160 }, { target := 592, numerator := 16577143085613177734359920148480 }, { target := 594, numerator := 4608642109336134829497783418880 }, { target := 599, numerator := 8178686080975205790639980544000 }, { target := 601, numerator := 8178684131024723899016282112000 }, { target := 617, numerator := 682760959741479402494987599872 }, { target := 763, numerator := 28121916925968042889805037568 }, { target := 766, numerator := 101153698895309730621794811904 }, { target := 768, numerator := 28121926307592630000706125824 }, { target := 773, numerator := 41236759770764430141586145280 }, { target := 775, numerator := 41236749939155930862520893440 }, { target := 777, numerator := 15186563924930834649820692480 }]

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
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 43579357945468152489808232448 }, { target := 2, numerator := 33018181985314752019575078912 }, { target := 3, numerator := 36790030542512395044658348032 }, { target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 36790030542512395044658348032 }, { target := 6, numerator := 36732002103170892844272451584 }, { target := 7, numerator := 1798881619586568211962789888 }, { target := 8, numerator := 43579357945468152489808232448 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 10, numerator := 37617410638981481080542986240 }, { target := 11, numerator := 6597740408934270911713189560320 }, { target := 16, numerator := 6597741199930562498261564784640 }, { target := 24, numerator := 37616619642689894532167761920 }, { target := 80, numerator := 213199166070509853629334159360 }, { target := 82, numerator := 8343540846811206438576118038528 }, { target := 85, numerator := 8343540846811206438576118038528 }, { target := 92, numerator := 213199166070509853629334159360 }, { target := 131, numerator := 24929027043457761777947770880 }, { target := 134, numerator := 92605123083231339677011148800 }, { target := 136, numerator := 24923779510105652634331381760 }, { target := 176, numerator := 8343783429932003546613248163840 }, { target := 178, numerator := 326533631194224947829628397944832 }, { target := 181, numerator := 326533631194224947829628397944832 }, { target := 188, numerator := 8343783429932003546613248163840 }, { target := 227, numerator := 8030172075353042224753787535360 }, { target := 230, numerator := 29830088118611563140521499033600 }, { target := 232, numerator := 8028481732777091222603531550720 }, { target := 263, numerator := 38628027641222774602109812736 }, { target := 265, numerator := 38628036850863336193032978432 }, { target := 286, numerator := 8343786490148545868911198863360 }, { target := 288, numerator := 326533750955677075222497987657728 }, { target := 291, numerator := 326533750955677075222497987657728 }, { target := 298, numerator := 8343786490148545868911198863360 }, { target := 302, numerator := 85404256936426437501239120887808 }, { target := 305, numerator := 317255531539296292303007729582080 }, { target := 307, numerator := 85386279432294217085576718319616 }, { target := 338, numerator := 6774993136338475204863693160448 }, { target := 340, numerator := 6774994751622904750430723506176 }, { target := 356, numerator := 1798881619586568211962789888 }, { target := 572, numerator := 43579357945468152489808232448 }, { target := 573, numerator := 213202226287052175927284858880 }, { target := 575, numerator := 8343660608263333831445707751424 }, { target := 578, numerator := 8343660608263333831445707751424 }, { target := 585, numerator := 213202226287052175927284858880 }, { target := 589, numerator := 8030196278291919368211824377856 }, { target := 592, numerator := 29830178026498051714637690306560 }, { target := 594, numerator := 8028505930621275791198322163712 }, { target := 599, numerator := 6774993948585413431050681450496 }, { target := 601, numerator := 6774995563870036631401688727552 }, { target := 617, numerator := 33018181985314752019575078912 }, { target := 622, numerator := 36790030542512395044658348032 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 757, numerator := 36790030542512395044658348032 }, { target := 762, numerator := 36732002103170892844272451584 }, { target := 763, numerator := 24929027043457761777947770880 }, { target := 766, numerator := 92605123083231339677011148800 }, { target := 768, numerator := 24923779510105652634331381760 }, { target := 773, numerator := 38627215394284548415121522688 }, { target := 775, numerator := 38627224603731455222067757056 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 782, numerator := 43579357945468152489808232448 }, { target := 783, numerator := 1798881619586568211962789888 }]

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
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 24823482132457052871212400640 }, { target := 27, numerator := 7996173805162391540655540142080 }, { target := 29, numerator := 85042671035712258374970558644224 }, { target := 37, numerator := 7996197905630481304784541319168 }, { target := 44, numerator := 24823482132457052871212400640 }, { target := 80, numerator := 214490238937307450643641794560 }, { target := 82, numerator := 8394310984009104900347280752640 }, { target := 85, numerator := 8394314062757438960567907778560 }, { target := 92, numerator := 214493317685641510864268820480 }, { target := 131, numerator := 24753298025667961505181597696 }, { target := 134, numerator := 88725593671679803690667999232 }, { target := 136, numerator := 24760491291901740388303503360 }, { target := 141, numerator := 37617419607672144257750138880 }, { target := 142, numerator := 6597741981958352009867128995840 }, { target := 147, numerator := 6597742772954832184649900359680 }, { target := 155, numerator := 37616628611191969474978775040 }, { target := 157, numerator := 92213050040950518654068326400 }, { target := 158, numerator := 29703793017317250321980640460800 }, { target := 160, numerator := 315912330026360183990880818954240 }, { target := 168, numerator := 29703882544550299788503605575680 }, { target := 175, numerator := 92213050040950518654068326400 }, { target := 176, numerator := 8394066931874657426294584639488 }, { target := 178, numerator := 328511025004444315701022998659072 }, { target := 181, numerator := 328511145491137372407939033202688 }, { target := 188, numerator := 8394187418567714133210619183104 }, { target := 227, numerator := 2925680904681648177786069712896 }, { target := 230, numerator := 10486795532967034229403924037632 }, { target := 232, numerator := 2926531102568032259144008335360 }, { target := 263, numerator := 21818685389432084165956730880 }, { target := 265, numerator := 21818700995377570524237398016 }, { target := 267, numerator := 24818256816195071477316321280 }, { target := 268, numerator := 7994490619185710475826597724160 }, { target := 270, numerator := 85024769645022826655413801320448 }, { target := 278, numerator := 7994514714580677655507643662336 }, { target := 285, numerator := 24818256816195071477316321280 }, { target := 286, numerator := 8394066931874657426294584639488 }, { target := 288, numerator := 328511025004444315701022998659072 }, { target := 291, numerator := 328511145491137372407939033202688 }, { target := 298, numerator := 8394187418567714133210619183104 }, { target := 302, numerator := 27764128590022049691598697005056 }, { target := 305, numerator := 99517599205251388217543834468352 }, { target := 307, numerator := 27772196798488243006832860200960 }, { target := 338, numerator := 16364014042074063124467548160 }, { target := 340, numerator := 16364025746533177893178048512 }, { target := 352, numerator := 17273125933300399964715745280 }, { target := 354, numerator := 17273138288007243331687940096 }, { target := 479, numerator := 22273241335045252586080829440 }, { target := 481, numerator := 22273257266114603243492343808 }, { target := 554, numerator := 298188700322238483601408655360 }, { target := 556, numerator := 298188913603493463831244439552 }, { target := 568, numerator := 521375669618304177882341048320 }, { target := 570, numerator := 521376042535376528985422823424 }, { target := 573, numerator := 214490238937307450643641794560 }, { target := 575, numerator := 8394310984009104900347280752640 }, { target := 578, numerator := 8394314062757438960567907778560 }, { target := 585, numerator := 214493317685641510864268820480 }, { target := 589, numerator := 2925682911271955057484635308032 }, { target := 592, numerator := 10486802725378972595146765369344 }, { target := 594, numerator := 2926533109741450863370693509120 }, { target := 599, numerator := 15909458096460894704343449600 }, { target := 601, numerator := 15909469475796145173923102720 }, { target := 763, numerator := 24753298025667961505181597696 }, { target := 766, numerator := 88725593671679803690667999232 }, { target := 768, numerator := 24760491291901740388303503360 }]

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
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 15105938961968801197087260672 }, { target := 2, numerator := 682760959741479402494987599872 }, { target := 7, numerator := 15186563924930834649820692480 }, { target := 10, numerator := 41336125456959043226264666112 }, { target := 11, numerator := 8198393758278760503388510617600 }, { target := 16, numerator := 8198393758278760503388510617600 }, { target := 24, numerator := 41336125456959043226264666112 }, { target := 26, numerator := 28149989715512308467933118464 }, { target := 27, numerator := 4613241161408723059767697735680 }, { target := 29, numerator := 47495103951049022630340832788480 }, { target := 37, numerator := 4613241161408723059767697735680 }, { target := 44, numerator := 28149989715512308467933118464 }, { target := 80, numerator := 37985145980886122886875578368 }, { target := 82, numerator := 1518639088593322886467990585344 }, { target := 85, numerator := 1518638717465228926144173047808 }, { target := 92, numerator := 37985145980886122886875578368 }, { target := 131, numerator := 2550356483478609577044344832 }, { target := 134, numerator := 9290338274188127686625329152 }, { target := 136, numerator := 2550358199025808432032645120 }, { target := 141, numerator := 41336115601659921057370341376 }, { target := 142, numerator := 8198391803629602751784996044800 }, { target := 147, numerator := 8198391803629602751784996044800 }, { target := 155, numerator := 41336115601659921057370341376 }, { target := 157, numerator := 101254675884474002875971796992 }, { target := 158, numerator := 16593691269377203866363274199040 }, { target := 160, numerator := 170838476506183952825455151677440 }, { target := 168, numerator := 16593691269377203866363274199040 }, { target := 175, numerator := 101254675884474002875971796992 }, { target := 176, numerator := 1481625213467125238923586961408 }, { target := 178, numerator := 59235101135291542199738422001664 }, { target := 181, numerator := 59235086659297644103244131074048 }, { target := 188, numerator := 1481625213467125238923586961408 }, { target := 267, numerator := 28149999106502131003951153152 }, { target := 268, numerator := 4613242700411089793140905738240 }, { target := 270, numerator := 47495119795674272308669332848640 }, { target := 278, numerator := 4613242700411089793140905738240 }, { target := 285, numerator := 28149999106502131003951153152 }, { target := 286, numerator := 1481624670012175992387708911616 }, { target := 288, numerator := 59235079408063503361047137353728 }, { target := 291, numerator := 59235064932074915008513516240896 }, { target := 298, numerator := 1481624670012175992387708911616 }, { target := 573, numerator := 37985327132535871732168261632 }, { target := 575, numerator := 1518646331002669166031752134656 }, { target := 578, numerator := 1518645959872805291054377992192 }, { target := 585, numerator := 37985327132535871732168261632 }, { target := 613, numerator := 298188700322238483601408655360 }, { target := 615, numerator := 298188913603493463831244439552 }, { target := 618, numerator := 16818569987687231544591646720 }, { target := 620, numerator := 16818582017270210612432994304 }, { target := 694, numerator := 17273125933300399964715745280 }, { target := 696, numerator := 17273138288007243331687940096 }, { target := 708, numerator := 17273125933300399964715745280 }, { target := 710, numerator := 17273138288007243331687940096 }, { target := 739, numerator := 16818569987687231544591646720 }, { target := 741, numerator := 16818582017270210612432994304 }, { target := 753, numerator := 521375669618304177882341048320 }, { target := 755, numerator := 521376042535376528985422823424 }, { target := 758, numerator := 16818569987687231544591646720 }, { target := 760, numerator := 16818582017270210612432994304 }, { target := 773, numerator := 21818685389432084165956730880 }, { target := 775, numerator := 21818700995377570524237398016 }, { target := 778, numerator := 22273241335045252586080829440 }, { target := 780, numerator := 22273257266114603243492343808 }]

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
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected,
    Slot25.Left9.expected,
    Slot25.Left10.expected,
    Slot25.Left11.expected,
    Slot25.Left12.expected,
    Slot25.Left13.expected,
    Slot25.Left14.expected,
    Slot25.Left15.expected,
    Slot25.Left16.expected,
    Slot25.Left17.expected,
    Slot25.Left18.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 44101613899541672293281300480 }, { target := 2, numerator := 32611982909924236616873803776 }, { target := 3, numerator := 36383831467121879641957072896 }, { target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 36325803027780377441571176448 }, { target := 6, numerator := 36964115860536901645816037376 }, { target := 7, numerator := 1798881619586568211962789888 }, { target := 8, numerator := 44101613899541672293281300480 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 227, numerator := 38255347252179143655665172480 }, { target := 230, numerator := 139355074112821915299379937280 }, { target := 232, numerator := 38255372985387126480489676800 }, { target := 253, numerator := 67159387398270052195501080576 }, { target := 256, numerator := 244645574553620695747800334336 }, { target := 258, numerator := 67159432574346288710192988160 }, { target := 302, numerator := 2550356483478609577044344832 }, { target := 305, numerator := 9290338274188127686625329152 }, { target := 307, numerator := 2550358199025808432032645120 }, { target := 328, numerator := 42505941391310159617405747200 }, { target := 331, numerator := 154838971236468794777088819200 }, { target := 333, numerator := 42505969983763473867210752000 }, { target := 342, numerator := 2550356483478609577044344832 }, { target := 345, numerator := 9290338274188127686625329152 }, { target := 347, numerator := 2550358199025808432032645120 }, { target := 443, numerator := 67159387398270052195501080576 }, { target := 446, numerator := 244645574553620695747800334336 }, { target := 448, numerator := 67159432574346288710192988160 }, { target := 469, numerator := 66734327984356950599327023104 }, { target := 472, numerator := 243097184841256007800029446144 }, { target := 474, numerator := 66734372874508653971520880640 }, { target := 518, numerator := 42505941391310159617405747200 }, { target := 521, numerator := 154838971236468794777088819200 }, { target := 523, numerator := 42505969983763473867210752000 }, { target := 544, numerator := 1029918959911445167529741254656 }, { target := 547, numerator := 3751748273059638897448862089216 }, { target := 549, numerator := 1029919652706588971802516520960 }, { target := 558, numerator := 65884209156530747406978908160 }, { target := 561, numerator := 240000405416526631904487669760 }, { target := 563, numerator := 65884253474833384494176665600 }, { target := 589, numerator := 38255347252179143655665172480 }, { target := 592, numerator := 139355074112821915299379937280 }, { target := 594, numerator := 38255372985387126480489676800 }, { target := 603, numerator := 67159387398270052195501080576 }, { target := 606, numerator := 244645574553620695747800334336 }, { target := 608, numerator := 67159432574346288710192988160 }, { target := 658, numerator := 2550356483478609577044344832 }, { target := 661, numerator := 9290338274188127686625329152 }, { target := 663, numerator := 2550358199025808432032645120 }, { target := 684, numerator := 65884209156530747406978908160 }, { target := 687, numerator := 240000405416526631904487669760 }, { target := 689, numerator := 65884253474833384494176665600 }, { target := 698, numerator := 2550356483478609577044344832 }, { target := 701, numerator := 9290338274188127686625329152 }, { target := 703, numerator := 2550358199025808432032645120 }, { target := 729, numerator := 67159387398270052195501080576 }, { target := 732, numerator := 244645574553620695747800334336 }, { target := 734, numerator := 67159432574346288710192988160 }, { target := 743, numerator := 67159387398270052195501080576 }, { target := 746, numerator := 244645574553620695747800334336 }, { target := 748, numerator := 67159432574346288710192988160 }, { target := 763, numerator := 2550356483478609577044344832 }, { target := 766, numerator := 9290338274188127686625329152 }, { target := 768, numerator := 2550358199025808432032645120 }]

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
    Slot27.Left0.expected,
    Slot27.Left2.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 24091470861352862217888858112 }, { target := 11, numerator := 17940457024411705906938511360 }, { target := 12, numerator := 18965625997235231958763569152 }, { target := 13, numerator := 24604055347764625243801387008 }, { target := 14, numerator := 329591824762763625661756080128 }, { target := 15, numerator := 596135757696880399136271106048 }, { target := 16, numerator := 17940457024411705906938511360 }, { target := 17, numerator := 329591824762763625661756080128 }, { target := 18, numerator := 19478210483646994984676098048 }, { target := 19, numerator := 19478210483646994984676098048 }, { target := 20, numerator := 18965625997235231958763569152 }, { target := 21, numerator := 18965625997235231958763569152 }, { target := 22, numerator := 596135757696880399136271106048 }, { target := 23, numerator := 18965625997235231958763569152 }, { target := 24, numerator := 24091470861352862217888858112 }, { target := 25, numerator := 24604055347764625243801387008 }, { target := 26, numerator := 3182442986707934596332257280 }, { target := 27, numerator := 46145423307265051646817730560 }, { target := 28, numerator := 81682703325503654639194603520 }, { target := 29, numerator := 2652035822256612163610214400 }, { target := 30, numerator := 50919087787326953541316116480 }, { target := 31, numerator := 2652035822256612163610214400 }, { target := 32, numerator := 81152296161052332206472560640 }, { target := 33, numerator := 84865146312211589235526860800 }, { target := 34, numerator := 50919087787326953541316116480 }, { target := 35, numerator := 1300027960070191282601727098880 }, { target := 36, numerator := 83273924818857621937360732160 }, { target := 37, numerator := 46145423307265051646817730560 }, { target := 38, numerator := 81152296161052332206472560640 }, { target := 39, numerator := 2652035822256612163610214400 }, { target := 40, numerator := 83273924818857621937360732160 }, { target := 41, numerator := 2652035822256612163610214400 }, { target := 42, numerator := 81152296161052332206472560640 }, { target := 43, numerator := 84865146312211589235526860800 }, { target := 44, numerator := 3182442986707934596332257280 }, { target := 141, numerator := 24091476605207798169200492544 }, { target := 142, numerator := 17940461301750487998340792320 }, { target := 143, numerator := 18965630518993373026817409024 }, { target := 144, numerator := 24604061213829240683438800896 }, { target := 145, numerator := 329591903343587536655232270336 }, { target := 146, numerator := 596135899826737644059152613376 }, { target := 147, numerator := 17940461301750487998340792320 }, { target := 148, numerator := 329591903343587536655232270336 }, { target := 149, numerator := 19478215127614815541055717376 }, { target := 150, numerator := 19478215127614815541055717376 }, { target := 151, numerator := 18965630518993373026817409024 }, { target := 152, numerator := 18965630518993373026817409024 }, { target := 153, numerator := 596135899826737644059152613376 }, { target := 154, numerator := 18965630518993373026817409024 }, { target := 155, numerator := 24091476605207798169200492544 }, { target := 156, numerator := 24604061213829240683438800896 }]

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
    Slot28.Left3.expected,
    Slot28.Left5.expected,
    Slot29.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 142294346861828149579087872 }, { target := 81, numerator := 160654907747225330169937920 }, { target := 82, numerator := 137704206640478854431375360 }, { target := 83, numerator := 1813105387432971583346442240 }, { target := 84, numerator := 160654907747225330169937920 }, { target := 85, numerator := 137704206640478854431375360 }, { target := 86, numerator := 160654907747225330169937920 }, { target := 87, numerator := 160654907747225330169937920 }, { target := 88, numerator := 6660293461177827259330854912 }, { target := 89, numerator := 165245047968574625317650432 }, { target := 90, numerator := 1813105387432971583346442240 }, { target := 91, numerator := 6660293461177827259330854912 }, { target := 92, numerator := 142294346861828149579087872 }, { target := 93, numerator := 160654907747225330169937920 }, { target := 94, numerator := 165245047968574625317650432 }, { target := 95, numerator := 160654907747225330169937920 }, { target := 157, numerator := 11623931294666812211331072000 }, { target := 158, numerator := 168547003772668777064300544000 }, { target := 159, numerator := 298347569896448180090830848000 }, { target := 160, numerator := 9686609412222343509442560000 }, { target := 161, numerator := 185982900714668995381297152000 }, { target := 162, numerator := 9686609412222343509442560000 }, { target := 163, numerator := 296410248014003711388942336000 }, { target := 164, numerator := 309971501191114992302161920000 }, { target := 165, numerator := 185982900714668995381297152000 }, { target := 166, numerator := 4748375933871392788328742912000 }, { target := 167, numerator := 304159535543781586196496384000 }, { target := 168, numerator := 168547003772668777064300544000 }, { target := 169, numerator := 296410248014003711388942336000 }, { target := 170, numerator := 9686609412222343509442560000 }, { target := 171, numerator := 304159535543781586196496384000 }, { target := 172, numerator := 9686609412222343509442560000 }, { target := 173, numerator := 296410248014003711388942336000 }, { target := 174, numerator := 309971501191114992302161920000 }, { target := 175, numerator := 11623931294666812211331072000 }, { target := 267, numerator := 3182441914490935311964569600 }, { target := 268, numerator := 46145407760118562023486259200 }, { target := 269, numerator := 81682675805267339673757286400 }, { target := 270, numerator := 2652034928742446093303808000 }, { target := 271, numerator := 50919070631854964991433113600 }, { target := 272, numerator := 2652034928742446093303808000 }, { target := 273, numerator := 81152268819518850455096524800 }, { target := 274, numerator := 84865117719758274985721856000 }, { target := 275, numerator := 50919070631854964991433113600 }, { target := 276, numerator := 1300027522069547074937526681600 }, { target := 277, numerator := 83273896762512807329739571200 }, { target := 278, numerator := 46145407760118562023486259200 }, { target := 279, numerator := 81152268819518850455096524800 }, { target := 280, numerator := 2652034928742446093303808000 }, { target := 281, numerator := 83273896762512807329739571200 }, { target := 282, numerator := 2652034928742446093303808000 }, { target := 283, numerator := 81152268819518850455096524800 }, { target := 284, numerator := 84865117719758274985721856000 }, { target := 285, numerator := 3182441914490935311964569600 }]

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
    Slot29.Left1.expected,
    Slot29.Left2.expected,
    Slot29.Left3.expected,
    Slot29.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 115, numerator := 162057450592637614798405632 }, { target := 116, numerator := 182968089378784403804651520 }, { target := 117, numerator := 156829790896100917546844160 }, { target := 118, numerator := 2064925580131995414366781440 }, { target := 119, numerator := 182968089378784403804651520 }, { target := 120, numerator := 156829790896100917546844160 }, { target := 121, numerator := 182968089378784403804651520 }, { target := 122, numerator := 182968089378784403804651520 }, { target := 123, numerator := 7585334219674747712015695872 }, { target := 124, numerator := 188195749075321101056212992 }, { target := 125, numerator := 2064925580131995414366781440 }, { target := 126, numerator := 7585334219674747712015695872 }, { target := 127, numerator := 162057450592637614798405632 }, { target := 128, numerator := 182968089378784403804651520 }, { target := 129, numerator := 188195749075321101056212992 }, { target := 130, numerator := 182968089378784403804651520 }, { target := 176, numerator := 126483863877180577403633664 }, { target := 177, numerator := 142804362441978071262167040 }, { target := 178, numerator := 122403739235981203939000320 }, { target := 179, numerator := 1611649233273752518530170880 }, { target := 180, numerator := 142804362441978071262167040 }, { target := 181, numerator := 122403739235981203939000320 }, { target := 182, numerator := 142804362441978071262167040 }, { target := 183, numerator := 142804362441978071262167040 }, { target := 184, numerator := 5920260854380290897182982144 }, { target := 185, numerator := 146884487083177444726800384 }, { target := 186, numerator := 1611649233273752518530170880 }, { target := 187, numerator := 5920260854380290897182982144 }, { target := 188, numerator := 126483863877180577403633664 }, { target := 189, numerator := 142804362441978071262167040 }, { target := 190, numerator := 146884487083177444726800384 }, { target := 191, numerator := 142804362441978071262167040 }, { target := 211, numerator := 1695674300103452115817463808 }, { target := 212, numerator := 1914470983987768517858426880 }, { target := 213, numerator := 1640975129132373015307223040 }, { target := 214, numerator := 21606172533576244701545103360 }, { target := 215, numerator := 1914470983987768517858426880 }, { target := 216, numerator := 1640975129132373015307223040 }, { target := 217, numerator := 1914470983987768517858426880 }, { target := 218, numerator := 1914470983987768517858426880 }, { target := 219, numerator := 79368497079035774840359354368 }, { target := 220, numerator := 1969170154958847618368667648 }, { target := 221, numerator := 21606172533576244701545103360 }, { target := 222, numerator := 79368497079035774840359354368 }, { target := 223, numerator := 1695674300103452115817463808 }, { target := 224, numerator := 1914470983987768517858426880 }, { target := 225, numerator := 1969170154958847618368667648 }, { target := 226, numerator := 1914470983987768517858426880 }, { target := 237, numerator := 150199588354151935666814976 }, { target := 238, numerator := 169580180399848959623823360 }, { target := 239, numerator := 145354440342727679677562880 }, { target := 240, numerator := 1913833464512581115754577920 }, { target := 241, numerator := 169580180399848959623823360 }, { target := 242, numerator := 145354440342727679677562880 }, { target := 243, numerator := 169580180399848959623823360 }, { target := 244, numerator := 169580180399848959623823360 }, { target := 245, numerator := 7030309764576595440404791296 }, { target := 246, numerator := 174425328411273215613075456 }, { target := 247, numerator := 1913833464512581115754577920 }, { target := 248, numerator := 7030309764576595440404791296 }, { target := 249, numerator := 150199588354151935666814976 }, { target := 250, numerator := 169580180399848959623823360 }, { target := 251, numerator := 174425328411273215613075456 }, { target := 252, numerator := 169580180399848959623823360 }]

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
    Slot29.Left5.expected,
    Slot29.Left6.expected,
    Slot29.Left7.expected,
    Slot29.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 286, numerator := 126483863877180577403633664 }, { target := 287, numerator := 142804362441978071262167040 }, { target := 288, numerator := 122403739235981203939000320 }, { target := 289, numerator := 1611649233273752518530170880 }, { target := 290, numerator := 142804362441978071262167040 }, { target := 291, numerator := 122403739235981203939000320 }, { target := 292, numerator := 142804362441978071262167040 }, { target := 293, numerator := 142804362441978071262167040 }, { target := 294, numerator := 5920260854380290897182982144 }, { target := 295, numerator := 146884487083177444726800384 }, { target := 296, numerator := 1611649233273752518530170880 }, { target := 297, numerator := 5920260854380290897182982144 }, { target := 298, numerator := 126483863877180577403633664 }, { target := 299, numerator := 142804362441978071262167040 }, { target := 300, numerator := 146884487083177444726800384 }, { target := 301, numerator := 142804362441978071262167040 }, { target := 312, numerator := 150199588354151935666814976 }, { target := 313, numerator := 169580180399848959623823360 }, { target := 314, numerator := 145354440342727679677562880 }, { target := 315, numerator := 1913833464512581115754577920 }, { target := 316, numerator := 169580180399848959623823360 }, { target := 317, numerator := 145354440342727679677562880 }, { target := 318, numerator := 169580180399848959623823360 }, { target := 319, numerator := 169580180399848959623823360 }, { target := 320, numerator := 7030309764576595440404791296 }, { target := 321, numerator := 174425328411273215613075456 }, { target := 322, numerator := 1913833464512581115754577920 }, { target := 323, numerator := 7030309764576595440404791296 }, { target := 324, numerator := 150199588354151935666814976 }, { target := 325, numerator := 169580180399848959623823360 }, { target := 326, numerator := 174425328411273215613075456 }, { target := 327, numerator := 169580180399848959623823360 }, { target := 392, numerator := 146246967607990042622951424 }, { target := 393, numerator := 165117544073537144896880640 }, { target := 394, numerator := 141529323491603267054469120 }, { target := 395, numerator := 1863469425972776349550510080 }, { target := 396, numerator := 165117544073537144896880640 }, { target := 397, numerator := 141529323491603267054469120 }, { target := 398, numerator := 165117544073537144896880640 }, { target := 399, numerator := 165117544073537144896880640 }, { target := 400, numerator := 6845301612877211349867823104 }, { target := 401, numerator := 169835188189923920465362944 }, { target := 402, numerator := 1863469425972776349550510080 }, { target := 403, numerator := 6845301612877211349867823104 }, { target := 404, numerator := 146246967607990042622951424 }, { target := 405, numerator := 165117544073537144896880640 }, { target := 406, numerator := 169835188189923920465362944 }, { target := 407, numerator := 165117544073537144896880640 }, { target := 427, numerator := 5525763803134326475321245696 }, { target := 428, numerator := 6238765584183916988265922560 }, { target := 429, numerator := 5347513357871928847085076480 }, { target := 430, numerator := 70408925878647063153286840320 }, { target := 431, numerator := 6238765584183916988265922560 }, { target := 432, numerator := 5347513357871928847085076480 }, { target := 433, numerator := 6238765584183916988265922560 }, { target := 434, numerator := 6238765584183916988265922560 }, { target := 435, numerator := 258641396075738958570681532416 }, { target := 436, numerator := 6417016029446314616502091776 }, { target := 437, numerator := 70408925878647063153286840320 }, { target := 438, numerator := 258641396075738958570681532416 }, { target := 439, numerator := 5525763803134326475321245696 }, { target := 440, numerator := 6238765584183916988265922560 }, { target := 441, numerator := 6417016029446314616502091776 }, { target := 442, numerator := 6238765584183916988265922560 }]

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
    Slot29.Left9.expected,
    Slot29.Left10.expected,
    Slot29.Left11.expected,
    Slot29.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 453, numerator := 146246967607990042622951424 }, { target := 454, numerator := 165117544073537144896880640 }, { target := 455, numerator := 141529323491603267054469120 }, { target := 456, numerator := 1863469425972776349550510080 }, { target := 457, numerator := 165117544073537144896880640 }, { target := 458, numerator := 141529323491603267054469120 }, { target := 459, numerator := 165117544073537144896880640 }, { target := 460, numerator := 165117544073537144896880640 }, { target := 461, numerator := 6845301612877211349867823104 }, { target := 462, numerator := 169835188189923920465362944 }, { target := 463, numerator := 1863469425972776349550510080 }, { target := 464, numerator := 6845301612877211349867823104 }, { target := 465, numerator := 146246967607990042622951424 }, { target := 466, numerator := 165117544073537144896880640 }, { target := 467, numerator := 169835188189923920465362944 }, { target := 468, numerator := 165117544073537144896880640 }, { target := 502, numerator := 1695674300103452115817463808 }, { target := 503, numerator := 1914470983987768517858426880 }, { target := 504, numerator := 1640975129132373015307223040 }, { target := 505, numerator := 21606172533576244701545103360 }, { target := 506, numerator := 1914470983987768517858426880 }, { target := 507, numerator := 1640975129132373015307223040 }, { target := 508, numerator := 1914470983987768517858426880 }, { target := 509, numerator := 1914470983987768517858426880 }, { target := 510, numerator := 79368497079035774840359354368 }, { target := 511, numerator := 1969170154958847618368667648 }, { target := 512, numerator := 21606172533576244701545103360 }, { target := 513, numerator := 79368497079035774840359354368 }, { target := 514, numerator := 1695674300103452115817463808 }, { target := 515, numerator := 1914470983987768517858426880 }, { target := 516, numerator := 1969170154958847618368667648 }, { target := 517, numerator := 1914470983987768517858426880 }, { target := 528, numerator := 5525763803134326475321245696 }, { target := 529, numerator := 6238765584183916988265922560 }, { target := 530, numerator := 5347513357871928847085076480 }, { target := 531, numerator := 70408925878647063153286840320 }, { target := 532, numerator := 6238765584183916988265922560 }, { target := 533, numerator := 5347513357871928847085076480 }, { target := 534, numerator := 6238765584183916988265922560 }, { target := 535, numerator := 6238765584183916988265922560 }, { target := 536, numerator := 258641396075738958570681532416 }, { target := 537, numerator := 6417016029446314616502091776 }, { target := 538, numerator := 70408925878647063153286840320 }, { target := 539, numerator := 258641396075738958570681532416 }, { target := 540, numerator := 5525763803134326475321245696 }, { target := 541, numerator := 6238765584183916988265922560 }, { target := 542, numerator := 6417016029446314616502091776 }, { target := 543, numerator := 6238765584183916988265922560 }, { target := 573, numerator := 142294346861828149579087872 }, { target := 574, numerator := 160654907747225330169937920 }, { target := 575, numerator := 137704206640478854431375360 }, { target := 576, numerator := 1813105387432971583346442240 }, { target := 577, numerator := 160654907747225330169937920 }, { target := 578, numerator := 137704206640478854431375360 }, { target := 579, numerator := 160654907747225330169937920 }, { target := 580, numerator := 160654907747225330169937920 }, { target := 581, numerator := 6660293461177827259330854912 }, { target := 582, numerator := 165245047968574625317650432 }, { target := 583, numerator := 1813105387432971583346442240 }, { target := 584, numerator := 6660293461177827259330854912 }, { target := 585, numerator := 142294346861828149579087872 }, { target := 586, numerator := 160654907747225330169937920 }, { target := 587, numerator := 165245047968574625317650432 }, { target := 588, numerator := 160654907747225330169937920 }]

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
    Slot29.Left13.expected,
    Slot29.Left14.expected,
    Slot29.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 642, numerator := 146246967607990042622951424 }, { target := 643, numerator := 165117544073537144896880640 }, { target := 644, numerator := 141529323491603267054469120 }, { target := 645, numerator := 1863469425972776349550510080 }, { target := 646, numerator := 165117544073537144896880640 }, { target := 647, numerator := 141529323491603267054469120 }, { target := 648, numerator := 165117544073537144896880640 }, { target := 649, numerator := 165117544073537144896880640 }, { target := 650, numerator := 6845301612877211349867823104 }, { target := 651, numerator := 169835188189923920465362944 }, { target := 652, numerator := 1863469425972776349550510080 }, { target := 653, numerator := 6845301612877211349867823104 }, { target := 654, numerator := 146246967607990042622951424 }, { target := 655, numerator := 165117544073537144896880640 }, { target := 656, numerator := 169835188189923920465362944 }, { target := 657, numerator := 165117544073537144896880640 }, { target := 668, numerator := 146246967607990042622951424 }, { target := 669, numerator := 165117544073537144896880640 }, { target := 670, numerator := 141529323491603267054469120 }, { target := 671, numerator := 1863469425972776349550510080 }, { target := 672, numerator := 165117544073537144896880640 }, { target := 673, numerator := 141529323491603267054469120 }, { target := 674, numerator := 165117544073537144896880640 }, { target := 675, numerator := 165117544073537144896880640 }, { target := 676, numerator := 6845301612877211349867823104 }, { target := 677, numerator := 169835188189923920465362944 }, { target := 678, numerator := 1863469425972776349550510080 }, { target := 679, numerator := 6845301612877211349867823104 }, { target := 680, numerator := 146246967607990042622951424 }, { target := 681, numerator := 165117544073537144896880640 }, { target := 682, numerator := 169835188189923920465362944 }, { target := 683, numerator := 165117544073537144896880640 }, { target := 713, numerator := 162057450592637614798405632 }, { target := 714, numerator := 182968089378784403804651520 }, { target := 715, numerator := 156829790896100917546844160 }, { target := 716, numerator := 2064925580131995414366781440 }, { target := 717, numerator := 182968089378784403804651520 }, { target := 718, numerator := 156829790896100917546844160 }, { target := 719, numerator := 182968089378784403804651520 }, { target := 720, numerator := 182968089378784403804651520 }, { target := 721, numerator := 7585334219674747712015695872 }, { target := 722, numerator := 188195749075321101056212992 }, { target := 723, numerator := 2064925580131995414366781440 }, { target := 724, numerator := 7585334219674747712015695872 }, { target := 725, numerator := 162057450592637614798405632 }, { target := 726, numerator := 182968089378784403804651520 }, { target := 727, numerator := 188195749075321101056212992 }, { target := 728, numerator := 182968089378784403804651520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1
