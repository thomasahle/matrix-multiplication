import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 27, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 142294346861828149579087872 }, some { target := 81, numerator := 162057450592637614798405632 }, some { target := 82, numerator := 126483863877180577403633664 }, some { target := 83, numerator := 1695674300103452115817463808 }, some { target := 84, numerator := 150199588354151935666814976 }, some { target := 85, numerator := 126483863877180577403633664 }, some { target := 86, numerator := 150199588354151935666814976 }, some { target := 87, numerator := 146246967607990042622951424 }, some { target := 88, numerator := 5525763803134326475321245696 }, some { target := 89, numerator := 146246967607990042622951424 }, some { target := 90, numerator := 1695674300103452115817463808 }, some { target := 91, numerator := 5525763803134326475321245696 }, some { target := 92, numerator := 142294346861828149579087872 }, some { target := 93, numerator := 146246967607990042622951424 }, some { target := 94, numerator := 146246967607990042622951424 }, some { target := 95, numerator := 162057450592637614798405632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 115, numerator := 160654907747225330169937920 }, some { target := 116, numerator := 182968089378784403804651520 }, some { target := 117, numerator := 142804362441978071262167040 }, some { target := 118, numerator := 1914470983987768517858426880 }, some { target := 119, numerator := 169580180399848959623823360 }, some { target := 120, numerator := 142804362441978071262167040 }, some { target := 121, numerator := 169580180399848959623823360 }, some { target := 122, numerator := 165117544073537144896880640 }, some { target := 123, numerator := 6238765584183916988265922560 }, some { target := 124, numerator := 165117544073537144896880640 }, some { target := 125, numerator := 1914470983987768517858426880 }, some { target := 126, numerator := 6238765584183916988265922560 }, some { target := 127, numerator := 160654907747225330169937920 }, some { target := 128, numerator := 165117544073537144896880640 }, some { target := 129, numerator := 165117544073537144896880640 }, some { target := 130, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 137704206640478854431375360 }, some { target := 177, numerator := 156829790896100917546844160 }, some { target := 178, numerator := 122403739235981203939000320 }, some { target := 179, numerator := 1640975129132373015307223040 }, some { target := 180, numerator := 145354440342727679677562880 }, some { target := 181, numerator := 122403739235981203939000320 }, some { target := 182, numerator := 145354440342727679677562880 }, some { target := 183, numerator := 141529323491603267054469120 }, some { target := 184, numerator := 5347513357871928847085076480 }, some { target := 185, numerator := 141529323491603267054469120 }, some { target := 186, numerator := 1640975129132373015307223040 }, some { target := 187, numerator := 5347513357871928847085076480 }, some { target := 188, numerator := 137704206640478854431375360 }, some { target := 189, numerator := 141529323491603267054469120 }, some { target := 190, numerator := 141529323491603267054469120 }, some { target := 191, numerator := 156829790896100917546844160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 211, numerator := 1813105387432971583346442240 }, some { target := 212, numerator := 2064925580131995414366781440 }, some { target := 213, numerator := 1611649233273752518530170880 }, some { target := 214, numerator := 21606172533576244701545103360 }, some { target := 215, numerator := 1913833464512581115754577920 }, some { target := 216, numerator := 1611649233273752518530170880 }, some { target := 217, numerator := 1913833464512581115754577920 }, some { target := 218, numerator := 1863469425972776349550510080 }, some { target := 219, numerator := 70408925878647063153286840320 }, some { target := 220, numerator := 1863469425972776349550510080 }, some { target := 221, numerator := 21606172533576244701545103360 }, some { target := 222, numerator := 70408925878647063153286840320 }, some { target := 223, numerator := 1813105387432971583346442240 }, some { target := 224, numerator := 1863469425972776349550510080 }, some { target := 225, numerator := 1863469425972776349550510080 }, some { target := 226, numerator := 2064925580131995414366781440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 237, numerator := 160654907747225330169937920 }, some { target := 238, numerator := 182968089378784403804651520 }, some { target := 239, numerator := 142804362441978071262167040 }, some { target := 240, numerator := 1914470983987768517858426880 }, some { target := 241, numerator := 169580180399848959623823360 }, some { target := 242, numerator := 142804362441978071262167040 }, some { target := 243, numerator := 169580180399848959623823360 }, some { target := 244, numerator := 165117544073537144896880640 }, some { target := 245, numerator := 6238765584183916988265922560 }, some { target := 246, numerator := 165117544073537144896880640 }, some { target := 247, numerator := 1914470983987768517858426880 }, some { target := 248, numerator := 6238765584183916988265922560 }, some { target := 249, numerator := 160654907747225330169937920 }, some { target := 250, numerator := 165117544073537144896880640 }, some { target := 251, numerator := 165117544073537144896880640 }, some { target := 252, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 137704206640478854431375360 }, some { target := 287, numerator := 156829790896100917546844160 }, some { target := 288, numerator := 122403739235981203939000320 }, some { target := 289, numerator := 1640975129132373015307223040 }, some { target := 290, numerator := 145354440342727679677562880 }, some { target := 291, numerator := 122403739235981203939000320 }, some { target := 292, numerator := 145354440342727679677562880 }, some { target := 293, numerator := 141529323491603267054469120 }, some { target := 294, numerator := 5347513357871928847085076480 }, some { target := 295, numerator := 141529323491603267054469120 }, some { target := 296, numerator := 1640975129132373015307223040 }, some { target := 297, numerator := 5347513357871928847085076480 }, some { target := 298, numerator := 137704206640478854431375360 }, some { target := 299, numerator := 141529323491603267054469120 }, some { target := 300, numerator := 141529323491603267054469120 }, some { target := 301, numerator := 156829790896100917546844160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 160654907747225330169937920 }, some { target := 313, numerator := 182968089378784403804651520 }, some { target := 314, numerator := 142804362441978071262167040 }, some { target := 315, numerator := 1914470983987768517858426880 }, some { target := 316, numerator := 169580180399848959623823360 }, some { target := 317, numerator := 142804362441978071262167040 }, some { target := 318, numerator := 169580180399848959623823360 }, some { target := 319, numerator := 165117544073537144896880640 }, some { target := 320, numerator := 6238765584183916988265922560 }, some { target := 321, numerator := 165117544073537144896880640 }, some { target := 322, numerator := 1914470983987768517858426880 }, some { target := 323, numerator := 6238765584183916988265922560 }, some { target := 324, numerator := 160654907747225330169937920 }, some { target := 325, numerator := 165117544073537144896880640 }, some { target := 326, numerator := 165117544073537144896880640 }, some { target := 327, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 160654907747225330169937920 }, some { target := 393, numerator := 182968089378784403804651520 }, some { target := 394, numerator := 142804362441978071262167040 }, some { target := 395, numerator := 1914470983987768517858426880 }, some { target := 396, numerator := 169580180399848959623823360 }, some { target := 397, numerator := 142804362441978071262167040 }, some { target := 398, numerator := 169580180399848959623823360 }, some { target := 399, numerator := 165117544073537144896880640 }, some { target := 400, numerator := 6238765584183916988265922560 }, some { target := 401, numerator := 165117544073537144896880640 }, some { target := 402, numerator := 1914470983987768517858426880 }, some { target := 403, numerator := 6238765584183916988265922560 }, some { target := 404, numerator := 160654907747225330169937920 }, some { target := 405, numerator := 165117544073537144896880640 }, some { target := 406, numerator := 165117544073537144896880640 }, some { target := 407, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 6660293461177827259330854912 }, some { target := 428, numerator := 7585334219674747712015695872 }, some { target := 429, numerator := 5920260854380290897182982144 }, some { target := 430, numerator := 79368497079035774840359354368 }, some { target := 431, numerator := 7030309764576595440404791296 }, some { target := 432, numerator := 5920260854380290897182982144 }, some { target := 433, numerator := 7030309764576595440404791296 }, some { target := 434, numerator := 6845301612877211349867823104 }, some { target := 435, numerator := 258641396075738958570681532416 }, some { target := 436, numerator := 6845301612877211349867823104 }, some { target := 437, numerator := 79368497079035774840359354368 }, some { target := 438, numerator := 258641396075738958570681532416 }, some { target := 439, numerator := 6660293461177827259330854912 }, some { target := 440, numerator := 6845301612877211349867823104 }, some { target := 441, numerator := 6845301612877211349867823104 }, some { target := 442, numerator := 7585334219674747712015695872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 165245047968574625317650432 }, some { target := 454, numerator := 188195749075321101056212992 }, some { target := 455, numerator := 146884487083177444726800384 }, some { target := 456, numerator := 1969170154958847618368667648 }, some { target := 457, numerator := 174425328411273215613075456 }, some { target := 458, numerator := 146884487083177444726800384 }, some { target := 459, numerator := 174425328411273215613075456 }, some { target := 460, numerator := 169835188189923920465362944 }, some { target := 461, numerator := 6417016029446314616502091776 }, some { target := 462, numerator := 169835188189923920465362944 }, some { target := 463, numerator := 1969170154958847618368667648 }, some { target := 464, numerator := 6417016029446314616502091776 }, some { target := 465, numerator := 165245047968574625317650432 }, some { target := 466, numerator := 169835188189923920465362944 }, some { target := 467, numerator := 169835188189923920465362944 }, some { target := 468, numerator := 188195749075321101056212992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 1813105387432971583346442240 }, some { target := 503, numerator := 2064925580131995414366781440 }, some { target := 504, numerator := 1611649233273752518530170880 }, some { target := 505, numerator := 21606172533576244701545103360 }, some { target := 506, numerator := 1913833464512581115754577920 }, some { target := 507, numerator := 1611649233273752518530170880 }, some { target := 508, numerator := 1913833464512581115754577920 }, some { target := 509, numerator := 1863469425972776349550510080 }, some { target := 510, numerator := 70408925878647063153286840320 }, some { target := 511, numerator := 1863469425972776349550510080 }, some { target := 512, numerator := 21606172533576244701545103360 }, some { target := 513, numerator := 70408925878647063153286840320 }, some { target := 514, numerator := 1813105387432971583346442240 }, some { target := 515, numerator := 1863469425972776349550510080 }, some { target := 516, numerator := 1863469425972776349550510080 }, some { target := 517, numerator := 2064925580131995414366781440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 6660293461177827259330854912 }, some { target := 529, numerator := 7585334219674747712015695872 }, some { target := 530, numerator := 5920260854380290897182982144 }, some { target := 531, numerator := 79368497079035774840359354368 }, some { target := 532, numerator := 7030309764576595440404791296 }, some { target := 533, numerator := 5920260854380290897182982144 }, some { target := 534, numerator := 7030309764576595440404791296 }, some { target := 535, numerator := 6845301612877211349867823104 }, some { target := 536, numerator := 258641396075738958570681532416 }, some { target := 537, numerator := 6845301612877211349867823104 }, some { target := 538, numerator := 79368497079035774840359354368 }, some { target := 539, numerator := 258641396075738958570681532416 }, some { target := 540, numerator := 6660293461177827259330854912 }, some { target := 541, numerator := 6845301612877211349867823104 }, some { target := 542, numerator := 6845301612877211349867823104 }, some { target := 543, numerator := 7585334219674747712015695872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 142294346861828149579087872 }, some { target := 574, numerator := 162057450592637614798405632 }, some { target := 575, numerator := 126483863877180577403633664 }, some { target := 576, numerator := 1695674300103452115817463808 }, some { target := 577, numerator := 150199588354151935666814976 }, some { target := 578, numerator := 126483863877180577403633664 }, some { target := 579, numerator := 150199588354151935666814976 }, some { target := 580, numerator := 146246967607990042622951424 }, some { target := 581, numerator := 5525763803134326475321245696 }, some { target := 582, numerator := 146246967607990042622951424 }, some { target := 583, numerator := 1695674300103452115817463808 }, some { target := 584, numerator := 5525763803134326475321245696 }, some { target := 585, numerator := 142294346861828149579087872 }, some { target := 586, numerator := 146246967607990042622951424 }, some { target := 587, numerator := 146246967607990042622951424 }, some { target := 588, numerator := 162057450592637614798405632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 642, numerator := 160654907747225330169937920 }, some { target := 643, numerator := 182968089378784403804651520 }, some { target := 644, numerator := 142804362441978071262167040 }, some { target := 645, numerator := 1914470983987768517858426880 }, some { target := 646, numerator := 169580180399848959623823360 }, some { target := 647, numerator := 142804362441978071262167040 }, some { target := 648, numerator := 169580180399848959623823360 }, some { target := 649, numerator := 165117544073537144896880640 }, some { target := 650, numerator := 6238765584183916988265922560 }, some { target := 651, numerator := 165117544073537144896880640 }, some { target := 652, numerator := 1914470983987768517858426880 }, some { target := 653, numerator := 6238765584183916988265922560 }, some { target := 654, numerator := 160654907747225330169937920 }, some { target := 655, numerator := 165117544073537144896880640 }, some { target := 656, numerator := 165117544073537144896880640 }, some { target := 657, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 668, numerator := 165245047968574625317650432 }, some { target := 669, numerator := 188195749075321101056212992 }, some { target := 670, numerator := 146884487083177444726800384 }, some { target := 671, numerator := 1969170154958847618368667648 }, some { target := 672, numerator := 174425328411273215613075456 }, some { target := 673, numerator := 146884487083177444726800384 }, some { target := 674, numerator := 174425328411273215613075456 }, some { target := 675, numerator := 169835188189923920465362944 }, some { target := 676, numerator := 6417016029446314616502091776 }, some { target := 677, numerator := 169835188189923920465362944 }, some { target := 678, numerator := 1969170154958847618368667648 }, some { target := 679, numerator := 6417016029446314616502091776 }, some { target := 680, numerator := 165245047968574625317650432 }, some { target := 681, numerator := 169835188189923920465362944 }, some { target := 682, numerator := 169835188189923920465362944 }, some { target := 683, numerator := 188195749075321101056212992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 713, numerator := 160654907747225330169937920 }, some { target := 714, numerator := 182968089378784403804651520 }, some { target := 715, numerator := 142804362441978071262167040 }, some { target := 716, numerator := 1914470983987768517858426880 }, some { target := 717, numerator := 169580180399848959623823360 }, some { target := 718, numerator := 142804362441978071262167040 }, some { target := 719, numerator := 169580180399848959623823360 }, some { target := 720, numerator := 165117544073537144896880640 }, some { target := 721, numerator := 6238765584183916988265922560 }, some { target := 722, numerator := 165117544073537144896880640 }, some { target := 723, numerator := 1914470983987768517858426880 }, some { target := 724, numerator := 6238765584183916988265922560 }, some { target := 725, numerator := 160654907747225330169937920 }, some { target := 726, numerator := 165117544073537144896880640 }, some { target := 727, numerator := 165117544073537144896880640 }, some { target := 728, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 147, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 3018187864813331520392527872 }, some { target := 134, numerator := 11023986453651750935907532800 }, some { target := 136, numerator := 3018186847936564457153495040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 43763724039793307045691654144 }, some { target := 230, numerator := 159847803577950388570659225600 }, some { target := 232, numerator := 43763709295080184628725678080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 77466821863542175690074882048 }, some { target := 256, numerator := 282948985643728274021626675200 }, some { target := 258, numerator := 77466795763705154400273039360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 2515156554011109600327106560 }, some { target := 305, numerator := 9186655378043125779922944000 }, some { target := 307, numerator := 2515155706613803714294579200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 48291005837013304326280445952 }, some { target := 331, numerator := 176383783258428014974520524800 }, some { target := 333, numerator := 48290989566985031314455920640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 2515156554011109600327106560 }, some { target := 345, numerator := 9186655378043125779922944000 }, some { target := 347, numerator := 2515155706613803714294579200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 76963790552739953770009460736 }, some { target := 446, numerator := 281111654568119648865642086400 }, some { target := 448, numerator := 76963764622382393657414123520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 80485009728355507210467409920 }, some { target := 472, numerator := 293972972097380024957534208000 }, some { target := 474, numerator := 80484982611641718857426534400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 48291005837013304326280445952 }, some { target := 521, numerator := 176383783258428014974520524800 }, some { target := 523, numerator := 48290989566985031314455920640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 1232929742776245926080347635712 }, some { target := 547, numerator := 4503298466316740257318227148800 }, some { target := 549, numerator := 1232929327382086580747202723840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 78975915795948841450271145984 }, some { target := 561, numerator := 288460978870554149489580441600 }, some { target := 563, numerator := 78975889187673436628849786880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 43763724039793307045691654144 }, some { target := 592, numerator := 159847803577950388570659225600 }, some { target := 594, numerator := 43763709295080184628725678080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 76963790552739953770009460736 }, some { target := 606, numerator := 281111654568119648865642086400 }, some { target := 608, numerator := 76963764622382393657414123520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 2515156554011109600327106560 }, some { target := 661, numerator := 9186655378043125779922944000 }, some { target := 663, numerator := 2515155706613803714294579200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 78975915795948841450271145984 }, some { target := 687, numerator := 288460978870554149489580441600 }, some { target := 689, numerator := 78975889187673436628849786880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 2515156554011109600327106560 }, some { target := 701, numerator := 9186655378043125779922944000 }, some { target := 703, numerator := 2515155706613803714294579200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 76963790552739953770009460736 }, some { target := 732, numerator := 281111654568119648865642086400 }, some { target := 734, numerator := 76963764622382393657414123520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 80485009728355507210467409920 }, some { target := 746, numerator := 293972972097380024957534208000 }, some { target := 748, numerator := 80484982611641718857426534400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 3018187864813331520392527872 }, some { target := 766, numerator := 11023986453651750935907532800 }, some { target := 768, numerator := 3018186847936564457153495040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1
