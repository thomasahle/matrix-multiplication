import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 66, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 57971770943707764643332096 }, some { target := 57, numerator := 869576564155616469649981440 }, some { target := 58, numerator := 1526589968184304468941078528 }, some { target := 59, numerator := 57971770943707764643332096 }, some { target := 60, numerator := 966196182395129410722201600 }, some { target := 61, numerator := 57971770943707764643332096 }, some { target := 62, numerator := 1526589968184304468941078528 }, some { target := 63, numerator := 1516928006360353174833856512 }, some { target := 64, numerator := 966196182395129410722201600 }, some { target := 65, numerator := 23410933499433985621798944768 }, some { target := 66, numerator := 1497604082712450586619412480 }, some { target := 67, numerator := 869576564155616469649981440 }, some { target := 68, numerator := 1526589968184304468941078528 }, some { target := 69, numerator := 57971770943707764643332096 }, some { target := 70, numerator := 1497604082712450586619412480 }, some { target := 71, numerator := 57971770943707764643332096 }, some { target := 72, numerator := 1526589968184304468941078528 }, some { target := 73, numerator := 1526589968184304468941078528 }, some { target := 74, numerator := 57971770943707764643332096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 65451999452573282661826560 }, some { target := 92, numerator := 981779991788599239927398400 }, some { target := 93, numerator := 1723569318917763110094766080 }, some { target := 94, numerator := 65451999452573282661826560 }, some { target := 95, numerator := 1090866657542888044363776000 }, some { target := 96, numerator := 65451999452573282661826560 }, some { target := 97, numerator := 1723569318917763110094766080 }, some { target := 98, numerator := 1712660652342334229651128320 }, some { target := 99, numerator := 1090866657542888044363776000 }, some { target := 100, numerator := 26431699112264177314934292480 }, some { target := 101, numerator := 1690843319191476468763852800 }, some { target := 102, numerator := 981779991788599239927398400 }, some { target := 103, numerator := 1723569318917763110094766080 }, some { target := 104, numerator := 65451999452573282661826560 }, some { target := 105, numerator := 1690843319191476468763852800 }, some { target := 106, numerator := 65451999452573282661826560 }, some { target := 107, numerator := 1723569318917763110094766080 }, some { target := 108, numerator := 1723569318917763110094766080 }, some { target := 109, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 56101713816491385138708480 }, some { target := 153, numerator := 841525707247370777080627200 }, some { target := 154, numerator := 1477345130500939808652656640 }, some { target := 155, numerator := 56101713816491385138708480 }, some { target := 156, numerator := 935028563608189752311808000 }, some { target := 157, numerator := 56101713816491385138708480 }, some { target := 158, numerator := 1477345130500939808652656640 }, some { target := 159, numerator := 1467994844864857911129538560 }, some { target := 160, numerator := 935028563608189752311808000 }, some { target := 161, numerator := 22655742096226437698515107840 }, some { target := 162, numerator := 1449294273592694116083302400 }, some { target := 163, numerator := 841525707247370777080627200 }, some { target := 164, numerator := 1477345130500939808652656640 }, some { target := 165, numerator := 56101713816491385138708480 }, some { target := 166, numerator := 1449294273592694116083302400 }, some { target := 167, numerator := 56101713816491385138708480 }, some { target := 168, numerator := 1477345130500939808652656640 }, some { target := 169, numerator := 1477345130500939808652656640 }, some { target := 170, numerator := 56101713816491385138708480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 738672565250469904326328320 }, some { target := 188, numerator := 11080088478757048564894924800 }, some { target := 189, numerator := 19451710884929040813926645760 }, some { target := 190, numerator := 738672565250469904326328320 }, some { target := 191, numerator := 12311209420841165072105472000 }, some { target := 192, numerator := 738672565250469904326328320 }, some { target := 193, numerator := 19451710884929040813926645760 }, some { target := 194, numerator := 19328598790720629163205591040 }, some { target := 195, numerator := 12311209420841165072105472000 }, some { target := 196, numerator := 298300604266981429697115586560 }, some { target := 197, numerator := 19082374602303805861763481600 }, some { target := 198, numerator := 11080088478757048564894924800 }, some { target := 199, numerator := 19451710884929040813926645760 }, some { target := 200, numerator := 738672565250469904326328320 }, some { target := 201, numerator := 19082374602303805861763481600 }, some { target := 202, numerator := 738672565250469904326328320 }, some { target := 203, numerator := 19451710884929040813926645760 }, some { target := 204, numerator := 19451710884929040813926645760 }, some { target := 205, numerator := 738672565250469904326328320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 65451999452573282661826560 }, some { target := 223, numerator := 981779991788599239927398400 }, some { target := 224, numerator := 1723569318917763110094766080 }, some { target := 225, numerator := 65451999452573282661826560 }, some { target := 226, numerator := 1090866657542888044363776000 }, some { target := 227, numerator := 65451999452573282661826560 }, some { target := 228, numerator := 1723569318917763110094766080 }, some { target := 229, numerator := 1712660652342334229651128320 }, some { target := 230, numerator := 1090866657542888044363776000 }, some { target := 231, numerator := 26431699112264177314934292480 }, some { target := 232, numerator := 1690843319191476468763852800 }, some { target := 233, numerator := 981779991788599239927398400 }, some { target := 234, numerator := 1723569318917763110094766080 }, some { target := 235, numerator := 65451999452573282661826560 }, some { target := 236, numerator := 1690843319191476468763852800 }, some { target := 237, numerator := 65451999452573282661826560 }, some { target := 238, numerator := 1723569318917763110094766080 }, some { target := 239, numerator := 1723569318917763110094766080 }, some { target := 240, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 56101713816491385138708480 }, some { target := 284, numerator := 841525707247370777080627200 }, some { target := 285, numerator := 1477345130500939808652656640 }, some { target := 286, numerator := 56101713816491385138708480 }, some { target := 287, numerator := 935028563608189752311808000 }, some { target := 288, numerator := 56101713816491385138708480 }, some { target := 289, numerator := 1477345130500939808652656640 }, some { target := 290, numerator := 1467994844864857911129538560 }, some { target := 291, numerator := 935028563608189752311808000 }, some { target := 292, numerator := 22655742096226437698515107840 }, some { target := 293, numerator := 1449294273592694116083302400 }, some { target := 294, numerator := 841525707247370777080627200 }, some { target := 295, numerator := 1477345130500939808652656640 }, some { target := 296, numerator := 56101713816491385138708480 }, some { target := 297, numerator := 1449294273592694116083302400 }, some { target := 298, numerator := 56101713816491385138708480 }, some { target := 299, numerator := 1477345130500939808652656640 }, some { target := 300, numerator := 1477345130500939808652656640 }, some { target := 301, numerator := 56101713816491385138708480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 65451999452573282661826560 }, some { target := 319, numerator := 981779991788599239927398400 }, some { target := 320, numerator := 1723569318917763110094766080 }, some { target := 321, numerator := 65451999452573282661826560 }, some { target := 322, numerator := 1090866657542888044363776000 }, some { target := 323, numerator := 65451999452573282661826560 }, some { target := 324, numerator := 1723569318917763110094766080 }, some { target := 325, numerator := 1712660652342334229651128320 }, some { target := 326, numerator := 1090866657542888044363776000 }, some { target := 327, numerator := 26431699112264177314934292480 }, some { target := 328, numerator := 1690843319191476468763852800 }, some { target := 329, numerator := 981779991788599239927398400 }, some { target := 330, numerator := 1723569318917763110094766080 }, some { target := 331, numerator := 65451999452573282661826560 }, some { target := 332, numerator := 1690843319191476468763852800 }, some { target := 333, numerator := 65451999452573282661826560 }, some { target := 334, numerator := 1723569318917763110094766080 }, some { target := 335, numerator := 1723569318917763110094766080 }, some { target := 336, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 65451999452573282661826560 }, some { target := 420, numerator := 981779991788599239927398400 }, some { target := 421, numerator := 1723569318917763110094766080 }, some { target := 422, numerator := 65451999452573282661826560 }, some { target := 423, numerator := 1090866657542888044363776000 }, some { target := 424, numerator := 65451999452573282661826560 }, some { target := 425, numerator := 1723569318917763110094766080 }, some { target := 426, numerator := 1712660652342334229651128320 }, some { target := 427, numerator := 1090866657542888044363776000 }, some { target := 428, numerator := 26431699112264177314934292480 }, some { target := 429, numerator := 1690843319191476468763852800 }, some { target := 430, numerator := 981779991788599239927398400 }, some { target := 431, numerator := 1723569318917763110094766080 }, some { target := 432, numerator := 65451999452573282661826560 }, some { target := 433, numerator := 1690843319191476468763852800 }, some { target := 434, numerator := 65451999452573282661826560 }, some { target := 435, numerator := 1723569318917763110094766080 }, some { target := 436, numerator := 1723569318917763110094766080 }, some { target := 437, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 2713452891590966661208866816 }, some { target := 455, numerator := 40701793373864499918133002240 }, some { target := 456, numerator := 71454259478562122078500159488 }, some { target := 457, numerator := 2713452891590966661208866816 }, some { target := 458, numerator := 45224214859849444353481113600 }, some { target := 459, numerator := 2713452891590966661208866816 }, some { target := 460, numerator := 71454259478562122078500159488 }, some { target := 461, numerator := 71002017329963627634965348352 }, some { target := 462, numerator := 45224214859849444353481113600 }, some { target := 463, numerator := 1095782726054152036684847382528 }, some { target := 464, numerator := 70097533032766638747895726080 }, some { target := 465, numerator := 40701793373864499918133002240 }, some { target := 466, numerator := 71454259478562122078500159488 }, some { target := 467, numerator := 2713452891590966661208866816 }, some { target := 468, numerator := 70097533032766638747895726080 }, some { target := 469, numerator := 2713452891590966661208866816 }, some { target := 470, numerator := 71454259478562122078500159488 }, some { target := 471, numerator := 71454259478562122078500159488 }, some { target := 472, numerator := 2713452891590966661208866816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 67322056579789662166450176 }, some { target := 490, numerator := 1009830848696844932496752640 }, some { target := 491, numerator := 1772814156601127770383187968 }, some { target := 492, numerator := 67322056579789662166450176 }, some { target := 493, numerator := 1122034276329827702774169600 }, some { target := 494, numerator := 67322056579789662166450176 }, some { target := 495, numerator := 1772814156601127770383187968 }, some { target := 496, numerator := 1761593813837829493355446272 }, some { target := 497, numerator := 1122034276329827702774169600 }, some { target := 498, numerator := 27186890515471725238218129408 }, some { target := 499, numerator := 1739153128311232939299962880 }, some { target := 500, numerator := 1009830848696844932496752640 }, some { target := 501, numerator := 1772814156601127770383187968 }, some { target := 502, numerator := 67322056579789662166450176 }, some { target := 503, numerator := 1739153128311232939299962880 }, some { target := 504, numerator := 67322056579789662166450176 }, some { target := 505, numerator := 1772814156601127770383187968 }, some { target := 506, numerator := 1772814156601127770383187968 }, some { target := 507, numerator := 67322056579789662166450176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 738672565250469904326328320 }, some { target := 551, numerator := 11080088478757048564894924800 }, some { target := 552, numerator := 19451710884929040813926645760 }, some { target := 553, numerator := 738672565250469904326328320 }, some { target := 554, numerator := 12311209420841165072105472000 }, some { target := 555, numerator := 738672565250469904326328320 }, some { target := 556, numerator := 19451710884929040813926645760 }, some { target := 557, numerator := 19328598790720629163205591040 }, some { target := 558, numerator := 12311209420841165072105472000 }, some { target := 559, numerator := 298300604266981429697115586560 }, some { target := 560, numerator := 19082374602303805861763481600 }, some { target := 561, numerator := 11080088478757048564894924800 }, some { target := 562, numerator := 19451710884929040813926645760 }, some { target := 563, numerator := 738672565250469904326328320 }, some { target := 564, numerator := 19082374602303805861763481600 }, some { target := 565, numerator := 738672565250469904326328320 }, some { target := 566, numerator := 19451710884929040813926645760 }, some { target := 567, numerator := 19451710884929040813926645760 }, some { target := 568, numerator := 738672565250469904326328320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 2713452891590966661208866816 }, some { target := 586, numerator := 40701793373864499918133002240 }, some { target := 587, numerator := 71454259478562122078500159488 }, some { target := 588, numerator := 2713452891590966661208866816 }, some { target := 589, numerator := 45224214859849444353481113600 }, some { target := 590, numerator := 2713452891590966661208866816 }, some { target := 591, numerator := 71454259478562122078500159488 }, some { target := 592, numerator := 71002017329963627634965348352 }, some { target := 593, numerator := 45224214859849444353481113600 }, some { target := 594, numerator := 1095782726054152036684847382528 }, some { target := 595, numerator := 70097533032766638747895726080 }, some { target := 596, numerator := 40701793373864499918133002240 }, some { target := 597, numerator := 71454259478562122078500159488 }, some { target := 598, numerator := 2713452891590966661208866816 }, some { target := 599, numerator := 70097533032766638747895726080 }, some { target := 600, numerator := 2713452891590966661208866816 }, some { target := 601, numerator := 71454259478562122078500159488 }, some { target := 602, numerator := 71454259478562122078500159488 }, some { target := 603, numerator := 2713452891590966661208866816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 57971770943707764643332096 }, some { target := 661, numerator := 869576564155616469649981440 }, some { target := 662, numerator := 1526589968184304468941078528 }, some { target := 663, numerator := 57971770943707764643332096 }, some { target := 664, numerator := 966196182395129410722201600 }, some { target := 665, numerator := 57971770943707764643332096 }, some { target := 666, numerator := 1526589968184304468941078528 }, some { target := 667, numerator := 1516928006360353174833856512 }, some { target := 668, numerator := 966196182395129410722201600 }, some { target := 669, numerator := 23410933499433985621798944768 }, some { target := 670, numerator := 1497604082712450586619412480 }, some { target := 671, numerator := 869576564155616469649981440 }, some { target := 672, numerator := 1526589968184304468941078528 }, some { target := 673, numerator := 57971770943707764643332096 }, some { target := 674, numerator := 1497604082712450586619412480 }, some { target := 675, numerator := 57971770943707764643332096 }, some { target := 676, numerator := 1526589968184304468941078528 }, some { target := 677, numerator := 1526589968184304468941078528 }, some { target := 678, numerator := 57971770943707764643332096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 65451999452573282661826560 }, some { target := 767, numerator := 981779991788599239927398400 }, some { target := 768, numerator := 1723569318917763110094766080 }, some { target := 769, numerator := 65451999452573282661826560 }, some { target := 770, numerator := 1090866657542888044363776000 }, some { target := 771, numerator := 65451999452573282661826560 }, some { target := 772, numerator := 1723569318917763110094766080 }, some { target := 773, numerator := 1712660652342334229651128320 }, some { target := 774, numerator := 1090866657542888044363776000 }, some { target := 775, numerator := 26431699112264177314934292480 }, some { target := 776, numerator := 1690843319191476468763852800 }, some { target := 777, numerator := 981779991788599239927398400 }, some { target := 778, numerator := 1723569318917763110094766080 }, some { target := 779, numerator := 65451999452573282661826560 }, some { target := 780, numerator := 1690843319191476468763852800 }, some { target := 781, numerator := 65451999452573282661826560 }, some { target := 782, numerator := 1723569318917763110094766080 }, some { target := 783, numerator := 1723569318917763110094766080 }, some { target := 784, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 67322056579789662166450176 }, some { target := 802, numerator := 1009830848696844932496752640 }, some { target := 803, numerator := 1772814156601127770383187968 }, some { target := 804, numerator := 67322056579789662166450176 }, some { target := 805, numerator := 1122034276329827702774169600 }, some { target := 806, numerator := 67322056579789662166450176 }, some { target := 807, numerator := 1772814156601127770383187968 }, some { target := 808, numerator := 1761593813837829493355446272 }, some { target := 809, numerator := 1122034276329827702774169600 }, some { target := 810, numerator := 27186890515471725238218129408 }, some { target := 811, numerator := 1739153128311232939299962880 }, some { target := 812, numerator := 1009830848696844932496752640 }, some { target := 813, numerator := 1772814156601127770383187968 }, some { target := 814, numerator := 67322056579789662166450176 }, some { target := 815, numerator := 1739153128311232939299962880 }, some { target := 816, numerator := 67322056579789662166450176 }, some { target := 817, numerator := 1772814156601127770383187968 }, some { target := 818, numerator := 1772814156601127770383187968 }, some { target := 819, numerator := 67322056579789662166450176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 65451999452573282661826560 }, some { target := 877, numerator := 981779991788599239927398400 }, some { target := 878, numerator := 1723569318917763110094766080 }, some { target := 879, numerator := 65451999452573282661826560 }, some { target := 880, numerator := 1090866657542888044363776000 }, some { target := 881, numerator := 65451999452573282661826560 }, some { target := 882, numerator := 1723569318917763110094766080 }, some { target := 883, numerator := 1712660652342334229651128320 }, some { target := 884, numerator := 1090866657542888044363776000 }, some { target := 885, numerator := 26431699112264177314934292480 }, some { target := 886, numerator := 1690843319191476468763852800 }, some { target := 887, numerator := 981779991788599239927398400 }, some { target := 888, numerator := 1723569318917763110094766080 }, some { target := 889, numerator := 65451999452573282661826560 }, some { target := 890, numerator := 1690843319191476468763852800 }, some { target := 891, numerator := 65451999452573282661826560 }, some { target := 892, numerator := 1723569318917763110094766080 }, some { target := 893, numerator := 1723569318917763110094766080 }, some { target := 894, numerator := 65451999452573282661826560 }]

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
def data : BetaFourLocalSlotData := ⟨1, 942, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 1366385986484274950333005824 }, some { target := 112, numerator := 53296410389523141851080556544 }, some { target := 115, numerator := 53296390840586109737383231488 }, some { target := 122, numerator := 1366392502796618988232114176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 19812596804021986779828584448 }, some { target := 208, numerator := 772797950648085556840668069888 }, some { target := 211, numerator := 772797667188498591192056856576 }, some { target := 218, numerator := 19812691290550975329365655552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 35070573653096390391880482816 }, some { target := 243, numerator := 1367941199997760640844400951296 }, some { target := 246, numerator := 1367940698241710149926169608192 }, some { target := 253, numerator := 35070740905113220697957597184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 1138654988736895791944171520 }, some { target := 304, numerator := 44413675324602618209233797120 }, some { target := 307, numerator := 44413659033821758114486026240 }, some { target := 314, numerator := 1138660418997182490193428480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 21862175783748399205328093184 }, some { target := 339, numerator := 852742566232370269617288904704 }, some { target := 342, numerator := 852742253449377755798131703808 }, some { target := 349, numerator := 21862280044745903811713826816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 1138654988736895791944171520 }, some { target := 365, numerator := 44413675324602618209233797120 }, some { target := 368, numerator := 44413659033821758114486026240 }, some { target := 375, numerator := 1138660418997182490193428480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 34842842655349011233491648512 }, some { target := 475, numerator := 1359058464932840117202554191872 }, some { target := 478, numerator := 1359057966434945798303272402944 }, some { target := 485, numerator := 34843008821313784199918911488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 36436959639580665342213488640 }, some { target := 510, numerator := 1421237610387283782695481507840 }, some { target := 513, numerator := 1421237089082296259663552839680 }, some { target := 520, numerator := 36437133407909839686189711360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 21862175783748399205328093184 }, some { target := 571, numerator := 852742566232370269617288904704 }, some { target := 574, numerator := 852742253449377755798131703808 }, some { target := 581, numerator := 21862280044745903811713826816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 558168675478826317211032879104 }, some { target := 606, numerator := 21771583644120203446166407348224 }, some { target := 609, numerator := 21771575658379425827721050062848 }, some { target := 616, numerator := 558171337392418856692818640896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 35753766646338527867046985728 }, some { target := 632, numerator := 1394589405192522211769941229568 }, some { target := 635, numerator := 1394588893662003204794861223936 }, some { target := 642, numerator := 35753937156511530192073654272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 19812596804021986779828584448 }, some { target := 681, numerator := 772797950648085556840668069888 }, some { target := 684, numerator := 772797667188498591192056856576 }, some { target := 691, numerator := 19812691290550975329365655552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 34842842655349011233491648512 }, some { target := 707, numerator := 1359058464932840117202554191872 }, some { target := 710, numerator := 1359057966434945798303272402944 }, some { target := 717, numerator := 34843008821313784199918911488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 1138654988736895791944171520 }, some { target := 787, numerator := 44413675324602618209233797120 }, some { target := 790, numerator := 44413659033821758114486026240 }, some { target := 797, numerator := 1138660418997182490193428480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 35753766646338527867046985728 }, some { target := 822, numerator := 1394589405192522211769941229568 }, some { target := 825, numerator := 1394588893662003204794861223936 }, some { target := 832, numerator := 35753937156511530192073654272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 1138654988736895791944171520 }, some { target := 848, numerator := 44413675324602618209233797120 }, some { target := 851, numerator := 44413659033821758114486026240 }, some { target := 858, numerator := 1138660418997182490193428480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 34842842655349011233491648512 }, some { target := 897, numerator := 1359058464932840117202554191872 }, some { target := 900, numerator := 1359057966434945798303272402944 }, some { target := 907, numerator := 34843008821313784199918911488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 36436959639580665342213488640 }, some { target := 923, numerator := 1421237610387283782695481507840 }, some { target := 926, numerator := 1421237089082296259663552839680 }, some { target := 933, numerator := 36437133407909839686189711360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 1366385986484274950333005824 }, some { target := 968, numerator := 53296410389523141851080556544 }, some { target := 971, numerator := 53296390840586109737383231488 }, some { target := 978, numerator := 1366392502796618988232114176 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3
