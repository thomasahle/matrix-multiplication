import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3

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
    Slot0.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 57971770943707764643332096 }, { target := 57, numerator := 869576564155616469649981440 }, { target := 58, numerator := 1526589968184304468941078528 }, { target := 59, numerator := 57971770943707764643332096 }, { target := 60, numerator := 966196182395129410722201600 }, { target := 61, numerator := 57971770943707764643332096 }, { target := 62, numerator := 1526589968184304468941078528 }, { target := 63, numerator := 1516928006360353174833856512 }, { target := 64, numerator := 966196182395129410722201600 }, { target := 65, numerator := 23410933499433985621798944768 }, { target := 66, numerator := 1497604082712450586619412480 }, { target := 67, numerator := 869576564155616469649981440 }, { target := 68, numerator := 1526589968184304468941078528 }, { target := 69, numerator := 57971770943707764643332096 }, { target := 70, numerator := 1497604082712450586619412480 }, { target := 71, numerator := 57971770943707764643332096 }, { target := 72, numerator := 1526589968184304468941078528 }, { target := 73, numerator := 1526589968184304468941078528 }, { target := 74, numerator := 57971770943707764643332096 }, { target := 91, numerator := 65451999452573282661826560 }, { target := 92, numerator := 981779991788599239927398400 }, { target := 93, numerator := 1723569318917763110094766080 }, { target := 94, numerator := 65451999452573282661826560 }, { target := 95, numerator := 1090866657542888044363776000 }, { target := 96, numerator := 65451999452573282661826560 }, { target := 97, numerator := 1723569318917763110094766080 }, { target := 98, numerator := 1712660652342334229651128320 }, { target := 99, numerator := 1090866657542888044363776000 }, { target := 100, numerator := 26431699112264177314934292480 }, { target := 101, numerator := 1690843319191476468763852800 }, { target := 102, numerator := 981779991788599239927398400 }, { target := 103, numerator := 1723569318917763110094766080 }, { target := 104, numerator := 65451999452573282661826560 }, { target := 105, numerator := 1690843319191476468763852800 }, { target := 106, numerator := 65451999452573282661826560 }, { target := 107, numerator := 1723569318917763110094766080 }, { target := 108, numerator := 1723569318917763110094766080 }, { target := 109, numerator := 65451999452573282661826560 }, { target := 152, numerator := 56101713816491385138708480 }, { target := 153, numerator := 841525707247370777080627200 }, { target := 154, numerator := 1477345130500939808652656640 }, { target := 155, numerator := 56101713816491385138708480 }, { target := 156, numerator := 935028563608189752311808000 }, { target := 157, numerator := 56101713816491385138708480 }, { target := 158, numerator := 1477345130500939808652656640 }, { target := 159, numerator := 1467994844864857911129538560 }, { target := 160, numerator := 935028563608189752311808000 }, { target := 161, numerator := 22655742096226437698515107840 }, { target := 162, numerator := 1449294273592694116083302400 }, { target := 163, numerator := 841525707247370777080627200 }, { target := 164, numerator := 1477345130500939808652656640 }, { target := 165, numerator := 56101713816491385138708480 }, { target := 166, numerator := 1449294273592694116083302400 }, { target := 167, numerator := 56101713816491385138708480 }, { target := 168, numerator := 1477345130500939808652656640 }, { target := 169, numerator := 1477345130500939808652656640 }, { target := 170, numerator := 56101713816491385138708480 }]

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 187, numerator := 738672565250469904326328320 }, { target := 188, numerator := 11080088478757048564894924800 }, { target := 189, numerator := 19451710884929040813926645760 }, { target := 190, numerator := 738672565250469904326328320 }, { target := 191, numerator := 12311209420841165072105472000 }, { target := 192, numerator := 738672565250469904326328320 }, { target := 193, numerator := 19451710884929040813926645760 }, { target := 194, numerator := 19328598790720629163205591040 }, { target := 195, numerator := 12311209420841165072105472000 }, { target := 196, numerator := 298300604266981429697115586560 }, { target := 197, numerator := 19082374602303805861763481600 }, { target := 198, numerator := 11080088478757048564894924800 }, { target := 199, numerator := 19451710884929040813926645760 }, { target := 200, numerator := 738672565250469904326328320 }, { target := 201, numerator := 19082374602303805861763481600 }, { target := 202, numerator := 738672565250469904326328320 }, { target := 203, numerator := 19451710884929040813926645760 }, { target := 204, numerator := 19451710884929040813926645760 }, { target := 205, numerator := 738672565250469904326328320 }, { target := 222, numerator := 65451999452573282661826560 }, { target := 223, numerator := 981779991788599239927398400 }, { target := 224, numerator := 1723569318917763110094766080 }, { target := 225, numerator := 65451999452573282661826560 }, { target := 226, numerator := 1090866657542888044363776000 }, { target := 227, numerator := 65451999452573282661826560 }, { target := 228, numerator := 1723569318917763110094766080 }, { target := 229, numerator := 1712660652342334229651128320 }, { target := 230, numerator := 1090866657542888044363776000 }, { target := 231, numerator := 26431699112264177314934292480 }, { target := 232, numerator := 1690843319191476468763852800 }, { target := 233, numerator := 981779991788599239927398400 }, { target := 234, numerator := 1723569318917763110094766080 }, { target := 235, numerator := 65451999452573282661826560 }, { target := 236, numerator := 1690843319191476468763852800 }, { target := 237, numerator := 65451999452573282661826560 }, { target := 238, numerator := 1723569318917763110094766080 }, { target := 239, numerator := 1723569318917763110094766080 }, { target := 240, numerator := 65451999452573282661826560 }, { target := 283, numerator := 56101713816491385138708480 }, { target := 284, numerator := 841525707247370777080627200 }, { target := 285, numerator := 1477345130500939808652656640 }, { target := 286, numerator := 56101713816491385138708480 }, { target := 287, numerator := 935028563608189752311808000 }, { target := 288, numerator := 56101713816491385138708480 }, { target := 289, numerator := 1477345130500939808652656640 }, { target := 290, numerator := 1467994844864857911129538560 }, { target := 291, numerator := 935028563608189752311808000 }, { target := 292, numerator := 22655742096226437698515107840 }, { target := 293, numerator := 1449294273592694116083302400 }, { target := 294, numerator := 841525707247370777080627200 }, { target := 295, numerator := 1477345130500939808652656640 }, { target := 296, numerator := 56101713816491385138708480 }, { target := 297, numerator := 1449294273592694116083302400 }, { target := 298, numerator := 56101713816491385138708480 }, { target := 299, numerator := 1477345130500939808652656640 }, { target := 300, numerator := 1477345130500939808652656640 }, { target := 301, numerator := 56101713816491385138708480 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 318, numerator := 65451999452573282661826560 }, { target := 319, numerator := 981779991788599239927398400 }, { target := 320, numerator := 1723569318917763110094766080 }, { target := 321, numerator := 65451999452573282661826560 }, { target := 322, numerator := 1090866657542888044363776000 }, { target := 323, numerator := 65451999452573282661826560 }, { target := 324, numerator := 1723569318917763110094766080 }, { target := 325, numerator := 1712660652342334229651128320 }, { target := 326, numerator := 1090866657542888044363776000 }, { target := 327, numerator := 26431699112264177314934292480 }, { target := 328, numerator := 1690843319191476468763852800 }, { target := 329, numerator := 981779991788599239927398400 }, { target := 330, numerator := 1723569318917763110094766080 }, { target := 331, numerator := 65451999452573282661826560 }, { target := 332, numerator := 1690843319191476468763852800 }, { target := 333, numerator := 65451999452573282661826560 }, { target := 334, numerator := 1723569318917763110094766080 }, { target := 335, numerator := 1723569318917763110094766080 }, { target := 336, numerator := 65451999452573282661826560 }, { target := 419, numerator := 65451999452573282661826560 }, { target := 420, numerator := 981779991788599239927398400 }, { target := 421, numerator := 1723569318917763110094766080 }, { target := 422, numerator := 65451999452573282661826560 }, { target := 423, numerator := 1090866657542888044363776000 }, { target := 424, numerator := 65451999452573282661826560 }, { target := 425, numerator := 1723569318917763110094766080 }, { target := 426, numerator := 1712660652342334229651128320 }, { target := 427, numerator := 1090866657542888044363776000 }, { target := 428, numerator := 26431699112264177314934292480 }, { target := 429, numerator := 1690843319191476468763852800 }, { target := 430, numerator := 981779991788599239927398400 }, { target := 431, numerator := 1723569318917763110094766080 }, { target := 432, numerator := 65451999452573282661826560 }, { target := 433, numerator := 1690843319191476468763852800 }, { target := 434, numerator := 65451999452573282661826560 }, { target := 435, numerator := 1723569318917763110094766080 }, { target := 436, numerator := 1723569318917763110094766080 }, { target := 437, numerator := 65451999452573282661826560 }, { target := 454, numerator := 2713452891590966661208866816 }, { target := 455, numerator := 40701793373864499918133002240 }, { target := 456, numerator := 71454259478562122078500159488 }, { target := 457, numerator := 2713452891590966661208866816 }, { target := 458, numerator := 45224214859849444353481113600 }, { target := 459, numerator := 2713452891590966661208866816 }, { target := 460, numerator := 71454259478562122078500159488 }, { target := 461, numerator := 71002017329963627634965348352 }, { target := 462, numerator := 45224214859849444353481113600 }, { target := 463, numerator := 1095782726054152036684847382528 }, { target := 464, numerator := 70097533032766638747895726080 }, { target := 465, numerator := 40701793373864499918133002240 }, { target := 466, numerator := 71454259478562122078500159488 }, { target := 467, numerator := 2713452891590966661208866816 }, { target := 468, numerator := 70097533032766638747895726080 }, { target := 469, numerator := 2713452891590966661208866816 }, { target := 470, numerator := 71454259478562122078500159488 }, { target := 471, numerator := 71454259478562122078500159488 }, { target := 472, numerator := 2713452891590966661208866816 }]

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
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 489, numerator := 67322056579789662166450176 }, { target := 490, numerator := 1009830848696844932496752640 }, { target := 491, numerator := 1772814156601127770383187968 }, { target := 492, numerator := 67322056579789662166450176 }, { target := 493, numerator := 1122034276329827702774169600 }, { target := 494, numerator := 67322056579789662166450176 }, { target := 495, numerator := 1772814156601127770383187968 }, { target := 496, numerator := 1761593813837829493355446272 }, { target := 497, numerator := 1122034276329827702774169600 }, { target := 498, numerator := 27186890515471725238218129408 }, { target := 499, numerator := 1739153128311232939299962880 }, { target := 500, numerator := 1009830848696844932496752640 }, { target := 501, numerator := 1772814156601127770383187968 }, { target := 502, numerator := 67322056579789662166450176 }, { target := 503, numerator := 1739153128311232939299962880 }, { target := 504, numerator := 67322056579789662166450176 }, { target := 505, numerator := 1772814156601127770383187968 }, { target := 506, numerator := 1772814156601127770383187968 }, { target := 507, numerator := 67322056579789662166450176 }, { target := 550, numerator := 738672565250469904326328320 }, { target := 551, numerator := 11080088478757048564894924800 }, { target := 552, numerator := 19451710884929040813926645760 }, { target := 553, numerator := 738672565250469904326328320 }, { target := 554, numerator := 12311209420841165072105472000 }, { target := 555, numerator := 738672565250469904326328320 }, { target := 556, numerator := 19451710884929040813926645760 }, { target := 557, numerator := 19328598790720629163205591040 }, { target := 558, numerator := 12311209420841165072105472000 }, { target := 559, numerator := 298300604266981429697115586560 }, { target := 560, numerator := 19082374602303805861763481600 }, { target := 561, numerator := 11080088478757048564894924800 }, { target := 562, numerator := 19451710884929040813926645760 }, { target := 563, numerator := 738672565250469904326328320 }, { target := 564, numerator := 19082374602303805861763481600 }, { target := 565, numerator := 738672565250469904326328320 }, { target := 566, numerator := 19451710884929040813926645760 }, { target := 567, numerator := 19451710884929040813926645760 }, { target := 568, numerator := 738672565250469904326328320 }, { target := 585, numerator := 2713452891590966661208866816 }, { target := 586, numerator := 40701793373864499918133002240 }, { target := 587, numerator := 71454259478562122078500159488 }, { target := 588, numerator := 2713452891590966661208866816 }, { target := 589, numerator := 45224214859849444353481113600 }, { target := 590, numerator := 2713452891590966661208866816 }, { target := 591, numerator := 71454259478562122078500159488 }, { target := 592, numerator := 71002017329963627634965348352 }, { target := 593, numerator := 45224214859849444353481113600 }, { target := 594, numerator := 1095782726054152036684847382528 }, { target := 595, numerator := 70097533032766638747895726080 }, { target := 596, numerator := 40701793373864499918133002240 }, { target := 597, numerator := 71454259478562122078500159488 }, { target := 598, numerator := 2713452891590966661208866816 }, { target := 599, numerator := 70097533032766638747895726080 }, { target := 600, numerator := 2713452891590966661208866816 }, { target := 601, numerator := 71454259478562122078500159488 }, { target := 602, numerator := 71454259478562122078500159488 }, { target := 603, numerator := 2713452891590966661208866816 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 57971770943707764643332096 }, { target := 661, numerator := 869576564155616469649981440 }, { target := 662, numerator := 1526589968184304468941078528 }, { target := 663, numerator := 57971770943707764643332096 }, { target := 664, numerator := 966196182395129410722201600 }, { target := 665, numerator := 57971770943707764643332096 }, { target := 666, numerator := 1526589968184304468941078528 }, { target := 667, numerator := 1516928006360353174833856512 }, { target := 668, numerator := 966196182395129410722201600 }, { target := 669, numerator := 23410933499433985621798944768 }, { target := 670, numerator := 1497604082712450586619412480 }, { target := 671, numerator := 869576564155616469649981440 }, { target := 672, numerator := 1526589968184304468941078528 }, { target := 673, numerator := 57971770943707764643332096 }, { target := 674, numerator := 1497604082712450586619412480 }, { target := 675, numerator := 57971770943707764643332096 }, { target := 676, numerator := 1526589968184304468941078528 }, { target := 677, numerator := 1526589968184304468941078528 }, { target := 678, numerator := 57971770943707764643332096 }, { target := 766, numerator := 65451999452573282661826560 }, { target := 767, numerator := 981779991788599239927398400 }, { target := 768, numerator := 1723569318917763110094766080 }, { target := 769, numerator := 65451999452573282661826560 }, { target := 770, numerator := 1090866657542888044363776000 }, { target := 771, numerator := 65451999452573282661826560 }, { target := 772, numerator := 1723569318917763110094766080 }, { target := 773, numerator := 1712660652342334229651128320 }, { target := 774, numerator := 1090866657542888044363776000 }, { target := 775, numerator := 26431699112264177314934292480 }, { target := 776, numerator := 1690843319191476468763852800 }, { target := 777, numerator := 981779991788599239927398400 }, { target := 778, numerator := 1723569318917763110094766080 }, { target := 779, numerator := 65451999452573282661826560 }, { target := 780, numerator := 1690843319191476468763852800 }, { target := 781, numerator := 65451999452573282661826560 }, { target := 782, numerator := 1723569318917763110094766080 }, { target := 783, numerator := 1723569318917763110094766080 }, { target := 784, numerator := 65451999452573282661826560 }, { target := 801, numerator := 67322056579789662166450176 }, { target := 802, numerator := 1009830848696844932496752640 }, { target := 803, numerator := 1772814156601127770383187968 }, { target := 804, numerator := 67322056579789662166450176 }, { target := 805, numerator := 1122034276329827702774169600 }, { target := 806, numerator := 67322056579789662166450176 }, { target := 807, numerator := 1772814156601127770383187968 }, { target := 808, numerator := 1761593813837829493355446272 }, { target := 809, numerator := 1122034276329827702774169600 }, { target := 810, numerator := 27186890515471725238218129408 }, { target := 811, numerator := 1739153128311232939299962880 }, { target := 812, numerator := 1009830848696844932496752640 }, { target := 813, numerator := 1772814156601127770383187968 }, { target := 814, numerator := 67322056579789662166450176 }, { target := 815, numerator := 1739153128311232939299962880 }, { target := 816, numerator := 67322056579789662166450176 }, { target := 817, numerator := 1772814156601127770383187968 }, { target := 818, numerator := 1772814156601127770383187968 }, { target := 819, numerator := 67322056579789662166450176 }]

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
    Slot0.Left15.expected,
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
    Slot1.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 1366385986484274950333005824 }, { target := 112, numerator := 53296410389523141851080556544 }, { target := 115, numerator := 53296390840586109737383231488 }, { target := 122, numerator := 1366392502796618988232114176 }, { target := 206, numerator := 19812596804021986779828584448 }, { target := 208, numerator := 772797950648085556840668069888 }, { target := 211, numerator := 772797667188498591192056856576 }, { target := 218, numerator := 19812691290550975329365655552 }, { target := 241, numerator := 35070573653096390391880482816 }, { target := 243, numerator := 1367941199997760640844400951296 }, { target := 246, numerator := 1367940698241710149926169608192 }, { target := 253, numerator := 35070740905113220697957597184 }, { target := 302, numerator := 1138654988736895791944171520 }, { target := 304, numerator := 44413675324602618209233797120 }, { target := 307, numerator := 44413659033821758114486026240 }, { target := 314, numerator := 1138660418997182490193428480 }, { target := 337, numerator := 21862175783748399205328093184 }, { target := 339, numerator := 852742566232370269617288904704 }, { target := 342, numerator := 852742253449377755798131703808 }, { target := 349, numerator := 21862280044745903811713826816 }, { target := 363, numerator := 1138654988736895791944171520 }, { target := 365, numerator := 44413675324602618209233797120 }, { target := 368, numerator := 44413659033821758114486026240 }, { target := 375, numerator := 1138660418997182490193428480 }, { target := 473, numerator := 34842842655349011233491648512 }, { target := 475, numerator := 1359058464932840117202554191872 }, { target := 478, numerator := 1359057966434945798303272402944 }, { target := 485, numerator := 34843008821313784199918911488 }, { target := 508, numerator := 36436959639580665342213488640 }, { target := 510, numerator := 1421237610387283782695481507840 }, { target := 513, numerator := 1421237089082296259663552839680 }, { target := 520, numerator := 36437133407909839686189711360 }, { target := 569, numerator := 21862175783748399205328093184 }, { target := 571, numerator := 852742566232370269617288904704 }, { target := 574, numerator := 852742253449377755798131703808 }, { target := 581, numerator := 21862280044745903811713826816 }, { target := 604, numerator := 558168675478826317211032879104 }, { target := 606, numerator := 21771583644120203446166407348224 }, { target := 609, numerator := 21771575658379425827721050062848 }, { target := 616, numerator := 558171337392418856692818640896 }, { target := 630, numerator := 35753766646338527867046985728 }, { target := 632, numerator := 1394589405192522211769941229568 }, { target := 635, numerator := 1394588893662003204794861223936 }, { target := 642, numerator := 35753937156511530192073654272 }, { target := 876, numerator := 65451999452573282661826560 }, { target := 877, numerator := 981779991788599239927398400 }, { target := 878, numerator := 1723569318917763110094766080 }, { target := 879, numerator := 65451999452573282661826560 }, { target := 880, numerator := 1090866657542888044363776000 }, { target := 881, numerator := 65451999452573282661826560 }, { target := 882, numerator := 1723569318917763110094766080 }, { target := 883, numerator := 1712660652342334229651128320 }, { target := 884, numerator := 1090866657542888044363776000 }, { target := 885, numerator := 26431699112264177314934292480 }, { target := 886, numerator := 1690843319191476468763852800 }, { target := 887, numerator := 981779991788599239927398400 }, { target := 888, numerator := 1723569318917763110094766080 }, { target := 889, numerator := 65451999452573282661826560 }, { target := 890, numerator := 1690843319191476468763852800 }, { target := 891, numerator := 65451999452573282661826560 }, { target := 892, numerator := 1723569318917763110094766080 }, { target := 893, numerator := 1723569318917763110094766080 }, { target := 894, numerator := 65451999452573282661826560 }]

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
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 66433598342299016753624121344 }, { target := 260, numerator := 238959677640024149441361477632 }, { target := 262, numerator := 66433620504909099811043540992 }, { target := 353, numerator := 49471828552775863539932856320 }, { target := 356, numerator := 177948696114911600647822376960 }, { target := 358, numerator := 49471845056847201986947317760 }, { target := 379, numerator := 52298790184363055742214733824 }, { target := 382, numerator := 188117193035763692113412227072 }, { target := 384, numerator := 52298807631524184957630021632 }, { target := 524, numerator := 67847079158092612854765060096 }, { target := 527, numerator := 244043926100450195174156402688 }, { target := 529, numerator := 67847101792247591296384892928 }, { target := 620, numerator := 908868164555282293033623617536 }, { target := 623, numerator := 3269171760053947406187136811008 }, { target := 625, numerator := 908868467758650025074489294848 }, { target := 646, numerator := 1643878188767952265626911768576 }, { target := 649, numerator := 5912980959475491187240497840128 }, { target := 651, numerator := 1643878737174665597451992301568 }, { target := 679, numerator := 19812596804021986779828584448 }, { target := 681, numerator := 772797950648085556840668069888 }, { target := 684, numerator := 772797667188498591192056856576 }, { target := 691, numerator := 19812691290550975329365655552 }, { target := 695, numerator := 49471828552775863539932856320 }, { target := 698, numerator := 177948696114911600647822376960 }, { target := 700, numerator := 49471845056847201986947317760 }, { target := 705, numerator := 34842842655349011233491648512 }, { target := 707, numerator := 1359058464932840117202554191872 }, { target := 710, numerator := 1359057966434945798303272402944 }, { target := 717, numerator := 34843008821313784199918911488 }, { target := 721, numerator := 908868164555282293033623617536 }, { target := 724, numerator := 3269171760053947406187136811008 }, { target := 726, numerator := 908868467758650025074489294848 }, { target := 735, numerator := 53712271000156651843355672576 }, { target := 738, numerator := 193201441496189737846207152128 }, { target := 740, numerator := 53712288918862676442971373568 }, { target := 785, numerator := 1138654988736895791944171520 }, { target := 787, numerator := 44413675324602618209233797120 }, { target := 790, numerator := 44413659033821758114486026240 }, { target := 797, numerator := 1138660418997182490193428480 }, { target := 820, numerator := 35753766646338527867046985728 }, { target := 822, numerator := 1394589405192522211769941229568 }, { target := 825, numerator := 1394588893662003204794861223936 }, { target := 832, numerator := 35753937156511530192073654272 }, { target := 836, numerator := 53712271000156651843355672576 }, { target := 839, numerator := 193201441496189737846207152128 }, { target := 841, numerator := 53712288918862676442971373568 }, { target := 846, numerator := 1138654988736895791944171520 }, { target := 848, numerator := 44413675324602618209233797120 }, { target := 851, numerator := 44413659033821758114486026240 }, { target := 858, numerator := 1138660418997182490193428480 }, { target := 895, numerator := 34842842655349011233491648512 }, { target := 897, numerator := 1359058464932840117202554191872 }, { target := 900, numerator := 1359057966434945798303272402944 }, { target := 907, numerator := 34843008821313784199918911488 }, { target := 921, numerator := 36436959639580665342213488640 }, { target := 923, numerator := 1421237610387283782695481507840 }, { target := 926, numerator := 1421237089082296259663552839680 }, { target := 933, numerator := 36437133407909839686189711360 }, { target := 966, numerator := 1366385986484274950333005824 }, { target := 968, numerator := 53296410389523141851080556544 }, { target := 971, numerator := 53296390840586109737383231488 }, { target := 978, numerator := 1366392502796618988232114176 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 7897878142385371593427648512 }, { target := 15, numerator := 5923408606789028695070736384 }, { target := 16, numerator := 6252486862721752511463555072 }, { target := 17, numerator := 8062417270351733501624057856 }, { target := 18, numerator := 107937667945933411776844529664 }, { target := 19, numerator := 188726379777417108701281517568 }, { target := 20, numerator := 5758869478822666786874327040 }, { target := 21, numerator := 107937667945933411776844529664 }, { target := 22, numerator := 6087947734755390603267145728 }, { target := 23, numerator := 6252486862721752511463555072 }, { target := 24, numerator := 6252486862721752511463555072 }, { target := 25, numerator := 6087947734755390603267145728 }, { target := 26, numerator := 188726379777417108701281517568 }, { target := 27, numerator := 6087947734755390603267145728 }, { target := 28, numerator := 7897878142385371593427648512 }, { target := 29, numerator := 8062417270351733501624057856 }, { target := 389, numerator := 8094968253134856309763473408 }, { target := 391, numerator := 8094966323144257597901635584 }, { target := 656, numerator := 198457286205886799852265799680 }, { target := 658, numerator := 198457238889988250787265904640 }, { target := 731, numerator := 146753940589089975680228130816 }, { target := 733, numerator := 146753905600228153871636103168 }, { target := 745, numerator := 163727261119856609878119284736 }, { target := 747, numerator := 163727222084240306899494371328 }, { target := 749, numerator := 19884411881021420665567182848 }, { target := 862, numerator := 52298790184363055742214733824 }, { target := 865, numerator := 188117193035763692113412227072 }, { target := 867, numerator := 52298807631524184957630021632 }, { target := 872, numerator := 8094968253134856309763473408 }, { target := 874, numerator := 8094966323144257597901635584 }, { target := 911, numerator := 52298790184363055742214733824 }, { target := 914, numerator := 188117193035763692113412227072 }, { target := 916, numerator := 52298807631524184957630021632 }, { target := 937, numerator := 1643878188767952265626911768576 }, { target := 940, numerator := 5912980959475491187240497840128 }, { target := 942, numerator := 1643878737174665597451992301568 }, { target := 947, numerator := 163466133111690969351997882368 }, { target := 949, numerator := 163466094138332427622142705664 }, { target := 951, numerator := 52298790184363055742214733824 }, { target := 954, numerator := 188117193035763692113412227072 }, { target := 956, numerator := 52298807631524184957630021632 }, { target := 961, numerator := 166338541201513015139333308416 }, { target := 963, numerator := 166338501543319099673011027968 }, { target := 965, numerator := 19826383441679918465181286400 }, { target := 982, numerator := 66433598342299016753624121344 }, { target := 985, numerator := 238959677640024149441361477632 }, { target := 987, numerator := 66433620504909099811043540992 }, { target := 992, numerator := 8094968253134856309763473408 }, { target := 994, numerator := 8094966323144257597901635584 }, { target := 996, numerator := 67847079158092612854765060096 }, { target := 999, numerator := 244043926100450195174156402688 }, { target := 1001, numerator := 67847101792247591296384892928 }, { target := 1006, numerator := 198457286205886799852265799680 }, { target := 1008, numerator := 198457238889988250787265904640 }, { target := 1010, numerator := 19690983749883079997614194688 }, { target := 1011, numerator := 8094968253134856309763473408 }, { target := 1013, numerator := 8094966323144257597901635584 }, { target := 1015, numerator := 19826383441679918465181286400 }]

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
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1656113273070321369643745280 }, { target := 57, numerator := 195741956243057643361696481280 }, { target := 59, numerator := 1857552146202381857308362670080 }, { target := 67, numerator := 195742090493485097181522165760 }, { target := 74, numerator := 1656113273070321369643745280 }, { target := 110, numerator := 3270861947716370959140126720 }, { target := 112, numerator := 128005051652155076142962835456 }, { target := 115, numerator := 128005051652155076142962835456 }, { target := 122, numerator := 3270861947716370959140126720 }, { target := 136, numerator := 28770079816840653481162309632 }, { target := 137, numerator := 21577559862630490110871732224 }, { target := 138, numerator := 22776313188332184005920161792 }, { target := 139, numerator := 29369456479691500428686524416 }, { target := 140, numerator := 393191090830155597575884898304 }, { target := 141, numerator := 687485032289921448810274357248 }, { target := 142, numerator := 20978183199779643163347517440 }, { target := 143, numerator := 393191090830155597575884898304 }, { target := 144, numerator := 22176936525481337058395947008 }, { target := 145, numerator := 22776313188332184005920161792 }, { target := 146, numerator := 22776313188332184005920161792 }, { target := 147, numerator := 22176936525481337058395947008 }, { target := 148, numerator := 687485032289921448810274357248 }, { target := 149, numerator := 22176936525481337058395947008 }, { target := 150, numerator := 28770079816840653481162309632 }, { target := 151, numerator := 29369456479691500428686524416 }, { target := 152, numerator := 66211101383903291237455626240 }, { target := 153, numerator := 7825727092848639684070594314240 }, { target := 155, numerator := 74264590156974526265532497264640 }, { target := 163, numerator := 7825732460155820610083178414080 }, { target := 170, numerator := 66211101383903291237455626240 }, { target := 206, numerator := 536031278269902408831624806400 }, { target := 208, numerator := 20977562660513550564443522334720 }, { target := 211, numerator := 20977562660513550564443522334720 }, { target := 218, numerator := 536031278269902408831624806400 }, { target := 267, numerator := 7897883455047664821778513920 }, { target := 268, numerator := 5923412591285748616333885440 }, { target := 269, numerator := 6252491068579401317241323520 }, { target := 270, numerator := 8062422693694491172232232960 }, { target := 271, numerator := 107937740552318085897639690240 }, { target := 272, numerator := 188726506727909823970415738880 }, { target := 273, numerator := 5758873352638922265880166400 }, { target := 274, numerator := 107937740552318085897639690240 }, { target := 275, numerator := 6087951829932574966787604480 }, { target := 276, numerator := 6252491068579401317241323520 }, { target := 277, numerator := 6252491068579401317241323520 }, { target := 278, numerator := 6087951829932574966787604480 }, { target := 279, numerator := 188726506727909823970415738880 }, { target := 280, numerator := 6087951829932574966787604480 }, { target := 281, numerator := 7897883455047664821778513920 }, { target := 282, numerator := 8062422693694491172232232960 }, { target := 283, numerator := 66211085203100334043095367680 }, { target := 284, numerator := 7825725180381614676301766983680 }, { target := 286, numerator := 74264572008043683696303648276480 }, { target := 294, numerator := 7825730547687483928922879426560 }, { target := 301, numerator := 66211085203100334043095367680 }, { target := 302, numerator := 5518649554984125546648462950400 }, { target := 304, numerator := 215972129862920641850220918865920 }, { target := 307, numerator := 215972129862920641850220918865920 }, { target := 314, numerator := 5518649554984125546648462950400 }, { target := 660, numerator := 1656113273070321369643745280 }, { target := 661, numerator := 195741956243057643361696481280 }, { target := 663, numerator := 1857552146202381857308362670080 }, { target := 671, numerator := 195742090493485097181522165760 }, { target := 678, numerator := 1656113273070321369643745280 }]

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
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left7.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1798880976256368641342177280 }, { target := 5, numerator := 43579342360275253214450810880 }, { target := 6, numerator := 33018170177092701836248350720 }, { target := 7, numerator := 36790017385372184471320657920 }, { target := 8, numerator := 1798880976256368641342177280 }, { target := 9, numerator := 36790017385372184471320657920 }, { target := 10, numerator := 36731988966783269353858007040 }, { target := 11, numerator := 1798880976256368641342177280 }, { target := 12, numerator := 43579342360275253214450810880 }, { target := 13, numerator := 1798880976256368641342177280 }, { target := 14, numerator := 21996964234167707586242019328 }, { target := 15, numerator := 3858060864275896114766103445504 }, { target := 20, numerator := 3858061326814833267397841911808 }, { target := 28, numerator := 21996501695230554954503553024 }, { target := 126, numerator := 1798882262916767782583402496 }, { target := 127, numerator := 43579373530661051765165654016 }, { target := 128, numerator := 33018193793536802202901807104 }, { target := 129, numerator := 36790043699652605617996038144 }, { target := 130, numerator := 1798882262916767782583402496 }, { target := 131, numerator := 36790043699652605617996038144 }, { target := 132, numerator := 36732015239558516334686896128 }, { target := 133, numerator := 1798882262916767782583402496 }, { target := 134, numerator := 43579373530661051765165654016 }, { target := 135, numerator := 1798882262916767782583402496 }, { target := 136, numerator := 78845805057064567581521739776 }, { target := 137, numerator := 13828813447379638507273787015168 }, { target := 142, numerator := 13828815105301817304602625703936 }, { target := 150, numerator := 78844147134885770252683051008 }, { target := 257, numerator := 34950318838796171991507271680 }, { target := 260, numerator := 129831724768989273912036556800 }, { target := 262, numerator := 34942961834310850022064783360 }, { target := 267, numerator := 22003356514497674265210388480 }, { target := 268, numerator := 3859182010190031760361405808640 }, { target := 273, numerator := 3859182472863381940096760545280 }, { target := 281, numerator := 22002893841147494529855651840 }, { target := 353, numerator := 6931865835277504441969803264000 }, { target := 356, numerator := 25750154137715661892894064640000 }, { target := 358, numerator := 6930406684982567009966358528000 }, { target := 389, numerator := 27694218128867674162754224128 }, { target := 391, numerator := 27694224731684596893232398336 }, { target := 679, numerator := 536031278269902408831624806400 }, { target := 681, numerator := 20977562660513550564443522334720 }, { target := 684, numerator := 20977562660513550564443522334720 }, { target := 691, numerator := 536031278269902408831624806400 }, { target := 695, numerator := 6931865835277504441969803264000 }, { target := 698, numerator := 25750154137715661892894064640000 }, { target := 700, numerator := 6930406684982567009966358528000 }, { target := 731, numerator := 1251728276975055840956727164928 }, { target := 733, numerator := 1251728575410368634858227367936 }, { target := 749, numerator := 19807040628566084398385987584 }, { target := 965, numerator := 19807040628566084398385987584 }, { target := 966, numerator := 3270861947716370959140126720 }, { target := 968, numerator := 128005051652155076142962835456 }, { target := 971, numerator := 128005051652155076142962835456 }, { target := 978, numerator := 3270861947716370959140126720 }, { target := 982, numerator := 34950318838796171991507271680 }, { target := 985, numerator := 129831724768989273912036556800 }, { target := 987, numerator := 34942961834310850022064783360 }, { target := 992, numerator := 27842030543344120475701739520 }, { target := 994, numerator := 27842037181402273240307466240 }, { target := 1010, numerator := 19807040628566084398385987584 }, { target := 1015, numerator := 19807040628566084398385987584 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left6.expected,
    Slot15.Left14.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2118618332964361125054382080 }, { target := 57, numerator := 682452217089884034831231221760 }, { target := 59, numerator := 7258166319258593266241768521728 }, { target := 67, numerator := 682454274000886912851740983296 }, { target := 74, numerator := 2118618332964361125054382080 }, { target := 110, numerator := 2122981120974126426536017920 }, { target := 112, numerator := 83085196934513624105856532480 }, { target := 115, numerator := 83085227407343631772596305920 }, { target := 122, numerator := 2123011593804134093275791360 }, { target := 152, numerator := 82914454435961135781401067520 }, { target := 153, numerator := 26708516762170257704108886589440 }, { target := 155, numerator := 284056307454277950370061989445632 }, { target := 163, numerator := 26708597261640583879968868532224 }, { target := 170, numerator := 82914454435961135781401067520 }, { target := 206, numerator := 683857564293592753813837578240 }, { target := 208, numerator := 26763516567881167741710300610560 }, { target := 211, numerator := 26763526383830589191913461514240 }, { target := 218, numerator := 683867380243014204016998481920 }, { target := 257, numerator := 21554612119769453868785598464 }, { target := 260, numerator := 77260240421547729842222399488 }, { target := 262, numerator := 21560875853328616830261002240 }, { target := 283, numerator := 82914484846168590629554094080 }, { target := 284, numerator := 26708526557947617322355927285760 }, { target := 286, numerator := 284056411636489572041320906620928 }, { target := 294, numerator := 26708607057447467971473043357696 }, { target := 301, numerator := 82914484846168590629554094080 }, { target := 302, numerator := 7273112777758382155246728118272 }, { target := 304, numerator := 284641253516991255839305910714368 }, { target := 307, numerator := 284641357913741238017381286019072 }, { target := 314, numerator := 7273217174508364333322103422976 }, { target := 353, numerator := 3780476459327020690154719281152 }, { target := 356, numerator := 13550720306755916343507769360384 }, { target := 358, numerator := 3781575059345259640866021048320 }, { target := 389, numerator := 1798880976256368641342177280 }, { target := 391, numerator := 1798882262916767782583402496 }, { target := 656, numerator := 43579342360275253214450810880 }, { target := 658, numerator := 43579373530661051765165654016 }, { target := 660, numerator := 2118648743171815973207408640 }, { target := 661, numerator := 682462012867243653078271918080 }, { target := 663, numerator := 7258270501470214937500685697024 }, { target := 671, numerator := 682464069807771004355915808768 }, { target := 678, numerator := 2118648743171815973207408640 }, { target := 679, numerator := 683859625440312146169591496704 }, { target := 681, numerator := 26763597233120909987947296587776 }, { target := 684, numerator := 26763607049099916710002561122304 }, { target := 691, numerator := 683869441419318868224856031232 }, { target := 695, numerator := 3780476912564443567322199752704 }, { target := 698, numerator := 13550721931337795384400379117568 }, { target := 700, numerator := 3781575512714392540935765360640 }, { target := 731, numerator := 33018170177092701836248350720 }, { target := 733, numerator := 33018193793536802202901807104 }, { target := 745, numerator := 36790017385372184471320657920 }, { target := 747, numerator := 36790043699652605617996038144 }, { target := 872, numerator := 1798880976256368641342177280 }, { target := 874, numerator := 1798882262916767782583402496 }, { target := 947, numerator := 36790017385372184471320657920 }, { target := 949, numerator := 36790043699652605617996038144 }, { target := 966, numerator := 2122981120974126426536017920 }, { target := 968, numerator := 83085196934513624105856532480 }, { target := 971, numerator := 83085227407343631772596305920 }, { target := 978, numerator := 2123011593804134093275791360 }, { target := 982, numerator := 21554158882346576701305126912 }, { target := 985, numerator := 77258615839668688949612642304 }, { target := 987, numerator := 21560422484195716760516689920 }]

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
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19807040628566084398385987584 }, { target := 1, numerator := 19807040628566084398385987584 }, { target := 2, numerator := 19807040628566084398385987584 }, { target := 3, numerator := 19807040628566084398385987584 }, { target := 4, numerator := 26854999397689865854791974912 }, { target := 6, numerator := 1213797117066720815473189978112 }, { target := 11, numerator := 26998332648091268340074414080 }, { target := 14, numerator := 35263306768695839203371515904 }, { target := 15, numerator := 6993942245742676123539682099200 }, { target := 20, numerator := 6993942245742676123539682099200 }, { target := 28, numerator := 35263306768695839203371515904 }, { target := 56, numerator := 3270372590752320035896688640 }, { target := 57, numerator := 535951082088234260655557836800 }, { target := 59, numerator := 5517823904242805360300969164800 }, { target := 67, numerator := 535951082088234260655557836800 }, { target := 74, numerator := 3270372590752320035896688640 }, { target := 110, numerator := 1658956385985463552252575744 }, { target := 112, numerator := 66324768510742610192369713152 }, { target := 115, numerator := 66324752302161450496388235264 }, { target := 122, numerator := 1658956385985463552252575744 }, { target := 126, numerator := 26855005800421427290407174144 }, { target := 128, numerator := 1213797406458539282286765932544 }, { target := 133, numerator := 26998339084996143748176936960 }, { target := 136, numerator := 130994396931099625618711511040 }, { target := 137, numerator := 25980752532978787223278190592000 }, { target := 142, numerator := 25980752532978787223278190592000 }, { target := 150, numerator := 130994396931099625618711511040 }, { target := 152, numerator := 127985900686916872211762511872 }, { target := 153, numerator := 20974424186147824419834838384640 }, { target := 155, numerator := 215939818054144022963050030039040 }, { target := 163, numerator := 20974424186147824419834838384640 }, { target := 170, numerator := 127985900686916872211762511872 }, { target := 206, numerator := 196077993936178772363175788544 }, { target := 208, numerator := 7839161817471555803699900055552 }, { target := 211, numerator := 7839159901721325602784688472064 }, { target := 218, numerator := 196077993936178772363175788544 }, { target := 267, numerator := 35255883880588260619277303808 }, { target := 268, numerator := 6992470028430172087667549798400 }, { target := 273, numerator := 6992470028430172087667549798400 }, { target := 281, numerator := 35255883880588260619277303808 }, { target := 283, numerator := 127985900686916872211762511872 }, { target := 284, numerator := 20974424186147824419834838384640 }, { target := 286, numerator := 215939818054144022963050030039040 }, { target := 294, numerator := 20974424186147824419834838384640 }, { target := 301, numerator := 127985900686916872211762511872 }, { target := 302, numerator := 1860741076925476075089149558784 }, { target := 304, numerator := 74392083015613109143241565929472 }, { target := 307, numerator := 74392064835525303754151379861504 }, { target := 314, numerator := 1860741076925476075089149558784 }, { target := 660, numerator := 3270372590752320035896688640 }, { target := 661, numerator := 535951082088234260655557836800 }, { target := 663, numerator := 5517823904242805360300969164800 }, { target := 671, numerator := 535951082088234260655557836800 }, { target := 678, numerator := 3270372590752320035896688640 }, { target := 961, numerator := 36731988966783269353858007040 }, { target := 963, numerator := 36732015239558516334686896128 }, { target := 992, numerator := 1798880976256368641342177280 }, { target := 994, numerator := 1798882262916767782583402496 }, { target := 1006, numerator := 43579342360275253214450810880 }, { target := 1008, numerator := 43579373530661051765165654016 }, { target := 1011, numerator := 1798880976256368641342177280 }, { target := 1013, numerator := 1798882262916767782583402496 }]

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
    Slot21.Left11.expected,
    Slot21.Left18.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected,
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19884411881021420665567182848 }, { target := 1, numerator := 19826383441679918465181286400 }, { target := 2, numerator := 19690983749883079997614194688 }, { target := 3, numerator := 19826383441679918465181286400 }, { target := 257, numerator := 8062417270351733501624057856 }, { target := 260, numerator := 29369456479691500428686524416 }, { target := 262, numerator := 8062422693694491172232232960 }, { target := 353, numerator := 6046812952763800126218043392 }, { target := 356, numerator := 22027092359768625321514893312 }, { target := 358, numerator := 6046817020270868379174174720 }, { target := 379, numerator := 6382747005695122355452379136 }, { target := 382, numerator := 23250819713089104506043498496 }, { target := 384, numerator := 6382751299174805511350517760 }, { target := 524, numerator := 8230384296817394616241225728 }, { target := 527, numerator := 29981320156351740020950827008 }, { target := 529, numerator := 8230389833146459738320404480 }, { target := 620, numerator := 110186369361473691188862124032 }, { target := 623, numerator := 401382571889117172525382500352 }, { target := 625, numerator := 110186443480491379353840517120 }, { target := 646, numerator := 192658179356113298465891549184 }, { target := 649, numerator := 701807637129294812327155073024 }, { target := 651, numerator := 192658308951407945303132733440 }, { target := 679, numerator := 196078128417079063013593448448 }, { target := 681, numerator := 7839167193992997984521089449984 }, { target := 684, numerator := 7839165278241453858414592524288 }, { target := 691, numerator := 196078128417079063013593448448 }, { target := 695, numerator := 5878845926298139011600875520 }, { target := 698, numerator := 21415228683108385729250590720 }, { target := 700, numerator := 5878849880818899813086003200 }, { target := 721, numerator := 110186369361473691188862124032 }, { target := 724, numerator := 401382571889117172525382500352 }, { target := 726, numerator := 110186443480491379353840517120 }, { target := 735, numerator := 6214779979229461240835211264 }, { target := 738, numerator := 22638956036428864913779195904 }, { target := 740, numerator := 6214784159722836945262346240 }, { target := 836, numerator := 6382747005695122355452379136 }, { target := 839, numerator := 23250819713089104506043498496 }, { target := 841, numerator := 6382751299174805511350517760 }, { target := 862, numerator := 6382747005695122355452379136 }, { target := 865, numerator := 23250819713089104506043498496 }, { target := 867, numerator := 6382751299174805511350517760 }, { target := 911, numerator := 6214779979229461240835211264 }, { target := 914, numerator := 22638956036428864913779195904 }, { target := 916, numerator := 6214784159722836945262346240 }, { target := 937, numerator := 192658179356113298465891549184 }, { target := 940, numerator := 701807637129294812327155073024 }, { target := 942, numerator := 192658308951407945303132733440 }, { target := 951, numerator := 6214779979229461240835211264 }, { target := 954, numerator := 22638956036428864913779195904 }, { target := 956, numerator := 6214784159722836945262346240 }, { target := 966, numerator := 1658956385985463552252575744 }, { target := 968, numerator := 66324768510742610192369713152 }, { target := 971, numerator := 66324752302161450496388235264 }, { target := 978, numerator := 1658956385985463552252575744 }, { target := 982, numerator := 8062417270351733501624057856 }, { target := 985, numerator := 29369456479691500428686524416 }, { target := 987, numerator := 8062422693694491172232232960 }, { target := 996, numerator := 8230384296817394616241225728 }, { target := 999, numerator := 29981320156351740020950827008 }, { target := 1001, numerator := 8230389833146459738320404480 }]

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
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot25.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 8094968253134856309763473408 }, { target := 5, numerator := 198457286205886799852265799680 }, { target := 6, numerator := 146753940589089975680228130816 }, { target := 7, numerator := 163727261119856609878119284736 }, { target := 8, numerator := 8094968253134856309763473408 }, { target := 9, numerator := 163466133111690969351997882368 }, { target := 10, numerator := 166338541201513015139333308416 }, { target := 11, numerator := 8094968253134856309763473408 }, { target := 12, numerator := 198457286205886799852265799680 }, { target := 13, numerator := 8094968253134856309763473408 }, { target := 14, numerator := 67895462364501195606393356288 }, { target := 15, numerator := 50560450696968975451569520640 }, { target := 16, numerator := 53449619308224345477373493248 }, { target := 17, numerator := 69340046670128880619295342592 }, { target := 18, numerator := 928867708518601463295977193472 }, { target := 19, numerator := 1680051547444997670005010071552 }, { target := 20, numerator := 50560450696968975451569520640 }, { target := 21, numerator := 928867708518601463295977193472 }, { target := 22, numerator := 54894203613852030490275479552 }, { target := 23, numerator := 54894203613852030490275479552 }, { target := 24, numerator := 53449619308224345477373493248 }, { target := 25, numerator := 53449619308224345477373493248 }, { target := 26, numerator := 1680051547444997670005010071552 }, { target := 27, numerator := 53449619308224345477373493248 }, { target := 28, numerator := 67895462364501195606393356288 }, { target := 29, numerator := 69340046670128880619295342592 }, { target := 126, numerator := 8094966323144257597901635584 }, { target := 127, numerator := 198457238889988250787265904640 }, { target := 128, numerator := 146753905600228153871636103168 }, { target := 129, numerator := 163727222084240306899494371328 }, { target := 130, numerator := 8094966323144257597901635584 }, { target := 131, numerator := 163466094138332427622142705664 }, { target := 132, numerator := 166338501543319099673011027968 }, { target := 133, numerator := 8094966323144257597901635584 }, { target := 134, numerator := 198457238889988250787265904640 }, { target := 135, numerator := 8094966323144257597901635584 }, { target := 136, numerator := 244217959055085805541538136064 }, { target := 137, numerator := 181864437594212833913911377920 }, { target := 138, numerator := 192256691171024995851849170944 }, { target := 139, numerator := 249414085843491886510507032576 }, { target := 140, numerator := 3341109524945110063047000457216 }, { target := 141, numerator := 6043095454916272166910826643456 }, { target := 142, numerator := 181864437594212833913911377920 }, { target := 143, numerator := 3341109524945110063047000457216 }, { target := 144, numerator := 197452817959431076820818067456 }, { target := 145, numerator := 197452817959431076820818067456 }, { target := 146, numerator := 192256691171024995851849170944 }, { target := 147, numerator := 192256691171024995851849170944 }, { target := 148, numerator := 6043095454916272166910826643456 }, { target := 149, numerator := 192256691171024995851849170944 }, { target := 150, numerator := 244217959055085805541538136064 }, { target := 151, numerator := 249414085843491886510507032576 }]

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
    Slot25.Left5.expected,
    Slot26.Left0.expected,
    Slot26.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1343177731936771341834780672 }, { target := 57, numerator := 19476077113083184456604319744 }, { target := 58, numerator := 34474895119710464440426037248 }, { target := 59, numerator := 1119314776613976118195650560 }, { target := 60, numerator := 21490843710988341469356490752 }, { target := 61, numerator := 1119314776613976118195650560 }, { target := 62, numerator := 34251032164387669216786907136 }, { target := 63, numerator := 35818072851647235782260817920 }, { target := 64, numerator := 21490843710988341469356490752 }, { target := 65, numerator := 548688103496171093139507904512 }, { target := 66, numerator := 35146483985678850111343427584 }, { target := 67, numerator := 19476077113083184456604319744 }, { target := 68, numerator := 34251032164387669216786907136 }, { target := 69, numerator := 1119314776613976118195650560 }, { target := 70, numerator := 35146483985678850111343427584 }, { target := 71, numerator := 1119314776613976118195650560 }, { target := 72, numerator := 34251032164387669216786907136 }, { target := 73, numerator := 35818072851647235782260817920 }, { target := 74, numerator := 1343177731936771341834780672 }, { target := 152, numerator := 52391163503926145811147128832 }, { target := 153, numerator := 759671870806929114261633368064 }, { target := 154, numerator := 1344706529934104409152776306688 }, { target := 155, numerator := 43659302919938454842622607360 }, { target := 156, numerator := 838258616062818332978354061312 }, { target := 157, numerator := 43659302919938454842622607360 }, { target := 158, numerator := 1335974669350116718184251785216 }, { target := 159, numerator := 1397097693438030554963923435520 }, { target := 160, numerator := 838258616062818332978354061312 }, { target := 161, numerator := 21401790291353830563853602127872 }, { target := 162, numerator := 1370902111686067482058349871104 }, { target := 163, numerator := 759671870806929114261633368064 }, { target := 164, numerator := 1335974669350116718184251785216 }, { target := 165, numerator := 43659302919938454842622607360 }, { target := 166, numerator := 1370902111686067482058349871104 }, { target := 167, numerator := 43659302919938454842622607360 }, { target := 168, numerator := 1335974669350116718184251785216 }, { target := 169, numerator := 1397097693438030554963923435520 }, { target := 170, numerator := 52391163503926145811147128832 }, { target := 267, numerator := 67895485014797075112509046784 }, { target := 268, numerator := 50560467564210587849740779520 }, { target := 269, numerator := 53449637139308335726868824064 }, { target := 270, numerator := 69340069802345949051073069056 }, { target := 271, numerator := 928868018393925942496666320896 }, { target := 272, numerator := 1680052107919340390549957902336 }, { target := 273, numerator := 50560467564210587849740779520 }, { target := 274, numerator := 928868018393925942496666320896 }, { target := 275, numerator := 54894221926857209665432846336 }, { target := 276, numerator := 54894221926857209665432846336 }, { target := 277, numerator := 53449637139308335726868824064 }, { target := 278, numerator := 53449637139308335726868824064 }, { target := 279, numerator := 1680052107919340390549957902336 }, { target := 280, numerator := 53449637139308335726868824064 }, { target := 281, numerator := 67895485014797075112509046784 }, { target := 282, numerator := 69340069802345949051073069056 }]

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
    Slot26.Left5.expected,
    Slot26.Left12.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 57971770943707764643332096 }, { target := 111, numerator := 65451999452573282661826560 }, { target := 112, numerator := 56101713816491385138708480 }, { target := 113, numerator := 738672565250469904326328320 }, { target := 114, numerator := 65451999452573282661826560 }, { target := 115, numerator := 56101713816491385138708480 }, { target := 116, numerator := 65451999452573282661826560 }, { target := 117, numerator := 65451999452573282661826560 }, { target := 118, numerator := 2713452891590966661208866816 }, { target := 119, numerator := 67322056579789662166450176 }, { target := 120, numerator := 738672565250469904326328320 }, { target := 121, numerator := 2713452891590966661208866816 }, { target := 122, numerator := 57971770943707764643332096 }, { target := 123, numerator := 65451999452573282661826560 }, { target := 124, numerator := 67322056579789662166450176 }, { target := 125, numerator := 65451999452573282661826560 }, { target := 283, numerator := 52391144287030507024221732864 }, { target := 284, numerator := 759671592161942351851215126528 }, { target := 285, numerator := 1344706036700449680288357810176 }, { target := 286, numerator := 43659286905858755853518110720 }, { target := 287, numerator := 838258308592488112387547725824 }, { target := 288, numerator := 43659286905858755853518110720 }, { target := 289, numerator := 1335974179319277929117654188032 }, { target := 290, numerator := 1397097180987480187312579543040 }, { target := 291, numerator := 838258308592488112387547725824 }, { target := 292, numerator := 21401782441251962119394577874944 }, { target := 293, numerator := 1370901608843964933800468676608 }, { target := 294, numerator := 759671592161942351851215126528 }, { target := 295, numerator := 1335974179319277929117654188032 }, { target := 296, numerator := 43659286905858755853518110720 }, { target := 297, numerator := 1370901608843964933800468676608 }, { target := 298, numerator := 43659286905858755853518110720 }, { target := 299, numerator := 1335974179319277929117654188032 }, { target := 300, numerator := 1397097180987480187312579543040 }, { target := 301, numerator := 52391144287030507024221732864 }, { target := 660, numerator := 1343184137568650937476579328 }, { target := 661, numerator := 19476169994745438593410400256 }, { target := 662, numerator := 34475059530928707395232202752 }, { target := 663, numerator := 1119320114640542447897149440 }, { target := 664, numerator := 21490946201098414999625269248 }, { target := 665, numerator := 1119320114640542447897149440 }, { target := 666, numerator := 34251195508000598905652772864 }, { target := 667, numerator := 35818243668497358332708782080 }, { target := 668, numerator := 21490946201098414999625269248 }, { target := 669, numerator := 548690720196793907959182655488 }, { target := 670, numerator := 35146651599713032863970492416 }, { target := 671, numerator := 19476169994745438593410400256 }, { target := 672, numerator := 34251195508000598905652772864 }, { target := 673, numerator := 1119320114640542447897149440 }, { target := 674, numerator := 35146651599713032863970492416 }, { target := 675, numerator := 1119320114640542447897149440 }, { target := 676, numerator := 34251195508000598905652772864 }, { target := 677, numerator := 35818243668497358332708782080 }, { target := 678, numerator := 1343184137568650937476579328 }]

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
    Slot27.Left1.expected,
    Slot27.Left2.expected,
    Slot27.Left3.expected,
    Slot27.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 869576564155616469649981440 }, { target := 207, numerator := 981779991788599239927398400 }, { target := 208, numerator := 841525707247370777080627200 }, { target := 209, numerator := 11080088478757048564894924800 }, { target := 210, numerator := 981779991788599239927398400 }, { target := 211, numerator := 841525707247370777080627200 }, { target := 212, numerator := 981779991788599239927398400 }, { target := 213, numerator := 981779991788599239927398400 }, { target := 214, numerator := 40701793373864499918133002240 }, { target := 215, numerator := 1009830848696844932496752640 }, { target := 216, numerator := 11080088478757048564894924800 }, { target := 217, numerator := 40701793373864499918133002240 }, { target := 218, numerator := 869576564155616469649981440 }, { target := 219, numerator := 981779991788599239927398400 }, { target := 220, numerator := 1009830848696844932496752640 }, { target := 221, numerator := 981779991788599239927398400 }, { target := 241, numerator := 1526589968184304468941078528 }, { target := 242, numerator := 1723569318917763110094766080 }, { target := 243, numerator := 1477345130500939808652656640 }, { target := 244, numerator := 19451710884929040813926645760 }, { target := 245, numerator := 1723569318917763110094766080 }, { target := 246, numerator := 1477345130500939808652656640 }, { target := 247, numerator := 1723569318917763110094766080 }, { target := 248, numerator := 1723569318917763110094766080 }, { target := 249, numerator := 71454259478562122078500159488 }, { target := 250, numerator := 1772814156601127770383187968 }, { target := 251, numerator := 19451710884929040813926645760 }, { target := 252, numerator := 71454259478562122078500159488 }, { target := 253, numerator := 1526589968184304468941078528 }, { target := 254, numerator := 1723569318917763110094766080 }, { target := 255, numerator := 1772814156601127770383187968 }, { target := 256, numerator := 1723569318917763110094766080 }, { target := 302, numerator := 57971770943707764643332096 }, { target := 303, numerator := 65451999452573282661826560 }, { target := 304, numerator := 56101713816491385138708480 }, { target := 305, numerator := 738672565250469904326328320 }, { target := 306, numerator := 65451999452573282661826560 }, { target := 307, numerator := 56101713816491385138708480 }, { target := 308, numerator := 65451999452573282661826560 }, { target := 309, numerator := 65451999452573282661826560 }, { target := 310, numerator := 2713452891590966661208866816 }, { target := 311, numerator := 67322056579789662166450176 }, { target := 312, numerator := 738672565250469904326328320 }, { target := 313, numerator := 2713452891590966661208866816 }, { target := 314, numerator := 57971770943707764643332096 }, { target := 315, numerator := 65451999452573282661826560 }, { target := 316, numerator := 67322056579789662166450176 }, { target := 317, numerator := 65451999452573282661826560 }, { target := 337, numerator := 966196182395129410722201600 }, { target := 338, numerator := 1090866657542888044363776000 }, { target := 339, numerator := 935028563608189752311808000 }, { target := 340, numerator := 12311209420841165072105472000 }, { target := 341, numerator := 1090866657542888044363776000 }, { target := 342, numerator := 935028563608189752311808000 }, { target := 343, numerator := 1090866657542888044363776000 }, { target := 344, numerator := 1090866657542888044363776000 }, { target := 345, numerator := 45224214859849444353481113600 }, { target := 346, numerator := 1122034276329827702774169600 }, { target := 347, numerator := 12311209420841165072105472000 }, { target := 348, numerator := 45224214859849444353481113600 }, { target := 349, numerator := 966196182395129410722201600 }, { target := 350, numerator := 1090866657542888044363776000 }, { target := 351, numerator := 1122034276329827702774169600 }, { target := 352, numerator := 1090866657542888044363776000 }]

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
    Slot27.Left5.expected,
    Slot27.Left6.expected,
    Slot27.Left7.expected,
    Slot27.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 363, numerator := 57971770943707764643332096 }, { target := 364, numerator := 65451999452573282661826560 }, { target := 365, numerator := 56101713816491385138708480 }, { target := 366, numerator := 738672565250469904326328320 }, { target := 367, numerator := 65451999452573282661826560 }, { target := 368, numerator := 56101713816491385138708480 }, { target := 369, numerator := 65451999452573282661826560 }, { target := 370, numerator := 65451999452573282661826560 }, { target := 371, numerator := 2713452891590966661208866816 }, { target := 372, numerator := 67322056579789662166450176 }, { target := 373, numerator := 738672565250469904326328320 }, { target := 374, numerator := 2713452891590966661208866816 }, { target := 375, numerator := 57971770943707764643332096 }, { target := 376, numerator := 65451999452573282661826560 }, { target := 377, numerator := 67322056579789662166450176 }, { target := 378, numerator := 65451999452573282661826560 }, { target := 473, numerator := 1526589968184304468941078528 }, { target := 474, numerator := 1723569318917763110094766080 }, { target := 475, numerator := 1477345130500939808652656640 }, { target := 476, numerator := 19451710884929040813926645760 }, { target := 477, numerator := 1723569318917763110094766080 }, { target := 478, numerator := 1477345130500939808652656640 }, { target := 479, numerator := 1723569318917763110094766080 }, { target := 480, numerator := 1723569318917763110094766080 }, { target := 481, numerator := 71454259478562122078500159488 }, { target := 482, numerator := 1772814156601127770383187968 }, { target := 483, numerator := 19451710884929040813926645760 }, { target := 484, numerator := 71454259478562122078500159488 }, { target := 485, numerator := 1526589968184304468941078528 }, { target := 486, numerator := 1723569318917763110094766080 }, { target := 487, numerator := 1772814156601127770383187968 }, { target := 488, numerator := 1723569318917763110094766080 }, { target := 508, numerator := 1516928006360353174833856512 }, { target := 509, numerator := 1712660652342334229651128320 }, { target := 510, numerator := 1467994844864857911129538560 }, { target := 511, numerator := 19328598790720629163205591040 }, { target := 512, numerator := 1712660652342334229651128320 }, { target := 513, numerator := 1467994844864857911129538560 }, { target := 514, numerator := 1712660652342334229651128320 }, { target := 515, numerator := 1712660652342334229651128320 }, { target := 516, numerator := 71002017329963627634965348352 }, { target := 517, numerator := 1761593813837829493355446272 }, { target := 518, numerator := 19328598790720629163205591040 }, { target := 519, numerator := 71002017329963627634965348352 }, { target := 520, numerator := 1516928006360353174833856512 }, { target := 521, numerator := 1712660652342334229651128320 }, { target := 522, numerator := 1761593813837829493355446272 }, { target := 523, numerator := 1712660652342334229651128320 }, { target := 569, numerator := 966196182395129410722201600 }, { target := 570, numerator := 1090866657542888044363776000 }, { target := 571, numerator := 935028563608189752311808000 }, { target := 572, numerator := 12311209420841165072105472000 }, { target := 573, numerator := 1090866657542888044363776000 }, { target := 574, numerator := 935028563608189752311808000 }, { target := 575, numerator := 1090866657542888044363776000 }, { target := 576, numerator := 1090866657542888044363776000 }, { target := 577, numerator := 45224214859849444353481113600 }, { target := 578, numerator := 1122034276329827702774169600 }, { target := 579, numerator := 12311209420841165072105472000 }, { target := 580, numerator := 45224214859849444353481113600 }, { target := 581, numerator := 966196182395129410722201600 }, { target := 582, numerator := 1090866657542888044363776000 }, { target := 583, numerator := 1122034276329827702774169600 }, { target := 584, numerator := 1090866657542888044363776000 }]

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
    Slot27.Left9.expected,
    Slot27.Left10.expected,
    Slot27.Left11.expected,
    Slot27.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 604, numerator := 23410933499433985621798944768 }, { target := 605, numerator := 26431699112264177314934292480 }, { target := 606, numerator := 22655742096226437698515107840 }, { target := 607, numerator := 298300604266981429697115586560 }, { target := 608, numerator := 26431699112264177314934292480 }, { target := 609, numerator := 22655742096226437698515107840 }, { target := 610, numerator := 26431699112264177314934292480 }, { target := 611, numerator := 26431699112264177314934292480 }, { target := 612, numerator := 1095782726054152036684847382528 }, { target := 613, numerator := 27186890515471725238218129408 }, { target := 614, numerator := 298300604266981429697115586560 }, { target := 615, numerator := 1095782726054152036684847382528 }, { target := 616, numerator := 23410933499433985621798944768 }, { target := 617, numerator := 26431699112264177314934292480 }, { target := 618, numerator := 27186890515471725238218129408 }, { target := 619, numerator := 26431699112264177314934292480 }, { target := 630, numerator := 1497604082712450586619412480 }, { target := 631, numerator := 1690843319191476468763852800 }, { target := 632, numerator := 1449294273592694116083302400 }, { target := 633, numerator := 19082374602303805861763481600 }, { target := 634, numerator := 1690843319191476468763852800 }, { target := 635, numerator := 1449294273592694116083302400 }, { target := 636, numerator := 1690843319191476468763852800 }, { target := 637, numerator := 1690843319191476468763852800 }, { target := 638, numerator := 70097533032766638747895726080 }, { target := 639, numerator := 1739153128311232939299962880 }, { target := 640, numerator := 19082374602303805861763481600 }, { target := 641, numerator := 70097533032766638747895726080 }, { target := 642, numerator := 1497604082712450586619412480 }, { target := 643, numerator := 1690843319191476468763852800 }, { target := 644, numerator := 1739153128311232939299962880 }, { target := 645, numerator := 1690843319191476468763852800 }, { target := 679, numerator := 869576564155616469649981440 }, { target := 680, numerator := 981779991788599239927398400 }, { target := 681, numerator := 841525707247370777080627200 }, { target := 682, numerator := 11080088478757048564894924800 }, { target := 683, numerator := 981779991788599239927398400 }, { target := 684, numerator := 841525707247370777080627200 }, { target := 685, numerator := 981779991788599239927398400 }, { target := 686, numerator := 981779991788599239927398400 }, { target := 687, numerator := 40701793373864499918133002240 }, { target := 688, numerator := 1009830848696844932496752640 }, { target := 689, numerator := 11080088478757048564894924800 }, { target := 690, numerator := 40701793373864499918133002240 }, { target := 691, numerator := 869576564155616469649981440 }, { target := 692, numerator := 981779991788599239927398400 }, { target := 693, numerator := 1009830848696844932496752640 }, { target := 694, numerator := 981779991788599239927398400 }, { target := 705, numerator := 1526589968184304468941078528 }, { target := 706, numerator := 1723569318917763110094766080 }, { target := 707, numerator := 1477345130500939808652656640 }, { target := 708, numerator := 19451710884929040813926645760 }, { target := 709, numerator := 1723569318917763110094766080 }, { target := 710, numerator := 1477345130500939808652656640 }, { target := 711, numerator := 1723569318917763110094766080 }, { target := 712, numerator := 1723569318917763110094766080 }, { target := 713, numerator := 71454259478562122078500159488 }, { target := 714, numerator := 1772814156601127770383187968 }, { target := 715, numerator := 19451710884929040813926645760 }, { target := 716, numerator := 71454259478562122078500159488 }, { target := 717, numerator := 1526589968184304468941078528 }, { target := 718, numerator := 1723569318917763110094766080 }, { target := 719, numerator := 1772814156601127770383187968 }, { target := 720, numerator := 1723569318917763110094766080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3
