import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 29; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3

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
    Slot2.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 7325547948121445000806400 }, { target := 143, numerator := 1169503167562554031262924800 }, { target := 145, numerator := 11669882912376438314028236800 }, { target := 153, numerator := 1169503167562554031262924800 }, { target := 160, numerator := 7324712080030605036748800 }, { target := 282, numerator := 146803980880353757816160256 }, { target := 283, numerator := 23436843477953582786509012992 }, { target := 285, numerator := 233864453564023823813125865472 }, { target := 293, numerator := 23436843477953582786509012992 }, { target := 300, numerator := 146787230083813324936445952 }, { target := 357, numerator := 246431432974805409827127296 }, { target := 358, numerator := 39342086556804317611684790272 }, { target := 360, numerator := 392574861172343384883909885952 }, { target := 368, numerator := 39342086556804317611684790272 }, { target := 375, numerator := 246403314372229553436229632 }, { target := 392, numerator := 236468687765360244626030592 }, { target := 393, numerator := 37751562248919244129167212544 }, { target := 395, numerator := 376703820411511428776831483904 }, { target := 403, numerator := 37751562248919244129167212544 }, { target := 410, numerator := 236441705943387930586251264 }, { target := 411, numerator := 3755976701895462221229588480 }, { target := 413, numerator := 141121693520721698075558543360 }, { target := 416, numerator := 141111020188483789544719646720 }, { target := 423, numerator := 3766650034133370752068485120 }, { target := 498, numerator := 7325547948121445000806400 }, { target := 499, numerator := 1169503167562554031262924800 }, { target := 501, numerator := 11669882912376438314028236800 }, { target := 509, numerator := 1169503167562554031262924800 }, { target := 516, numerator := 7324712080030605036748800 }, { target := 573, numerator := 236468687765360244626030592 }, { target := 574, numerator := 37751562248919244129167212544 }, { target := 576, numerator := 376703820411511428776831483904 }, { target := 584, numerator := 37751562248919244129167212544 }, { target := 591, numerator := 236441705943387930586251264 }, { target := 608, numerator := 157938813761498354217385984 }, { target := 609, numerator := 25214488292648664914028658688 }, { target := 611, numerator := 251602675590836010050448785408 }, { target := 619, numerator := 25214488292648664914028658688 }, { target := 626, numerator := 157920792445459844592304128 }, { target := 627, numerator := 3433032910704450516226670592 }, { target := 629, numerator := 128987865666603570764389023744 }, { target := 632, numerator := 128978110041436585210033471488 }, { target := 639, numerator := 3442788535871436070582222848 }, { target := 669, numerator := 7618569866046302800838656 }, { target := 670, numerator := 1216283294265056192513441792 }, { target := 672, numerator := 12136678228871495846589366272 }, { target := 680, numerator := 1216283294265056192513441792 }, { target := 687, numerator := 7617700563231829238218752 }, { target := 704, numerator := 146803980880353757816160256 }, { target := 705, numerator := 23436843477953582786509012992 }, { target := 707, numerator := 233864453564023823813125865472 }, { target := 715, numerator := 23436843477953582786509012992 }, { target := 722, numerator := 146787230083813324936445952 }, { target := 723, numerator := 3755976701895462221229588480 }, { target := 725, numerator := 141121693520721698075558543360 }, { target := 728, numerator := 141111020188483789544719646720 }, { target := 735, numerator := 3766650034133370752068485120 }, { target := 758, numerator := 3433032910704450516226670592 }, { target := 760, numerator := 128987865666603570764389023744 }, { target := 763, numerator := 128978110041436585210033471488 }, { target := 770, numerator := 3442788535871436070582222848 }, { target := 774, numerator := 131249109447714678995870023680 }, { target := 777, numerator := 450555243732949680350155505664 }, { target := 779, numerator := 131249109447714678995870023680 }]

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
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 178505453052472589077708800 }, { target := 56, numerator := 138837574596367569282662400 }, { target := 57, numerator := 158671513824420079180185600 }, { target := 58, numerator := 186439028743693593036718080 }, { target := 59, numerator := 2201567254313828598625075200 }, { target := 60, numerator := 4950551231321906470421790720 }, { target := 61, numerator := 138837574596367569282662400 }, { target := 62, numerator := 2201567254313828598625075200 }, { target := 63, numerator := 158671513824420079180185600 }, { target := 64, numerator := 154704725978809577200680960 }, { target := 65, numerator := 154704725978809577200680960 }, { target := 66, numerator := 154704725978809577200680960 }, { target := 67, numerator := 4950551231321906470421790720 }, { target := 68, numerator := 154704725978809577200680960 }, { target := 69, numerator := 178505453052472589077708800 }, { target := 70, numerator := 186439028743693593036718080 }, { target := 100, numerator := 183605608853971805908500480 }, { target := 101, numerator := 142804362441978071262167040 }, { target := 102, numerator := 163204985647974938585333760 }, { target := 103, numerator := 191765858136370552837767168 }, { target := 104, numerator := 2264469175865652272871505920 }, { target := 105, numerator := 5091995552216818083862413312 }, { target := 106, numerator := 142804362441978071262167040 }, { target := 107, numerator := 2264469175865652272871505920 }, { target := 108, numerator := 163204985647974938585333760 }, { target := 109, numerator := 159124861006775565120700416 }, { target := 110, numerator := 159124861006775565120700416 }, { target := 111, numerator := 159124861006775565120700416 }, { target := 112, numerator := 5091995552216818083862413312 }, { target := 113, numerator := 159124861006775565120700416 }, { target := 114, numerator := 183605608853971805908500480 }, { target := 115, numerator := 191765858136370552837767168 }, { target := 126, numerator := 178505453052472589077708800 }, { target := 127, numerator := 138837574596367569282662400 }, { target := 128, numerator := 158671513824420079180185600 }, { target := 129, numerator := 186439028743693593036718080 }, { target := 130, numerator := 2201567254313828598625075200 }, { target := 131, numerator := 4950551231321906470421790720 }, { target := 132, numerator := 138837574596367569282662400 }, { target := 133, numerator := 2201567254313828598625075200 }, { target := 134, numerator := 158671513824420079180185600 }, { target := 135, numerator := 154704725978809577200680960 }, { target := 136, numerator := 154704725978809577200680960 }, { target := 137, numerator := 154704725978809577200680960 }, { target := 138, numerator := 4950551231321906470421790720 }, { target := 139, numerator := 154704725978809577200680960 }, { target := 140, numerator := 178505453052472589077708800 }, { target := 141, numerator := 186439028743693593036718080 }, { target := 739, numerator := 7032526030196587200774144 }, { target := 740, numerator := 1122723040860051870012407808 }, { target := 742, numerator := 11203087595881380781467107328 }, { target := 750, numerator := 1122723040860051870012407808 }, { target := 757, numerator := 7031723596829380835278848 }]

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
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 195, numerator := 158104829846475721754542080 }, { target := 196, numerator := 122970423213925561364643840 }, { target := 197, numerator := 140537626530200641559592960 }, { target := 198, numerator := 165131711172985753832521728 }, { target := 199, numerator := 1949959568106533901639352320 }, { target := 200, numerator := 4384773947742260016659300352 }, { target := 201, numerator := 122970423213925561364643840 }, { target := 202, numerator := 1949959568106533901639352320 }, { target := 203, numerator := 140537626530200641559592960 }, { target := 204, numerator := 137024185866945625520603136 }, { target := 205, numerator := 137024185866945625520603136 }, { target := 206, numerator := 137024185866945625520603136 }, { target := 207, numerator := 4384773947742260016659300352 }, { target := 208, numerator := 137024185866945625520603136 }, { target := 209, numerator := 158104829846475721754542080 }, { target := 210, numerator := 165131711172985753832521728 }, { target := 240, numerator := 7400326067975363621478727680 }, { target := 241, numerator := 5755809163980838372261232640 }, { target := 242, numerator := 6578067615978100996869980160 }, { target := 243, numerator := 7729229448774268671322226688 }, { target := 244, numerator := 91270688171696151331570974720 }, { target := 245, numerator := 205235709618516751102343380992 }, { target := 246, numerator := 5755809163980838372261232640 }, { target := 247, numerator := 91270688171696151331570974720 }, { target := 248, numerator := 6578067615978100996869980160 }, { target := 249, numerator := 6413615925578648471948230656 }, { target := 250, numerator := 6413615925578648471948230656 }, { target := 251, numerator := 6413615925578648471948230656 }, { target := 252, numerator := 205235709618516751102343380992 }, { target := 253, numerator := 6413615925578648471948230656 }, { target := 254, numerator := 7400326067975363621478727680 }, { target := 255, numerator := 7729229448774268671322226688 }, { target := 266, numerator := 2014561541592190648162713600 }, { target := 267, numerator := 1566881199016148281904332800 }, { target := 268, numerator := 1790721370304169465033523200 }, { target := 269, numerator := 2104097610107399121414389760 }, { target := 270, numerator := 24846259012970351327340134400 }, { target := 271, numerator := 55870506753490087309045923840 }, { target := 272, numerator := 1566881199016148281904332800 }, { target := 273, numerator := 24846259012970351327340134400 }, { target := 274, numerator := 1790721370304169465033523200 }, { target := 275, numerator := 1745953336046565228407685120 }, { target := 276, numerator := 1745953336046565228407685120 }, { target := 277, numerator := 1745953336046565228407685120 }, { target := 278, numerator := 55870506753490087309045923840 }, { target := 279, numerator := 1745953336046565228407685120 }, { target := 280, numerator := 2014561541592190648162713600 }, { target := 281, numerator := 2104097610107399121414389760 }, { target := 315, numerator := 183605608853971805908500480 }, { target := 316, numerator := 142804362441978071262167040 }, { target := 317, numerator := 163204985647974938585333760 }, { target := 318, numerator := 191765858136370552837767168 }, { target := 319, numerator := 2264469175865652272871505920 }, { target := 320, numerator := 5091995552216818083862413312 }, { target := 321, numerator := 142804362441978071262167040 }, { target := 322, numerator := 2264469175865652272871505920 }, { target := 323, numerator := 163204985647974938585333760 }, { target := 324, numerator := 159124861006775565120700416 }, { target := 325, numerator := 159124861006775565120700416 }, { target := 326, numerator := 159124861006775565120700416 }, { target := 327, numerator := 5091995552216818083862413312 }, { target := 328, numerator := 159124861006775565120700416 }, { target := 329, numerator := 183605608853971805908500480 }, { target := 330, numerator := 191765858136370552837767168 }]

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
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 341, numerator := 7400326067975363621478727680 }, { target := 342, numerator := 5755809163980838372261232640 }, { target := 343, numerator := 6578067615978100996869980160 }, { target := 344, numerator := 7729229448774268671322226688 }, { target := 345, numerator := 91270688171696151331570974720 }, { target := 346, numerator := 205235709618516751102343380992 }, { target := 347, numerator := 5755809163980838372261232640 }, { target := 348, numerator := 91270688171696151331570974720 }, { target := 349, numerator := 6578067615978100996869980160 }, { target := 350, numerator := 6413615925578648471948230656 }, { target := 351, numerator := 6413615925578648471948230656 }, { target := 352, numerator := 6413615925578648471948230656 }, { target := 353, numerator := 205235709618516751102343380992 }, { target := 354, numerator := 6413615925578648471948230656 }, { target := 355, numerator := 7400326067975363621478727680 }, { target := 356, numerator := 7729229448774268671322226688 }, { target := 376, numerator := 178505453052472589077708800 }, { target := 377, numerator := 138837574596367569282662400 }, { target := 378, numerator := 158671513824420079180185600 }, { target := 379, numerator := 186439028743693593036718080 }, { target := 380, numerator := 2201567254313828598625075200 }, { target := 381, numerator := 4950551231321906470421790720 }, { target := 382, numerator := 138837574596367569282662400 }, { target := 383, numerator := 2201567254313828598625075200 }, { target := 384, numerator := 158671513824420079180185600 }, { target := 385, numerator := 154704725978809577200680960 }, { target := 386, numerator := 154704725978809577200680960 }, { target := 387, numerator := 154704725978809577200680960 }, { target := 388, numerator := 4950551231321906470421790720 }, { target := 389, numerator := 154704725978809577200680960 }, { target := 390, numerator := 178505453052472589077708800 }, { target := 391, numerator := 186439028743693593036718080 }, { target := 456, numerator := 178505453052472589077708800 }, { target := 457, numerator := 138837574596367569282662400 }, { target := 458, numerator := 158671513824420079180185600 }, { target := 459, numerator := 186439028743693593036718080 }, { target := 460, numerator := 2201567254313828598625075200 }, { target := 461, numerator := 4950551231321906470421790720 }, { target := 462, numerator := 138837574596367569282662400 }, { target := 463, numerator := 2201567254313828598625075200 }, { target := 464, numerator := 158671513824420079180185600 }, { target := 465, numerator := 154704725978809577200680960 }, { target := 466, numerator := 154704725978809577200680960 }, { target := 467, numerator := 154704725978809577200680960 }, { target := 468, numerator := 4950551231321906470421790720 }, { target := 469, numerator := 154704725978809577200680960 }, { target := 470, numerator := 178505453052472589077708800 }, { target := 471, numerator := 186439028743693593036718080 }, { target := 482, numerator := 153004674044976504923750400 }, { target := 483, numerator := 119003635368315059385139200 }, { target := 484, numerator := 136004154706645782154444800 }, { target := 485, numerator := 159804881780308794031472640 }, { target := 486, numerator := 1887057646554710227392921600 }, { target := 487, numerator := 4243329626847348403218677760 }, { target := 488, numerator := 119003635368315059385139200 }, { target := 489, numerator := 1887057646554710227392921600 }, { target := 490, numerator := 136004154706645782154444800 }, { target := 491, numerator := 132604050838979637600583680 }, { target := 492, numerator := 132604050838979637600583680 }, { target := 493, numerator := 132604050838979637600583680 }, { target := 494, numerator := 4243329626847348403218677760 }, { target := 495, numerator := 132604050838979637600583680 }, { target := 496, numerator := 153004674044976504923750400 }, { target := 497, numerator := 159804881780308794031472640 }]

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
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 531, numerator := 178505453052472589077708800 }, { target := 532, numerator := 138837574596367569282662400 }, { target := 533, numerator := 158671513824420079180185600 }, { target := 534, numerator := 186439028743693593036718080 }, { target := 535, numerator := 2201567254313828598625075200 }, { target := 536, numerator := 4950551231321906470421790720 }, { target := 537, numerator := 138837574596367569282662400 }, { target := 538, numerator := 2201567254313828598625075200 }, { target := 539, numerator := 158671513824420079180185600 }, { target := 540, numerator := 154704725978809577200680960 }, { target := 541, numerator := 154704725978809577200680960 }, { target := 542, numerator := 154704725978809577200680960 }, { target := 543, numerator := 4950551231321906470421790720 }, { target := 544, numerator := 154704725978809577200680960 }, { target := 545, numerator := 178505453052472589077708800 }, { target := 546, numerator := 186439028743693593036718080 }, { target := 557, numerator := 2014561541592190648162713600 }, { target := 558, numerator := 1566881199016148281904332800 }, { target := 559, numerator := 1790721370304169465033523200 }, { target := 560, numerator := 2104097610107399121414389760 }, { target := 561, numerator := 24846259012970351327340134400 }, { target := 562, numerator := 55870506753490087309045923840 }, { target := 563, numerator := 1566881199016148281904332800 }, { target := 564, numerator := 24846259012970351327340134400 }, { target := 565, numerator := 1790721370304169465033523200 }, { target := 566, numerator := 1745953336046565228407685120 }, { target := 567, numerator := 1745953336046565228407685120 }, { target := 568, numerator := 1745953336046565228407685120 }, { target := 569, numerator := 55870506753490087309045923840 }, { target := 570, numerator := 1745953336046565228407685120 }, { target := 571, numerator := 2014561541592190648162713600 }, { target := 572, numerator := 2104097610107399121414389760 }, { target := 592, numerator := 153004674044976504923750400 }, { target := 593, numerator := 119003635368315059385139200 }, { target := 594, numerator := 136004154706645782154444800 }, { target := 595, numerator := 159804881780308794031472640 }, { target := 596, numerator := 1887057646554710227392921600 }, { target := 597, numerator := 4243329626847348403218677760 }, { target := 598, numerator := 119003635368315059385139200 }, { target := 599, numerator := 1887057646554710227392921600 }, { target := 600, numerator := 136004154706645782154444800 }, { target := 601, numerator := 132604050838979637600583680 }, { target := 602, numerator := 132604050838979637600583680 }, { target := 603, numerator := 132604050838979637600583680 }, { target := 604, numerator := 4243329626847348403218677760 }, { target := 605, numerator := 132604050838979637600583680 }, { target := 606, numerator := 153004674044976504923750400 }, { target := 607, numerator := 159804881780308794031472640 }, { target := 653, numerator := 178505453052472589077708800 }, { target := 654, numerator := 138837574596367569282662400 }, { target := 655, numerator := 158671513824420079180185600 }, { target := 656, numerator := 186439028743693593036718080 }, { target := 657, numerator := 2201567254313828598625075200 }, { target := 658, numerator := 4950551231321906470421790720 }, { target := 659, numerator := 138837574596367569282662400 }, { target := 660, numerator := 2201567254313828598625075200 }, { target := 661, numerator := 158671513824420079180185600 }, { target := 662, numerator := 154704725978809577200680960 }, { target := 663, numerator := 154704725978809577200680960 }, { target := 664, numerator := 154704725978809577200680960 }, { target := 665, numerator := 4950551231321906470421790720 }, { target := 666, numerator := 154704725978809577200680960 }, { target := 667, numerator := 178505453052472589077708800 }, { target := 668, numerator := 186439028743693593036718080 }]

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
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 315943922992683846677299200 }, { target := 56, numerator := 26567484961106596555286118400 }, { target := 61, numerator := 26567478551597680630431744000 }, { target := 69, numerator := 315950332501599771531673600 }, { target := 100, numerator := 26453711346618059627975147520 }, { target := 101, numerator := 2224472532054382365784450007040 }, { target := 106, numerator := 2224471995391745751700104806400 }, { target := 114, numerator := 26454248009254673712320348160 }, { target := 142, numerator := 217773037458852737055719424 }, { target := 143, numerator := 32163937983976410314056925184 }, { target := 145, numerator := 335239346560508440590900264960 }, { target := 153, numerator := 32163937983976410314056925184 }, { target := 160, numerator := 217773037458852737055719424 }, { target := 315, numerator := 26453720920192818256847831040 }, { target := 316, numerator := 2224473337089025902169376686080 }, { target := 321, numerator := 2224472800426195070351101132800 }, { target := 329, numerator := 26454257583023650075123384320 }, { target := 357, numerator := 2109365556899643549420617728 }, { target := 358, numerator := 311542254033514641174139240448 }, { target := 360, numerator := 3247152811954009415185722245120 }, { target := 368, numerator := 311542254033514641174139240448 }, { target := 375, numerator := 2109365556899643549420617728 }, { target := 411, numerator := 3191224153395854406768918528 }, { target := 413, numerator := 115651019618000651983547006976 }, { target := 416, numerator := 115651062119298997810353930240 }, { target := 423, numerator := 3191181652097508579961995264 }, { target := 627, numerator := 3191224153395854406768918528 }, { target := 629, numerator := 115651019618000651983547006976 }, { target := 632, numerator := 115651062119298997810353930240 }, { target := 639, numerator := 3191181652097508579961995264 }, { target := 653, numerator := 315934349417925217804615680 }, { target := 654, numerator := 26566679926463060170359439360 }, { target := 659, numerator := 26566673517148361979435417600 }, { target := 667, numerator := 315940758732623408728637440 }, { target := 669, numerator := 217773037458852737055719424 }, { target := 670, numerator := 32163937983976410314056925184 }, { target := 672, numerator := 335239346560508440590900264960 }, { target := 680, numerator := 32163937983976410314056925184 }, { target := 687, numerator := 217773037458852737055719424 }, { target := 688, numerator := 158104829846475721754542080 }, { target := 689, numerator := 122970423213925561364643840 }, { target := 690, numerator := 140537626530200641559592960 }, { target := 691, numerator := 165131711172985753832521728 }, { target := 692, numerator := 1949959568106533901639352320 }, { target := 693, numerator := 4384773947742260016659300352 }, { target := 694, numerator := 122970423213925561364643840 }, { target := 695, numerator := 1949959568106533901639352320 }, { target := 696, numerator := 140537626530200641559592960 }, { target := 697, numerator := 137024185866945625520603136 }, { target := 698, numerator := 137024185866945625520603136 }, { target := 699, numerator := 137024185866945625520603136 }, { target := 700, numerator := 4384773947742260016659300352 }, { target := 701, numerator := 137024185866945625520603136 }, { target := 702, numerator := 158104829846475721754542080 }, { target := 703, numerator := 165131711172985753832521728 }, { target := 723, numerator := 3191224153395854406768918528 }, { target := 725, numerator := 115651019618000651983547006976 }, { target := 728, numerator := 115651062119298997810353930240 }, { target := 735, numerator := 3191181652097508579961995264 }, { target := 758, numerator := 3191224153395854406768918528 }, { target := 760, numerator := 115651019618000651983547006976 }, { target := 763, numerator := 115651062119298997810353930240 }, { target := 770, numerator := 3191181652097508579961995264 }]

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
  [{ target := 11, numerator := 12065336227847204279156736 }, { target := 12, numerator := 288789660679439534681751552 }, { target := 13, numerator := 216008438917909624997806080 }, { target := 14, numerator := 250647630023664501799256064 }, { target := 15, numerator := 12065336227847204279156736 }, { target := 16, numerator := 250258425629217817790251008 }, { target := 17, numerator := 251426038812557869817266176 }, { target := 18, numerator := 12065336227847204279156736 }, { target := 19, numerator := 288789660679439534681751552 }, { target := 20, numerator := 12065336227847204279156736 }, { target := 31, numerator := 1265028742845778892427362304 }, { target := 32, numerator := 30279075070695739941325897728 }, { target := 33, numerator := 22648095234819589848296325120 }, { target := 34, numerator := 26279951948151019571716816896 }, { target := 35, numerator := 1265028742845778892427362304 }, { target := 36, numerator := 26239144569349542833251418112 }, { target := 37, numerator := 26361566705753973048647614464 }, { target := 38, numerator := 1265028742845778892427362304 }, { target := 39, numerator := 30279075070695739941325897728 }, { target := 40, numerator := 1265028742845778892427362304 }, { target := 76, numerator := 13635745453136562358321152000 }, { target := 77, numerator := 326378165362171911931428864000 }, { target := 78, numerator := 244123829886799745447362560000 }, { target := 79, numerator := 283271615219998263185768448000 }, { target := 80, numerator := 13635745453136562358321152000 }, { target := 81, numerator := 282831752463445470851629056000 }, { target := 82, numerator := 284151340733103847854047232000 }, { target := 83, numerator := 13635745453136562358321152000 }, { target := 84, numerator := 326378165362171911931428864000 }, { target := 85, numerator := 13635745453136562358321152000 }, { target := 142, numerator := 12065336227847204279156736 }, { target := 143, numerator := 1265028742845778892427362304 }, { target := 145, numerator := 13635745453136562358321152000 }, { target := 153, numerator := 1265029707841078248358281216 }, { target := 160, numerator := 12065336227847204279156736 }, { target := 282, numerator := 288789660679439534681751552 }, { target := 283, numerator := 30279075070695739941325897728 }, { target := 285, numerator := 326378165362171911931428864000 }, { target := 293, numerator := 30279098168325163234898214912 }, { target := 300, numerator := 288789660679439534681751552 }, { target := 305, numerator := 1265029707841078248358281216 }, { target := 306, numerator := 30279098168325163234898214912 }, { target := 307, numerator := 22648112511348336381898260480 }, { target := 308, numerator := 26279971995150141675572035584 }, { target := 309, numerator := 1265029707841078248358281216 }, { target := 310, numerator := 26239164585219784312721768448 }, { target := 311, numerator := 26361586815010856401272569856 }, { target := 312, numerator := 1265029707841078248358281216 }, { target := 313, numerator := 30279098168325163234898214912 }, { target := 314, numerator := 1265029707841078248358281216 }, { target := 643, numerator := 12065336227847204279156736 }, { target := 644, numerator := 288789660679439534681751552 }, { target := 645, numerator := 216008438917909624997806080 }, { target := 646, numerator := 250647630023664501799256064 }, { target := 647, numerator := 12065336227847204279156736 }, { target := 648, numerator := 250258425629217817790251008 }, { target := 649, numerator := 251426038812557869817266176 }, { target := 650, numerator := 12065336227847204279156736 }, { target := 651, numerator := 288789660679439534681751552 }, { target := 652, numerator := 12065336227847204279156736 }]

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
    Slot10.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 221464105890358715649884160 }, { target := 13, numerator := 2145117515491162931614187520 }, { target := 18, numerator := 221464105890358715649884160 }, { target := 31, numerator := 32709089475230247777007042560 }, { target := 33, numerator := 316822631220523363905904312320 }, { target := 38, numerator := 32709089475230247777007042560 }, { target := 55, numerator := 313196584531877900184453120 }, { target := 56, numerator := 26223679074038772152949276672 }, { target := 61, numerator := 26223688564365054619831762944 }, { target := 69, numerator := 313187094205595433301966848 }, { target := 100, numerator := 26336463352749147889587978240 }, { target := 101, numerator := 2205129292645213823473280876544 }, { target := 106, numerator := 2205130090679556111715729932288 }, { target := 114, numerator := 26335665318406859647138922496 }, { target := 315, numerator := 26336456998975092103210598400 }, { target := 316, numerator := 2205128760649208832120103895040 }, { target := 321, numerator := 2205129558683358591478482862080 }, { target := 329, numerator := 26335658964825332744831631360 }, { target := 357, numerator := 216008438917909624997806080 }, { target := 358, numerator := 22648095234819589848296325120 }, { target := 360, numerator := 244123829886799745447362560000 }, { target := 368, numerator := 22648112511348336381898260480 }, { target := 375, numerator := 216008438917909624997806080 }, { target := 392, numerator := 250647630023664501799256064 }, { target := 393, numerator := 26279951948151019571716816896 }, { target := 395, numerator := 283271615219998263185768448000 }, { target := 403, numerator := 26279971995150141675572035584 }, { target := 410, numerator := 250647630023664501799256064 }, { target := 498, numerator := 12065336227847204279156736 }, { target := 499, numerator := 1265028742845778892427362304 }, { target := 501, numerator := 13635745453136562358321152000 }, { target := 509, numerator := 1265029707841078248358281216 }, { target := 516, numerator := 12065336227847204279156736 }, { target := 573, numerator := 250258425629217817790251008 }, { target := 574, numerator := 26239144569349542833251418112 }, { target := 576, numerator := 282831752463445470851629056000 }, { target := 584, numerator := 26239164585219784312721768448 }, { target := 591, numerator := 250258425629217817790251008 }, { target := 608, numerator := 251426038812557869817266176 }, { target := 609, numerator := 26361566705753973048647614464 }, { target := 611, numerator := 284151340733103847854047232000 }, { target := 619, numerator := 26361586815010856401272569856 }, { target := 626, numerator := 251426038812557869817266176 }, { target := 653, numerator := 313202938305933686561832960 }, { target := 654, numerator := 26224211070043763506126258176 }, { target := 659, numerator := 26224220560562574857078833152 }, { target := 667, numerator := 313193447787122335609257984 }, { target := 669, numerator := 12065336227847204279156736 }, { target := 670, numerator := 1265028742845778892427362304 }, { target := 672, numerator := 13635745453136562358321152000 }, { target := 680, numerator := 1265029707841078248358281216 }, { target := 687, numerator := 12065336227847204279156736 }, { target := 704, numerator := 288789660679439534681751552 }, { target := 705, numerator := 30279075070695739941325897728 }, { target := 707, numerator := 326378165362171911931428864000 }, { target := 715, numerator := 30279098168325163234898214912 }, { target := 722, numerator := 288789660679439534681751552 }, { target := 739, numerator := 12065336227847204279156736 }, { target := 740, numerator := 1265028742845778892427362304 }, { target := 742, numerator := 13635745453136562358321152000 }, { target := 750, numerator := 1265029707841078248358281216 }, { target := 757, numerator := 12065336227847204279156736 }]

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
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 3191224153395854406768918528 }, { target := 3, numerator := 3191224153395854406768918528 }, { target := 4, numerator := 3191224153395854406768918528 }, { target := 5, numerator := 3191224153395854406768918528 }, { target := 22, numerator := 115651019618000651983547006976 }, { target := 23, numerator := 115651019618000651983547006976 }, { target := 24, numerator := 115651019618000651983547006976 }, { target := 25, numerator := 115651019618000651983547006976 }, { target := 55, numerator := 178505453052472589077708800 }, { target := 56, numerator := 183605608853971805908500480 }, { target := 57, numerator := 178505453052472589077708800 }, { target := 58, numerator := 158104829846475721754542080 }, { target := 59, numerator := 7400326067975363621478727680 }, { target := 60, numerator := 2014561541592190648162713600 }, { target := 61, numerator := 183605608853971805908500480 }, { target := 62, numerator := 7400326067975363621478727680 }, { target := 63, numerator := 178505453052472589077708800 }, { target := 64, numerator := 178505453052472589077708800 }, { target := 65, numerator := 153004674044976504923750400 }, { target := 66, numerator := 178505453052472589077708800 }, { target := 67, numerator := 2014561541592190648162713600 }, { target := 68, numerator := 153004674044976504923750400 }, { target := 69, numerator := 178505453052472589077708800 }, { target := 70, numerator := 158104829846475721754542080 }, { target := 72, numerator := 115651062119298997810353930240 }, { target := 73, numerator := 115651062119298997810353930240 }, { target := 74, numerator := 115651062119298997810353930240 }, { target := 75, numerator := 115651062119298997810353930240 }, { target := 76, numerator := 340921369383567905685661286400 }, { target := 78, numerator := 3302189300292212964595649740800 }, { target := 83, numerator := 340921369383567905685661286400 }, { target := 100, numerator := 138837574596367569282662400 }, { target := 101, numerator := 142804362441978071262167040 }, { target := 102, numerator := 138837574596367569282662400 }, { target := 103, numerator := 122970423213925561364643840 }, { target := 104, numerator := 5755809163980838372261232640 }, { target := 105, numerator := 1566881199016148281904332800 }, { target := 106, numerator := 142804362441978071262167040 }, { target := 107, numerator := 5755809163980838372261232640 }, { target := 108, numerator := 138837574596367569282662400 }, { target := 109, numerator := 138837574596367569282662400 }, { target := 110, numerator := 119003635368315059385139200 }, { target := 111, numerator := 138837574596367569282662400 }, { target := 112, numerator := 1566881199016148281904332800 }, { target := 113, numerator := 119003635368315059385139200 }, { target := 114, numerator := 138837574596367569282662400 }, { target := 115, numerator := 122970423213925561364643840 }, { target := 301, numerator := 3191181652097508579961995264 }, { target := 302, numerator := 3191181652097508579961995264 }, { target := 303, numerator := 3191181652097508579961995264 }, { target := 304, numerator := 3191181652097508579961995264 }, { target := 305, numerator := 32709089475230247777007042560 }, { target := 307, numerator := 316822631220523363905904312320 }, { target := 312, numerator := 32709089475230247777007042560 }, { target := 643, numerator := 221464105890358715649884160 }, { target := 645, numerator := 2145117515491162931614187520 }, { target := 650, numerator := 221464105890358715649884160 }]

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
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 126, numerator := 158671513824420079180185600 }, { target := 127, numerator := 163204985647974938585333760 }, { target := 128, numerator := 158671513824420079180185600 }, { target := 129, numerator := 140537626530200641559592960 }, { target := 130, numerator := 6578067615978100996869980160 }, { target := 131, numerator := 1790721370304169465033523200 }, { target := 132, numerator := 163204985647974938585333760 }, { target := 133, numerator := 6578067615978100996869980160 }, { target := 134, numerator := 158671513824420079180185600 }, { target := 135, numerator := 158671513824420079180185600 }, { target := 136, numerator := 136004154706645782154444800 }, { target := 137, numerator := 158671513824420079180185600 }, { target := 138, numerator := 1790721370304169465033523200 }, { target := 139, numerator := 136004154706645782154444800 }, { target := 140, numerator := 158671513824420079180185600 }, { target := 141, numerator := 140537626530200641559592960 }, { target := 195, numerator := 186439028743693593036718080 }, { target := 196, numerator := 191765858136370552837767168 }, { target := 197, numerator := 186439028743693593036718080 }, { target := 198, numerator := 165131711172985753832521728 }, { target := 199, numerator := 7729229448774268671322226688 }, { target := 200, numerator := 2104097610107399121414389760 }, { target := 201, numerator := 191765858136370552837767168 }, { target := 202, numerator := 7729229448774268671322226688 }, { target := 203, numerator := 186439028743693593036718080 }, { target := 204, numerator := 186439028743693593036718080 }, { target := 205, numerator := 159804881780308794031472640 }, { target := 206, numerator := 186439028743693593036718080 }, { target := 207, numerator := 2104097610107399121414389760 }, { target := 208, numerator := 159804881780308794031472640 }, { target := 209, numerator := 186439028743693593036718080 }, { target := 210, numerator := 165131711172985753832521728 }, { target := 240, numerator := 2201567254313828598625075200 }, { target := 241, numerator := 2264469175865652272871505920 }, { target := 242, numerator := 2201567254313828598625075200 }, { target := 243, numerator := 1949959568106533901639352320 }, { target := 244, numerator := 91270688171696151331570974720 }, { target := 245, numerator := 24846259012970351327340134400 }, { target := 246, numerator := 2264469175865652272871505920 }, { target := 247, numerator := 91270688171696151331570974720 }, { target := 248, numerator := 2201567254313828598625075200 }, { target := 249, numerator := 2201567254313828598625075200 }, { target := 250, numerator := 1887057646554710227392921600 }, { target := 251, numerator := 2201567254313828598625075200 }, { target := 252, numerator := 24846259012970351327340134400 }, { target := 253, numerator := 1887057646554710227392921600 }, { target := 254, numerator := 2201567254313828598625075200 }, { target := 255, numerator := 1949959568106533901639352320 }, { target := 266, numerator := 4950551231321906470421790720 }, { target := 267, numerator := 5091995552216818083862413312 }, { target := 268, numerator := 4950551231321906470421790720 }, { target := 269, numerator := 4384773947742260016659300352 }, { target := 270, numerator := 205235709618516751102343380992 }, { target := 271, numerator := 55870506753490087309045923840 }, { target := 272, numerator := 5091995552216818083862413312 }, { target := 273, numerator := 205235709618516751102343380992 }, { target := 274, numerator := 4950551231321906470421790720 }, { target := 275, numerator := 4950551231321906470421790720 }, { target := 276, numerator := 4243329626847348403218677760 }, { target := 277, numerator := 4950551231321906470421790720 }, { target := 278, numerator := 55870506753490087309045923840 }, { target := 279, numerator := 4243329626847348403218677760 }, { target := 280, numerator := 4950551231321906470421790720 }, { target := 281, numerator := 4384773947742260016659300352 }]

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
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 315, numerator := 138837574596367569282662400 }, { target := 316, numerator := 142804362441978071262167040 }, { target := 317, numerator := 138837574596367569282662400 }, { target := 318, numerator := 122970423213925561364643840 }, { target := 319, numerator := 5755809163980838372261232640 }, { target := 320, numerator := 1566881199016148281904332800 }, { target := 321, numerator := 142804362441978071262167040 }, { target := 322, numerator := 5755809163980838372261232640 }, { target := 323, numerator := 138837574596367569282662400 }, { target := 324, numerator := 138837574596367569282662400 }, { target := 325, numerator := 119003635368315059385139200 }, { target := 326, numerator := 138837574596367569282662400 }, { target := 327, numerator := 1566881199016148281904332800 }, { target := 328, numerator := 119003635368315059385139200 }, { target := 329, numerator := 138837574596367569282662400 }, { target := 330, numerator := 122970423213925561364643840 }, { target := 341, numerator := 2201567254313828598625075200 }, { target := 342, numerator := 2264469175865652272871505920 }, { target := 343, numerator := 2201567254313828598625075200 }, { target := 344, numerator := 1949959568106533901639352320 }, { target := 345, numerator := 91270688171696151331570974720 }, { target := 346, numerator := 24846259012970351327340134400 }, { target := 347, numerator := 2264469175865652272871505920 }, { target := 348, numerator := 91270688171696151331570974720 }, { target := 349, numerator := 2201567254313828598625075200 }, { target := 350, numerator := 2201567254313828598625075200 }, { target := 351, numerator := 1887057646554710227392921600 }, { target := 352, numerator := 2201567254313828598625075200 }, { target := 353, numerator := 24846259012970351327340134400 }, { target := 354, numerator := 1887057646554710227392921600 }, { target := 355, numerator := 2201567254313828598625075200 }, { target := 356, numerator := 1949959568106533901639352320 }, { target := 376, numerator := 158671513824420079180185600 }, { target := 377, numerator := 163204985647974938585333760 }, { target := 378, numerator := 158671513824420079180185600 }, { target := 379, numerator := 140537626530200641559592960 }, { target := 380, numerator := 6578067615978100996869980160 }, { target := 381, numerator := 1790721370304169465033523200 }, { target := 382, numerator := 163204985647974938585333760 }, { target := 383, numerator := 6578067615978100996869980160 }, { target := 384, numerator := 158671513824420079180185600 }, { target := 385, numerator := 158671513824420079180185600 }, { target := 386, numerator := 136004154706645782154444800 }, { target := 387, numerator := 158671513824420079180185600 }, { target := 388, numerator := 1790721370304169465033523200 }, { target := 389, numerator := 136004154706645782154444800 }, { target := 390, numerator := 158671513824420079180185600 }, { target := 391, numerator := 140537626530200641559592960 }, { target := 456, numerator := 154704725978809577200680960 }, { target := 457, numerator := 159124861006775565120700416 }, { target := 458, numerator := 154704725978809577200680960 }, { target := 459, numerator := 137024185866945625520603136 }, { target := 460, numerator := 6413615925578648471948230656 }, { target := 461, numerator := 1745953336046565228407685120 }, { target := 462, numerator := 159124861006775565120700416 }, { target := 463, numerator := 6413615925578648471948230656 }, { target := 464, numerator := 154704725978809577200680960 }, { target := 465, numerator := 154704725978809577200680960 }, { target := 466, numerator := 132604050838979637600583680 }, { target := 467, numerator := 154704725978809577200680960 }, { target := 468, numerator := 1745953336046565228407685120 }, { target := 469, numerator := 132604050838979637600583680 }, { target := 470, numerator := 154704725978809577200680960 }, { target := 471, numerator := 137024185866945625520603136 }]

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
    Slot12.Left10.expected,
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 482, numerator := 154704725978809577200680960 }, { target := 483, numerator := 159124861006775565120700416 }, { target := 484, numerator := 154704725978809577200680960 }, { target := 485, numerator := 137024185866945625520603136 }, { target := 486, numerator := 6413615925578648471948230656 }, { target := 487, numerator := 1745953336046565228407685120 }, { target := 488, numerator := 159124861006775565120700416 }, { target := 489, numerator := 6413615925578648471948230656 }, { target := 490, numerator := 154704725978809577200680960 }, { target := 491, numerator := 154704725978809577200680960 }, { target := 492, numerator := 132604050838979637600583680 }, { target := 493, numerator := 154704725978809577200680960 }, { target := 494, numerator := 1745953336046565228407685120 }, { target := 495, numerator := 132604050838979637600583680 }, { target := 496, numerator := 154704725978809577200680960 }, { target := 497, numerator := 137024185866945625520603136 }, { target := 531, numerator := 154704725978809577200680960 }, { target := 532, numerator := 159124861006775565120700416 }, { target := 533, numerator := 154704725978809577200680960 }, { target := 534, numerator := 137024185866945625520603136 }, { target := 535, numerator := 6413615925578648471948230656 }, { target := 536, numerator := 1745953336046565228407685120 }, { target := 537, numerator := 159124861006775565120700416 }, { target := 538, numerator := 6413615925578648471948230656 }, { target := 539, numerator := 154704725978809577200680960 }, { target := 540, numerator := 154704725978809577200680960 }, { target := 541, numerator := 132604050838979637600583680 }, { target := 542, numerator := 154704725978809577200680960 }, { target := 543, numerator := 1745953336046565228407685120 }, { target := 544, numerator := 132604050838979637600583680 }, { target := 545, numerator := 154704725978809577200680960 }, { target := 546, numerator := 137024185866945625520603136 }, { target := 557, numerator := 4950551231321906470421790720 }, { target := 558, numerator := 5091995552216818083862413312 }, { target := 559, numerator := 4950551231321906470421790720 }, { target := 560, numerator := 4384773947742260016659300352 }, { target := 561, numerator := 205235709618516751102343380992 }, { target := 562, numerator := 55870506753490087309045923840 }, { target := 563, numerator := 5091995552216818083862413312 }, { target := 564, numerator := 205235709618516751102343380992 }, { target := 565, numerator := 4950551231321906470421790720 }, { target := 566, numerator := 4950551231321906470421790720 }, { target := 567, numerator := 4243329626847348403218677760 }, { target := 568, numerator := 4950551231321906470421790720 }, { target := 569, numerator := 55870506753490087309045923840 }, { target := 570, numerator := 4243329626847348403218677760 }, { target := 571, numerator := 4950551231321906470421790720 }, { target := 572, numerator := 4384773947742260016659300352 }, { target := 592, numerator := 154704725978809577200680960 }, { target := 593, numerator := 159124861006775565120700416 }, { target := 594, numerator := 154704725978809577200680960 }, { target := 595, numerator := 137024185866945625520603136 }, { target := 596, numerator := 6413615925578648471948230656 }, { target := 597, numerator := 1745953336046565228407685120 }, { target := 598, numerator := 159124861006775565120700416 }, { target := 599, numerator := 6413615925578648471948230656 }, { target := 600, numerator := 154704725978809577200680960 }, { target := 601, numerator := 154704725978809577200680960 }, { target := 602, numerator := 132604050838979637600583680 }, { target := 603, numerator := 154704725978809577200680960 }, { target := 604, numerator := 1745953336046565228407685120 }, { target := 605, numerator := 132604050838979637600583680 }, { target := 606, numerator := 154704725978809577200680960 }, { target := 607, numerator := 137024185866945625520603136 }]

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
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 7072942846462084828364800 }, { target := 12, numerator := 141741774643100179960430592 }, { target := 13, numerator := 237933797354984533626191872 }, { target := 14, numerator := 228314595083796098259615744 }, { target := 15, numerator := 7072942846462084828364800 }, { target := 16, numerator := 228314595083796098259615744 }, { target := 17, numerator := 152492647769722548899545088 }, { target := 18, numerator := 7355860560320568221499392 }, { target := 19, numerator := 141741774643100179960430592 }, { target := 20, numerator := 6790025132603601435230208 }, { target := 31, numerator := 1129175472129362512943513600 }, { target := 32, numerator := 22628676461472424759388012544 }, { target := 33, numerator := 37985462882431754935419797504 }, { target := 34, numerator := 36449784240335821917816619008 }, { target := 35, numerator := 1129175472129362512943513600 }, { target := 36, numerator := 36449784240335821917816619008 }, { target := 37, numerator := 24345023179109055779062153216 }, { target := 38, numerator := 1174342491014537013461254144 }, { target := 39, numerator := 22628676461472424759388012544 }, { target := 40, numerator := 1084008453244188012425773056 }, { target := 76, numerator := 11267473156777250785958297600 }, { target := 77, numerator := 225800162061816105750604283904 }, { target := 78, numerator := 379037796993986716439637131264 }, { target := 79, numerator := 363714033500769655370733846528 }, { target := 80, numerator := 11267473156777250785958297600 }, { target := 81, numerator := 363714033500769655370733846528 }, { target := 82, numerator := 242926721260117526945260896256 }, { target := 83, numerator := 11718172083048340817396629504 }, { target := 84, numerator := 225800162061816105750604283904 }, { target := 85, numerator := 10816774230506160754519965696 }, { target := 653, numerator := 178505453052472589077708800 }, { target := 654, numerator := 183605608853971805908500480 }, { target := 655, numerator := 178505453052472589077708800 }, { target := 656, numerator := 158104829846475721754542080 }, { target := 657, numerator := 7400326067975363621478727680 }, { target := 658, numerator := 2014561541592190648162713600 }, { target := 659, numerator := 183605608853971805908500480 }, { target := 660, numerator := 7400326067975363621478727680 }, { target := 661, numerator := 178505453052472589077708800 }, { target := 662, numerator := 178505453052472589077708800 }, { target := 663, numerator := 153004674044976504923750400 }, { target := 664, numerator := 178505453052472589077708800 }, { target := 665, numerator := 2014561541592190648162713600 }, { target := 666, numerator := 153004674044976504923750400 }, { target := 667, numerator := 178505453052472589077708800 }, { target := 668, numerator := 158104829846475721754542080 }, { target := 688, numerator := 186439028743693593036718080 }, { target := 689, numerator := 191765858136370552837767168 }, { target := 690, numerator := 186439028743693593036718080 }, { target := 691, numerator := 165131711172985753832521728 }, { target := 692, numerator := 7729229448774268671322226688 }, { target := 693, numerator := 2104097610107399121414389760 }, { target := 694, numerator := 191765858136370552837767168 }, { target := 695, numerator := 7729229448774268671322226688 }, { target := 696, numerator := 186439028743693593036718080 }, { target := 697, numerator := 186439028743693593036718080 }, { target := 698, numerator := 159804881780308794031472640 }, { target := 699, numerator := 186439028743693593036718080 }, { target := 700, numerator := 2104097610107399121414389760 }, { target := 701, numerator := 159804881780308794031472640 }, { target := 702, numerator := 186439028743693593036718080 }, { target := 703, numerator := 165131711172985753832521728 }]

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
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 131249109447714678995870023680 }, { target := 2, numerator := 3487692651760072062570332160 }, { target := 3, numerator := 3187816274225561193639051264 }, { target := 4, numerator := 3487692651760072062570332160 }, { target := 5, numerator := 3187816274225561193639051264 }, { target := 21, numerator := 450555243732949680350155505664 }, { target := 22, numerator := 131041572554955862498732933120 }, { target := 23, numerator := 119774446690417601424075522048 }, { target := 24, numerator := 131041572554955862498732933120 }, { target := 25, numerator := 119774446690417601424075522048 }, { target := 71, numerator := 131249109447714678995870023680 }, { target := 72, numerator := 131031661603592090291525386240 }, { target := 73, numerator := 119765387895619686266459652096 }, { target := 74, numerator := 131031661603592090291525386240 }, { target := 75, numerator := 119765387895619686266459652096 }, { target := 301, numerator := 3497603603123844269777879040 }, { target := 302, numerator := 3196875069023476351254921216 }, { target := 303, numerator := 3497603603123844269777879040 }, { target := 304, numerator := 3196875069023476351254921216 }, { target := 305, numerator := 1129175472129362512943513600 }, { target := 306, numerator := 22628676461472424759388012544 }, { target := 307, numerator := 37985462882431754935419797504 }, { target := 308, numerator := 36449784240335821917816619008 }, { target := 309, numerator := 1129175472129362512943513600 }, { target := 310, numerator := 36449784240335821917816619008 }, { target := 311, numerator := 24345023179109055779062153216 }, { target := 312, numerator := 1174342491014537013461254144 }, { target := 313, numerator := 22628676461472424759388012544 }, { target := 314, numerator := 1084008453244188012425773056 }, { target := 643, numerator := 7072135801408860035481600 }, { target := 644, numerator := 141725601460233555111051264 }, { target := 645, numerator := 237906648359394051593601024 }, { target := 646, numerator := 228288543669478001945346048 }, { target := 647, numerator := 7072135801408860035481600 }, { target := 648, numerator := 228288543669478001945346048 }, { target := 649, numerator := 152475247878375022364983296 }, { target := 650, numerator := 7355021233465214436900864 }, { target := 651, numerator := 141725601460233555111051264 }, { target := 652, numerator := 6789250369352505634062336 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3
