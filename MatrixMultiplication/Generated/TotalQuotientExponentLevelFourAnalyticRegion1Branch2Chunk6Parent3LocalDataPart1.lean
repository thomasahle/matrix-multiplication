import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 29; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 24, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 178505453052472589077708800 }, some { target := 56, numerator := 138837574596367569282662400 }, some { target := 57, numerator := 158671513824420079180185600 }, some { target := 58, numerator := 186439028743693593036718080 }, some { target := 59, numerator := 2201567254313828598625075200 }, some { target := 60, numerator := 4950551231321906470421790720 }, some { target := 61, numerator := 138837574596367569282662400 }, some { target := 62, numerator := 2201567254313828598625075200 }, some { target := 63, numerator := 158671513824420079180185600 }, some { target := 64, numerator := 154704725978809577200680960 }, some { target := 65, numerator := 154704725978809577200680960 }, some { target := 66, numerator := 154704725978809577200680960 }, some { target := 67, numerator := 4950551231321906470421790720 }, some { target := 68, numerator := 154704725978809577200680960 }, some { target := 69, numerator := 178505453052472589077708800 }, some { target := 70, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 183605608853971805908500480 }, some { target := 101, numerator := 142804362441978071262167040 }, some { target := 102, numerator := 163204985647974938585333760 }, some { target := 103, numerator := 191765858136370552837767168 }, some { target := 104, numerator := 2264469175865652272871505920 }, some { target := 105, numerator := 5091995552216818083862413312 }, some { target := 106, numerator := 142804362441978071262167040 }, some { target := 107, numerator := 2264469175865652272871505920 }, some { target := 108, numerator := 163204985647974938585333760 }, some { target := 109, numerator := 159124861006775565120700416 }, some { target := 110, numerator := 159124861006775565120700416 }, some { target := 111, numerator := 159124861006775565120700416 }, some { target := 112, numerator := 5091995552216818083862413312 }, some { target := 113, numerator := 159124861006775565120700416 }, some { target := 114, numerator := 183605608853971805908500480 }, some { target := 115, numerator := 191765858136370552837767168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 178505453052472589077708800 }, some { target := 127, numerator := 138837574596367569282662400 }, some { target := 128, numerator := 158671513824420079180185600 }, some { target := 129, numerator := 186439028743693593036718080 }, some { target := 130, numerator := 2201567254313828598625075200 }, some { target := 131, numerator := 4950551231321906470421790720 }, some { target := 132, numerator := 138837574596367569282662400 }, some { target := 133, numerator := 2201567254313828598625075200 }, some { target := 134, numerator := 158671513824420079180185600 }, some { target := 135, numerator := 154704725978809577200680960 }, some { target := 136, numerator := 154704725978809577200680960 }, some { target := 137, numerator := 154704725978809577200680960 }, some { target := 138, numerator := 4950551231321906470421790720 }, some { target := 139, numerator := 154704725978809577200680960 }, some { target := 140, numerator := 178505453052472589077708800 }, some { target := 141, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 158104829846475721754542080 }, some { target := 196, numerator := 122970423213925561364643840 }, some { target := 197, numerator := 140537626530200641559592960 }, some { target := 198, numerator := 165131711172985753832521728 }, some { target := 199, numerator := 1949959568106533901639352320 }, some { target := 200, numerator := 4384773947742260016659300352 }, some { target := 201, numerator := 122970423213925561364643840 }, some { target := 202, numerator := 1949959568106533901639352320 }, some { target := 203, numerator := 140537626530200641559592960 }, some { target := 204, numerator := 137024185866945625520603136 }, some { target := 205, numerator := 137024185866945625520603136 }, some { target := 206, numerator := 137024185866945625520603136 }, some { target := 207, numerator := 4384773947742260016659300352 }, some { target := 208, numerator := 137024185866945625520603136 }, some { target := 209, numerator := 158104829846475721754542080 }, some { target := 210, numerator := 165131711172985753832521728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 7400326067975363621478727680 }, some { target := 241, numerator := 5755809163980838372261232640 }, some { target := 242, numerator := 6578067615978100996869980160 }, some { target := 243, numerator := 7729229448774268671322226688 }, some { target := 244, numerator := 91270688171696151331570974720 }, some { target := 245, numerator := 205235709618516751102343380992 }, some { target := 246, numerator := 5755809163980838372261232640 }, some { target := 247, numerator := 91270688171696151331570974720 }, some { target := 248, numerator := 6578067615978100996869980160 }, some { target := 249, numerator := 6413615925578648471948230656 }, some { target := 250, numerator := 6413615925578648471948230656 }, some { target := 251, numerator := 6413615925578648471948230656 }, some { target := 252, numerator := 205235709618516751102343380992 }, some { target := 253, numerator := 6413615925578648471948230656 }, some { target := 254, numerator := 7400326067975363621478727680 }, some { target := 255, numerator := 7729229448774268671322226688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 2014561541592190648162713600 }, some { target := 267, numerator := 1566881199016148281904332800 }, some { target := 268, numerator := 1790721370304169465033523200 }, some { target := 269, numerator := 2104097610107399121414389760 }, some { target := 270, numerator := 24846259012970351327340134400 }, some { target := 271, numerator := 55870506753490087309045923840 }, some { target := 272, numerator := 1566881199016148281904332800 }, some { target := 273, numerator := 24846259012970351327340134400 }, some { target := 274, numerator := 1790721370304169465033523200 }, some { target := 275, numerator := 1745953336046565228407685120 }, some { target := 276, numerator := 1745953336046565228407685120 }, some { target := 277, numerator := 1745953336046565228407685120 }, some { target := 278, numerator := 55870506753490087309045923840 }, some { target := 279, numerator := 1745953336046565228407685120 }, some { target := 280, numerator := 2014561541592190648162713600 }, some { target := 281, numerator := 2104097610107399121414389760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 183605608853971805908500480 }, some { target := 316, numerator := 142804362441978071262167040 }, some { target := 317, numerator := 163204985647974938585333760 }, some { target := 318, numerator := 191765858136370552837767168 }, some { target := 319, numerator := 2264469175865652272871505920 }, some { target := 320, numerator := 5091995552216818083862413312 }, some { target := 321, numerator := 142804362441978071262167040 }, some { target := 322, numerator := 2264469175865652272871505920 }, some { target := 323, numerator := 163204985647974938585333760 }, some { target := 324, numerator := 159124861006775565120700416 }, some { target := 325, numerator := 159124861006775565120700416 }, some { target := 326, numerator := 159124861006775565120700416 }, some { target := 327, numerator := 5091995552216818083862413312 }, some { target := 328, numerator := 159124861006775565120700416 }, some { target := 329, numerator := 183605608853971805908500480 }, some { target := 330, numerator := 191765858136370552837767168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 7400326067975363621478727680 }, some { target := 342, numerator := 5755809163980838372261232640 }, some { target := 343, numerator := 6578067615978100996869980160 }, some { target := 344, numerator := 7729229448774268671322226688 }, some { target := 345, numerator := 91270688171696151331570974720 }, some { target := 346, numerator := 205235709618516751102343380992 }, some { target := 347, numerator := 5755809163980838372261232640 }, some { target := 348, numerator := 91270688171696151331570974720 }, some { target := 349, numerator := 6578067615978100996869980160 }, some { target := 350, numerator := 6413615925578648471948230656 }, some { target := 351, numerator := 6413615925578648471948230656 }, some { target := 352, numerator := 6413615925578648471948230656 }, some { target := 353, numerator := 205235709618516751102343380992 }, some { target := 354, numerator := 6413615925578648471948230656 }, some { target := 355, numerator := 7400326067975363621478727680 }, some { target := 356, numerator := 7729229448774268671322226688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 178505453052472589077708800 }, some { target := 377, numerator := 138837574596367569282662400 }, some { target := 378, numerator := 158671513824420079180185600 }, some { target := 379, numerator := 186439028743693593036718080 }, some { target := 380, numerator := 2201567254313828598625075200 }, some { target := 381, numerator := 4950551231321906470421790720 }, some { target := 382, numerator := 138837574596367569282662400 }, some { target := 383, numerator := 2201567254313828598625075200 }, some { target := 384, numerator := 158671513824420079180185600 }, some { target := 385, numerator := 154704725978809577200680960 }, some { target := 386, numerator := 154704725978809577200680960 }, some { target := 387, numerator := 154704725978809577200680960 }, some { target := 388, numerator := 4950551231321906470421790720 }, some { target := 389, numerator := 154704725978809577200680960 }, some { target := 390, numerator := 178505453052472589077708800 }, some { target := 391, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 178505453052472589077708800 }, some { target := 457, numerator := 138837574596367569282662400 }, some { target := 458, numerator := 158671513824420079180185600 }, some { target := 459, numerator := 186439028743693593036718080 }, some { target := 460, numerator := 2201567254313828598625075200 }, some { target := 461, numerator := 4950551231321906470421790720 }, some { target := 462, numerator := 138837574596367569282662400 }, some { target := 463, numerator := 2201567254313828598625075200 }, some { target := 464, numerator := 158671513824420079180185600 }, some { target := 465, numerator := 154704725978809577200680960 }, some { target := 466, numerator := 154704725978809577200680960 }, some { target := 467, numerator := 154704725978809577200680960 }, some { target := 468, numerator := 4950551231321906470421790720 }, some { target := 469, numerator := 154704725978809577200680960 }, some { target := 470, numerator := 178505453052472589077708800 }, some { target := 471, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 153004674044976504923750400 }, some { target := 483, numerator := 119003635368315059385139200 }, some { target := 484, numerator := 136004154706645782154444800 }, some { target := 485, numerator := 159804881780308794031472640 }, some { target := 486, numerator := 1887057646554710227392921600 }, some { target := 487, numerator := 4243329626847348403218677760 }, some { target := 488, numerator := 119003635368315059385139200 }, some { target := 489, numerator := 1887057646554710227392921600 }, some { target := 490, numerator := 136004154706645782154444800 }, some { target := 491, numerator := 132604050838979637600583680 }, some { target := 492, numerator := 132604050838979637600583680 }, some { target := 493, numerator := 132604050838979637600583680 }, some { target := 494, numerator := 4243329626847348403218677760 }, some { target := 495, numerator := 132604050838979637600583680 }, some { target := 496, numerator := 153004674044976504923750400 }, some { target := 497, numerator := 159804881780308794031472640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 178505453052472589077708800 }, some { target := 532, numerator := 138837574596367569282662400 }, some { target := 533, numerator := 158671513824420079180185600 }, some { target := 534, numerator := 186439028743693593036718080 }, some { target := 535, numerator := 2201567254313828598625075200 }, some { target := 536, numerator := 4950551231321906470421790720 }, some { target := 537, numerator := 138837574596367569282662400 }, some { target := 538, numerator := 2201567254313828598625075200 }, some { target := 539, numerator := 158671513824420079180185600 }, some { target := 540, numerator := 154704725978809577200680960 }, some { target := 541, numerator := 154704725978809577200680960 }, some { target := 542, numerator := 154704725978809577200680960 }, some { target := 543, numerator := 4950551231321906470421790720 }, some { target := 544, numerator := 154704725978809577200680960 }, some { target := 545, numerator := 178505453052472589077708800 }, some { target := 546, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 2014561541592190648162713600 }, some { target := 558, numerator := 1566881199016148281904332800 }, some { target := 559, numerator := 1790721370304169465033523200 }, some { target := 560, numerator := 2104097610107399121414389760 }, some { target := 561, numerator := 24846259012970351327340134400 }, some { target := 562, numerator := 55870506753490087309045923840 }, some { target := 563, numerator := 1566881199016148281904332800 }, some { target := 564, numerator := 24846259012970351327340134400 }, some { target := 565, numerator := 1790721370304169465033523200 }, some { target := 566, numerator := 1745953336046565228407685120 }, some { target := 567, numerator := 1745953336046565228407685120 }, some { target := 568, numerator := 1745953336046565228407685120 }, some { target := 569, numerator := 55870506753490087309045923840 }, some { target := 570, numerator := 1745953336046565228407685120 }, some { target := 571, numerator := 2014561541592190648162713600 }, some { target := 572, numerator := 2104097610107399121414389760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 153004674044976504923750400 }, some { target := 593, numerator := 119003635368315059385139200 }, some { target := 594, numerator := 136004154706645782154444800 }, some { target := 595, numerator := 159804881780308794031472640 }, some { target := 596, numerator := 1887057646554710227392921600 }, some { target := 597, numerator := 4243329626847348403218677760 }, some { target := 598, numerator := 119003635368315059385139200 }, some { target := 599, numerator := 1887057646554710227392921600 }, some { target := 600, numerator := 136004154706645782154444800 }, some { target := 601, numerator := 132604050838979637600583680 }, some { target := 602, numerator := 132604050838979637600583680 }, some { target := 603, numerator := 132604050838979637600583680 }, some { target := 604, numerator := 4243329626847348403218677760 }, some { target := 605, numerator := 132604050838979637600583680 }, some { target := 606, numerator := 153004674044976504923750400 }, some { target := 607, numerator := 159804881780308794031472640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 178505453052472589077708800 }, some { target := 654, numerator := 138837574596367569282662400 }, some { target := 655, numerator := 158671513824420079180185600 }, some { target := 656, numerator := 186439028743693593036718080 }, some { target := 657, numerator := 2201567254313828598625075200 }, some { target := 658, numerator := 4950551231321906470421790720 }, some { target := 659, numerator := 138837574596367569282662400 }, some { target := 660, numerator := 2201567254313828598625075200 }, some { target := 661, numerator := 158671513824420079180185600 }, some { target := 662, numerator := 154704725978809577200680960 }, some { target := 663, numerator := 154704725978809577200680960 }, some { target := 664, numerator := 154704725978809577200680960 }, some { target := 665, numerator := 4950551231321906470421790720 }, some { target := 666, numerator := 154704725978809577200680960 }, some { target := 667, numerator := 178505453052472589077708800 }, some { target := 668, numerator := 186439028743693593036718080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 158104829846475721754542080 }, some { target := 689, numerator := 122970423213925561364643840 }, some { target := 690, numerator := 140537626530200641559592960 }, some { target := 691, numerator := 165131711172985753832521728 }, some { target := 692, numerator := 1949959568106533901639352320 }, some { target := 693, numerator := 4384773947742260016659300352 }, some { target := 694, numerator := 122970423213925561364643840 }, some { target := 695, numerator := 1949959568106533901639352320 }, some { target := 696, numerator := 140537626530200641559592960 }, some { target := 697, numerator := 137024185866945625520603136 }, some { target := 698, numerator := 137024185866945625520603136 }, some { target := 699, numerator := 137024185866945625520603136 }, some { target := 700, numerator := 4384773947742260016659300352 }, some { target := 701, numerator := 137024185866945625520603136 }, some { target := 702, numerator := 158104829846475721754542080 }, some { target := 703, numerator := 165131711172985753832521728 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 12, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 411, numerator := 3191224153395854406768918528 }, some { target := 413, numerator := 115651019618000651983547006976 }, some { target := 416, numerator := 115651062119298997810353930240 }, some { target := 423, numerator := 3191181652097508579961995264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 3191224153395854406768918528 }, some { target := 629, numerator := 115651019618000651983547006976 }, some { target := 632, numerator := 115651062119298997810353930240 }, some { target := 639, numerator := 3191181652097508579961995264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 3191224153395854406768918528 }, some { target := 725, numerator := 115651019618000651983547006976 }, some { target := 728, numerator := 115651062119298997810353930240 }, some { target := 735, numerator := 3191181652097508579961995264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 3191224153395854406768918528 }, some { target := 760, numerator := 115651019618000651983547006976 }, some { target := 763, numerator := 115651062119298997810353930240 }, some { target := 770, numerator := 3191181652097508579961995264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 59, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 7]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

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
  [some { target := 142, numerator := 217773037458852737055719424 }, some { target := 143, numerator := 32163937983976410314056925184 }, some { target := 145, numerator := 335239346560508440590900264960 }, some { target := 153, numerator := 32163937983976410314056925184 }, some { target := 160, numerator := 217773037458852737055719424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 2109365556899643549420617728 }, some { target := 358, numerator := 311542254033514641174139240448 }, some { target := 360, numerator := 3247152811954009415185722245120 }, some { target := 368, numerator := 311542254033514641174139240448 }, some { target := 375, numerator := 2109365556899643549420617728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 217773037458852737055719424 }, some { target := 670, numerator := 32163937983976410314056925184 }, some { target := 672, numerator := 335239346560508440590900264960 }, some { target := 680, numerator := 32163937983976410314056925184 }, some { target := 687, numerator := 217773037458852737055719424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left7.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left7.routed_eq]
  rfl

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 115, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 6, 14]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 315943922992683846677299200 }, some { target := 56, numerator := 26567484961106596555286118400 }, some { target := 61, numerator := 26567478551597680630431744000 }, some { target := 69, numerator := 315950332501599771531673600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 26453711346618059627975147520 }, some { target := 101, numerator := 2224472532054382365784450007040 }, some { target := 106, numerator := 2224471995391745751700104806400 }, some { target := 114, numerator := 26454248009254673712320348160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 26453720920192818256847831040 }, some { target := 316, numerator := 2224473337089025902169376686080 }, some { target := 321, numerator := 2224472800426195070351101132800 }, some { target := 329, numerator := 26454257583023650075123384320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 315934349417925217804615680 }, some { target := 654, numerator := 26566679926463060170359439360 }, some { target := 659, numerator := 26566673517148361979435417600 }, some { target := 667, numerator := 315940758732623408728637440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left6.expected ++ Left14.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left6.routed_eq, Left14.routed_eq]
  rfl

end Slot6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3
