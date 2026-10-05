import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 29; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 12, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 3191224153395854406768918528 }, some { target := 3, numerator := 3191224153395854406768918528 }, some { target := 4, numerator := 3191224153395854406768918528 }, some { target := 5, numerator := 3191224153395854406768918528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 115651019618000651983547006976 }, some { target := 23, numerator := 115651019618000651983547006976 }, some { target := 24, numerator := 115651019618000651983547006976 }, some { target := 25, numerator := 115651019618000651983547006976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 115651062119298997810353930240 }, some { target := 73, numerator := 115651062119298997810353930240 }, some { target := 74, numerator := 115651062119298997810353930240 }, some { target := 75, numerator := 115651062119298997810353930240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 3191181652097508579961995264 }, some { target := 302, numerator := 3191181652097508579961995264 }, some { target := 303, numerator := 3191181652097508579961995264 }, some { target := 304, numerator := 3191181652097508579961995264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 24, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 178505453052472589077708800 }, some { target := 56, numerator := 183605608853971805908500480 }, some { target := 57, numerator := 178505453052472589077708800 }, some { target := 58, numerator := 158104829846475721754542080 }, some { target := 59, numerator := 7400326067975363621478727680 }, some { target := 60, numerator := 2014561541592190648162713600 }, some { target := 61, numerator := 183605608853971805908500480 }, some { target := 62, numerator := 7400326067975363621478727680 }, some { target := 63, numerator := 178505453052472589077708800 }, some { target := 64, numerator := 178505453052472589077708800 }, some { target := 65, numerator := 153004674044976504923750400 }, some { target := 66, numerator := 178505453052472589077708800 }, some { target := 67, numerator := 2014561541592190648162713600 }, some { target := 68, numerator := 153004674044976504923750400 }, some { target := 69, numerator := 178505453052472589077708800 }, some { target := 70, numerator := 158104829846475721754542080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 138837574596367569282662400 }, some { target := 101, numerator := 142804362441978071262167040 }, some { target := 102, numerator := 138837574596367569282662400 }, some { target := 103, numerator := 122970423213925561364643840 }, some { target := 104, numerator := 5755809163980838372261232640 }, some { target := 105, numerator := 1566881199016148281904332800 }, some { target := 106, numerator := 142804362441978071262167040 }, some { target := 107, numerator := 5755809163980838372261232640 }, some { target := 108, numerator := 138837574596367569282662400 }, some { target := 109, numerator := 138837574596367569282662400 }, some { target := 110, numerator := 119003635368315059385139200 }, some { target := 111, numerator := 138837574596367569282662400 }, some { target := 112, numerator := 1566881199016148281904332800 }, some { target := 113, numerator := 119003635368315059385139200 }, some { target := 114, numerator := 138837574596367569282662400 }, some { target := 115, numerator := 122970423213925561364643840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 158671513824420079180185600 }, some { target := 127, numerator := 163204985647974938585333760 }, some { target := 128, numerator := 158671513824420079180185600 }, some { target := 129, numerator := 140537626530200641559592960 }, some { target := 130, numerator := 6578067615978100996869980160 }, some { target := 131, numerator := 1790721370304169465033523200 }, some { target := 132, numerator := 163204985647974938585333760 }, some { target := 133, numerator := 6578067615978100996869980160 }, some { target := 134, numerator := 158671513824420079180185600 }, some { target := 135, numerator := 158671513824420079180185600 }, some { target := 136, numerator := 136004154706645782154444800 }, some { target := 137, numerator := 158671513824420079180185600 }, some { target := 138, numerator := 1790721370304169465033523200 }, some { target := 139, numerator := 136004154706645782154444800 }, some { target := 140, numerator := 158671513824420079180185600 }, some { target := 141, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 186439028743693593036718080 }, some { target := 196, numerator := 191765858136370552837767168 }, some { target := 197, numerator := 186439028743693593036718080 }, some { target := 198, numerator := 165131711172985753832521728 }, some { target := 199, numerator := 7729229448774268671322226688 }, some { target := 200, numerator := 2104097610107399121414389760 }, some { target := 201, numerator := 191765858136370552837767168 }, some { target := 202, numerator := 7729229448774268671322226688 }, some { target := 203, numerator := 186439028743693593036718080 }, some { target := 204, numerator := 186439028743693593036718080 }, some { target := 205, numerator := 159804881780308794031472640 }, some { target := 206, numerator := 186439028743693593036718080 }, some { target := 207, numerator := 2104097610107399121414389760 }, some { target := 208, numerator := 159804881780308794031472640 }, some { target := 209, numerator := 186439028743693593036718080 }, some { target := 210, numerator := 165131711172985753832521728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 2201567254313828598625075200 }, some { target := 241, numerator := 2264469175865652272871505920 }, some { target := 242, numerator := 2201567254313828598625075200 }, some { target := 243, numerator := 1949959568106533901639352320 }, some { target := 244, numerator := 91270688171696151331570974720 }, some { target := 245, numerator := 24846259012970351327340134400 }, some { target := 246, numerator := 2264469175865652272871505920 }, some { target := 247, numerator := 91270688171696151331570974720 }, some { target := 248, numerator := 2201567254313828598625075200 }, some { target := 249, numerator := 2201567254313828598625075200 }, some { target := 250, numerator := 1887057646554710227392921600 }, some { target := 251, numerator := 2201567254313828598625075200 }, some { target := 252, numerator := 24846259012970351327340134400 }, some { target := 253, numerator := 1887057646554710227392921600 }, some { target := 254, numerator := 2201567254313828598625075200 }, some { target := 255, numerator := 1949959568106533901639352320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 4950551231321906470421790720 }, some { target := 267, numerator := 5091995552216818083862413312 }, some { target := 268, numerator := 4950551231321906470421790720 }, some { target := 269, numerator := 4384773947742260016659300352 }, some { target := 270, numerator := 205235709618516751102343380992 }, some { target := 271, numerator := 55870506753490087309045923840 }, some { target := 272, numerator := 5091995552216818083862413312 }, some { target := 273, numerator := 205235709618516751102343380992 }, some { target := 274, numerator := 4950551231321906470421790720 }, some { target := 275, numerator := 4950551231321906470421790720 }, some { target := 276, numerator := 4243329626847348403218677760 }, some { target := 277, numerator := 4950551231321906470421790720 }, some { target := 278, numerator := 55870506753490087309045923840 }, some { target := 279, numerator := 4243329626847348403218677760 }, some { target := 280, numerator := 4950551231321906470421790720 }, some { target := 281, numerator := 4384773947742260016659300352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 138837574596367569282662400 }, some { target := 316, numerator := 142804362441978071262167040 }, some { target := 317, numerator := 138837574596367569282662400 }, some { target := 318, numerator := 122970423213925561364643840 }, some { target := 319, numerator := 5755809163980838372261232640 }, some { target := 320, numerator := 1566881199016148281904332800 }, some { target := 321, numerator := 142804362441978071262167040 }, some { target := 322, numerator := 5755809163980838372261232640 }, some { target := 323, numerator := 138837574596367569282662400 }, some { target := 324, numerator := 138837574596367569282662400 }, some { target := 325, numerator := 119003635368315059385139200 }, some { target := 326, numerator := 138837574596367569282662400 }, some { target := 327, numerator := 1566881199016148281904332800 }, some { target := 328, numerator := 119003635368315059385139200 }, some { target := 329, numerator := 138837574596367569282662400 }, some { target := 330, numerator := 122970423213925561364643840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 2201567254313828598625075200 }, some { target := 342, numerator := 2264469175865652272871505920 }, some { target := 343, numerator := 2201567254313828598625075200 }, some { target := 344, numerator := 1949959568106533901639352320 }, some { target := 345, numerator := 91270688171696151331570974720 }, some { target := 346, numerator := 24846259012970351327340134400 }, some { target := 347, numerator := 2264469175865652272871505920 }, some { target := 348, numerator := 91270688171696151331570974720 }, some { target := 349, numerator := 2201567254313828598625075200 }, some { target := 350, numerator := 2201567254313828598625075200 }, some { target := 351, numerator := 1887057646554710227392921600 }, some { target := 352, numerator := 2201567254313828598625075200 }, some { target := 353, numerator := 24846259012970351327340134400 }, some { target := 354, numerator := 1887057646554710227392921600 }, some { target := 355, numerator := 2201567254313828598625075200 }, some { target := 356, numerator := 1949959568106533901639352320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 158671513824420079180185600 }, some { target := 377, numerator := 163204985647974938585333760 }, some { target := 378, numerator := 158671513824420079180185600 }, some { target := 379, numerator := 140537626530200641559592960 }, some { target := 380, numerator := 6578067615978100996869980160 }, some { target := 381, numerator := 1790721370304169465033523200 }, some { target := 382, numerator := 163204985647974938585333760 }, some { target := 383, numerator := 6578067615978100996869980160 }, some { target := 384, numerator := 158671513824420079180185600 }, some { target := 385, numerator := 158671513824420079180185600 }, some { target := 386, numerator := 136004154706645782154444800 }, some { target := 387, numerator := 158671513824420079180185600 }, some { target := 388, numerator := 1790721370304169465033523200 }, some { target := 389, numerator := 136004154706645782154444800 }, some { target := 390, numerator := 158671513824420079180185600 }, some { target := 391, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 154704725978809577200680960 }, some { target := 457, numerator := 159124861006775565120700416 }, some { target := 458, numerator := 154704725978809577200680960 }, some { target := 459, numerator := 137024185866945625520603136 }, some { target := 460, numerator := 6413615925578648471948230656 }, some { target := 461, numerator := 1745953336046565228407685120 }, some { target := 462, numerator := 159124861006775565120700416 }, some { target := 463, numerator := 6413615925578648471948230656 }, some { target := 464, numerator := 154704725978809577200680960 }, some { target := 465, numerator := 154704725978809577200680960 }, some { target := 466, numerator := 132604050838979637600583680 }, some { target := 467, numerator := 154704725978809577200680960 }, some { target := 468, numerator := 1745953336046565228407685120 }, some { target := 469, numerator := 132604050838979637600583680 }, some { target := 470, numerator := 154704725978809577200680960 }, some { target := 471, numerator := 137024185866945625520603136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 154704725978809577200680960 }, some { target := 483, numerator := 159124861006775565120700416 }, some { target := 484, numerator := 154704725978809577200680960 }, some { target := 485, numerator := 137024185866945625520603136 }, some { target := 486, numerator := 6413615925578648471948230656 }, some { target := 487, numerator := 1745953336046565228407685120 }, some { target := 488, numerator := 159124861006775565120700416 }, some { target := 489, numerator := 6413615925578648471948230656 }, some { target := 490, numerator := 154704725978809577200680960 }, some { target := 491, numerator := 154704725978809577200680960 }, some { target := 492, numerator := 132604050838979637600583680 }, some { target := 493, numerator := 154704725978809577200680960 }, some { target := 494, numerator := 1745953336046565228407685120 }, some { target := 495, numerator := 132604050838979637600583680 }, some { target := 496, numerator := 154704725978809577200680960 }, some { target := 497, numerator := 137024185866945625520603136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 154704725978809577200680960 }, some { target := 532, numerator := 159124861006775565120700416 }, some { target := 533, numerator := 154704725978809577200680960 }, some { target := 534, numerator := 137024185866945625520603136 }, some { target := 535, numerator := 6413615925578648471948230656 }, some { target := 536, numerator := 1745953336046565228407685120 }, some { target := 537, numerator := 159124861006775565120700416 }, some { target := 538, numerator := 6413615925578648471948230656 }, some { target := 539, numerator := 154704725978809577200680960 }, some { target := 540, numerator := 154704725978809577200680960 }, some { target := 541, numerator := 132604050838979637600583680 }, some { target := 542, numerator := 154704725978809577200680960 }, some { target := 543, numerator := 1745953336046565228407685120 }, some { target := 544, numerator := 132604050838979637600583680 }, some { target := 545, numerator := 154704725978809577200680960 }, some { target := 546, numerator := 137024185866945625520603136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 4950551231321906470421790720 }, some { target := 558, numerator := 5091995552216818083862413312 }, some { target := 559, numerator := 4950551231321906470421790720 }, some { target := 560, numerator := 4384773947742260016659300352 }, some { target := 561, numerator := 205235709618516751102343380992 }, some { target := 562, numerator := 55870506753490087309045923840 }, some { target := 563, numerator := 5091995552216818083862413312 }, some { target := 564, numerator := 205235709618516751102343380992 }, some { target := 565, numerator := 4950551231321906470421790720 }, some { target := 566, numerator := 4950551231321906470421790720 }, some { target := 567, numerator := 4243329626847348403218677760 }, some { target := 568, numerator := 4950551231321906470421790720 }, some { target := 569, numerator := 55870506753490087309045923840 }, some { target := 570, numerator := 4243329626847348403218677760 }, some { target := 571, numerator := 4950551231321906470421790720 }, some { target := 572, numerator := 4384773947742260016659300352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 154704725978809577200680960 }, some { target := 593, numerator := 159124861006775565120700416 }, some { target := 594, numerator := 154704725978809577200680960 }, some { target := 595, numerator := 137024185866945625520603136 }, some { target := 596, numerator := 6413615925578648471948230656 }, some { target := 597, numerator := 1745953336046565228407685120 }, some { target := 598, numerator := 159124861006775565120700416 }, some { target := 599, numerator := 6413615925578648471948230656 }, some { target := 600, numerator := 154704725978809577200680960 }, some { target := 601, numerator := 154704725978809577200680960 }, some { target := 602, numerator := 132604050838979637600583680 }, some { target := 603, numerator := 154704725978809577200680960 }, some { target := 604, numerator := 1745953336046565228407685120 }, some { target := 605, numerator := 132604050838979637600583680 }, some { target := 606, numerator := 154704725978809577200680960 }, some { target := 607, numerator := 137024185866945625520603136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 178505453052472589077708800 }, some { target := 654, numerator := 183605608853971805908500480 }, some { target := 655, numerator := 178505453052472589077708800 }, some { target := 656, numerator := 158104829846475721754542080 }, some { target := 657, numerator := 7400326067975363621478727680 }, some { target := 658, numerator := 2014561541592190648162713600 }, some { target := 659, numerator := 183605608853971805908500480 }, some { target := 660, numerator := 7400326067975363621478727680 }, some { target := 661, numerator := 178505453052472589077708800 }, some { target := 662, numerator := 178505453052472589077708800 }, some { target := 663, numerator := 153004674044976504923750400 }, some { target := 664, numerator := 178505453052472589077708800 }, some { target := 665, numerator := 2014561541592190648162713600 }, some { target := 666, numerator := 153004674044976504923750400 }, some { target := 667, numerator := 178505453052472589077708800 }, some { target := 668, numerator := 158104829846475721754542080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 186439028743693593036718080 }, some { target := 689, numerator := 191765858136370552837767168 }, some { target := 690, numerator := 186439028743693593036718080 }, some { target := 691, numerator := 165131711172985753832521728 }, some { target := 692, numerator := 7729229448774268671322226688 }, some { target := 693, numerator := 2104097610107399121414389760 }, some { target := 694, numerator := 191765858136370552837767168 }, some { target := 695, numerator := 7729229448774268671322226688 }, some { target := 696, numerator := 186439028743693593036718080 }, some { target := 697, numerator := 186439028743693593036718080 }, some { target := 698, numerator := 159804881780308794031472640 }, some { target := 699, numerator := 186439028743693593036718080 }, some { target := 700, numerator := 2104097610107399121414389760 }, some { target := 701, numerator := 159804881780308794031472640 }, some { target := 702, numerator := 186439028743693593036718080 }, some { target := 703, numerator := 165131711172985753832521728 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 28, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 3, 11, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 7072942846462084828364800 }, some { target := 12, numerator := 141741774643100179960430592 }, some { target := 13, numerator := 237933797354984533626191872 }, some { target := 14, numerator := 228314595083796098259615744 }, some { target := 15, numerator := 7072942846462084828364800 }, some { target := 16, numerator := 228314595083796098259615744 }, some { target := 17, numerator := 152492647769722548899545088 }, some { target := 18, numerator := 7355860560320568221499392 }, some { target := 19, numerator := 141741774643100179960430592 }, some { target := 20, numerator := 6790025132603601435230208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 1129175472129362512943513600 }, some { target := 32, numerator := 22628676461472424759388012544 }, some { target := 33, numerator := 37985462882431754935419797504 }, some { target := 34, numerator := 36449784240335821917816619008 }, some { target := 35, numerator := 1129175472129362512943513600 }, some { target := 36, numerator := 36449784240335821917816619008 }, some { target := 37, numerator := 24345023179109055779062153216 }, some { target := 38, numerator := 1174342491014537013461254144 }, some { target := 39, numerator := 22628676461472424759388012544 }, some { target := 40, numerator := 1084008453244188012425773056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 11267473156777250785958297600 }, some { target := 77, numerator := 225800162061816105750604283904 }, some { target := 78, numerator := 379037796993986716439637131264 }, some { target := 79, numerator := 363714033500769655370733846528 }, some { target := 80, numerator := 11267473156777250785958297600 }, some { target := 81, numerator := 363714033500769655370733846528 }, some { target := 82, numerator := 242926721260117526945260896256 }, some { target := 83, numerator := 11718172083048340817396629504 }, some { target := 84, numerator := 225800162061816105750604283904 }, some { target := 85, numerator := 10816774230506160754519965696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 1129175472129362512943513600 }, some { target := 306, numerator := 22628676461472424759388012544 }, some { target := 307, numerator := 37985462882431754935419797504 }, some { target := 308, numerator := 36449784240335821917816619008 }, some { target := 309, numerator := 1129175472129362512943513600 }, some { target := 310, numerator := 36449784240335821917816619008 }, some { target := 311, numerator := 24345023179109055779062153216 }, some { target := 312, numerator := 1174342491014537013461254144 }, some { target := 313, numerator := 22628676461472424759388012544 }, some { target := 314, numerator := 1084008453244188012425773056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 7072135801408860035481600 }, some { target := 644, numerator := 141725601460233555111051264 }, some { target := 645, numerator := 237906648359394051593601024 }, some { target := 646, numerator := 228288543669478001945346048 }, some { target := 647, numerator := 7072135801408860035481600 }, some { target := 648, numerator := 228288543669478001945346048 }, some { target := 649, numerator := 152475247878375022364983296 }, some { target := 650, numerator := 7355021233465214436900864 }, some { target := 651, numerator := 141725601460233555111051264 }, some { target := 652, numerator := 6789250369352505634062336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left3.expected ++ Left11.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left3.routed_eq, Left11.routed_eq, Left18.routed_eq]
  rfl

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 13, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 3487692651760072062570332160 }, some { target := 3, numerator := 3187816274225561193639051264 }, some { target := 4, numerator := 3487692651760072062570332160 }, some { target := 5, numerator := 3187816274225561193639051264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 131041572554955862498732933120 }, some { target := 23, numerator := 119774446690417601424075522048 }, some { target := 24, numerator := 131041572554955862498732933120 }, some { target := 25, numerator := 119774446690417601424075522048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 131031661603592090291525386240 }, some { target := 73, numerator := 119765387895619686266459652096 }, some { target := 74, numerator := 131031661603592090291525386240 }, some { target := 75, numerator := 119765387895619686266459652096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 3497603603123844269777879040 }, some { target := 302, numerator := 3196875069023476351254921216 }, some { target := 303, numerator := 3497603603123844269777879040 }, some { target := 304, numerator := 3196875069023476351254921216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot14

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent3
