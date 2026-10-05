import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 25, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 29, numerator := 132226261520350065983488000 }, some { target := 30, numerator := 136004154706645782154444800 }, some { target := 31, numerator := 132226261520350065983488000 }, some { target := 32, numerator := 117114688775167201299660800 }, some { target := 33, numerator := 5481723013315084164058316800 }, some { target := 34, numerator := 1492267808586807887527936000 }, some { target := 35, numerator := 136004154706645782154444800 }, some { target := 36, numerator := 5481723013315084164058316800 }, some { target := 37, numerator := 132226261520350065983488000 }, some { target := 38, numerator := 132226261520350065983488000 }, some { target := 39, numerator := 113336795588871485128704000 }, some { target := 40, numerator := 132226261520350065983488000 }, some { target := 41, numerator := 1492267808586807887527936000 }, some { target := 42, numerator := 113336795588871485128704000 }, some { target := 43, numerator := 132226261520350065983488000 }, some { target := 44, numerator := 117114688775167201299660800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 157018685555415703355392000 }, some { target := 56, numerator := 161504933714141866308403200 }, some { target := 57, numerator := 157018685555415703355392000 }, some { target := 58, numerator := 139073692920511051543347200 }, some { target := 59, numerator := 6509546078311662444819251200 }, some { target := 60, numerator := 1772068022696834366439424000 }, some { target := 61, numerator := 161504933714141866308403200 }, some { target := 62, numerator := 6509546078311662444819251200 }, some { target := 63, numerator := 157018685555415703355392000 }, some { target := 64, numerator := 157018685555415703355392000 }, some { target := 65, numerator := 134587444761784888590336000 }, some { target := 66, numerator := 157018685555415703355392000 }, some { target := 67, numerator := 1772068022696834366439424000 }, some { target := 68, numerator := 134587444761784888590336000 }, some { target := 69, numerator := 157018685555415703355392000 }, some { target := 70, numerator := 139073692920511051543347200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 119830049502817247297536000 }, some { target := 105, numerator := 123253765202897740077465600 }, some { target := 106, numerator := 119830049502817247297536000 }, some { target := 107, numerator := 106135186702495276177817600 }, some { target := 108, numerator := 4967811480816795023677849600 }, some { target := 109, numerator := 1352367701531794648072192000 }, some { target := 110, numerator := 123253765202897740077465600 }, some { target := 111, numerator := 4967811480816795023677849600 }, some { target := 112, numerator := 119830049502817247297536000 }, some { target := 113, numerator := 119830049502817247297536000 }, some { target := 114, numerator := 102711471002414783397888000 }, some { target := 115, numerator := 119830049502817247297536000 }, some { target := 116, numerator := 1352367701531794648072192000 }, some { target := 117, numerator := 102711471002414783397888000 }, some { target := 118, numerator := 119830049502817247297536000 }, some { target := 119, numerator := 106135186702495276177817600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 130, numerator := 1235489131080770929033216000 }, some { target := 131, numerator := 1270788820540221527005593600 }, some { target := 132, numerator := 1235489131080770929033216000 }, some { target := 133, numerator := 1094290373242968537143705600 }, some { target := 134, numerator := 51219849405662817657919897600 }, some { target := 135, numerator := 13943377336482986199089152000 }, some { target := 136, numerator := 1270788820540221527005593600 }, some { target := 137, numerator := 51219849405662817657919897600 }, some { target := 138, numerator := 1235489131080770929033216000 }, some { target := 139, numerator := 1235489131080770929033216000 }, some { target := 140, numerator := 1058990683783517939171328000 }, some { target := 141, numerator := 1235489131080770929033216000 }, some { target := 142, numerator := 13943377336482986199089152000 }, some { target := 143, numerator := 1058990683783517939171328000 }, some { target := 144, numerator := 1235489131080770929033216000 }, some { target := 145, numerator := 1094290373242968537143705600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 165, numerator := 148754544210393824231424000 }, some { target := 166, numerator := 153004674044976504923750400 }, some { target := 167, numerator := 148754544210393824231424000 }, some { target := 168, numerator := 131754024872063101462118400 }, some { target := 169, numerator := 6166938389979469684565606400 }, some { target := 170, numerator := 1678801284660158873468928000 }, some { target := 171, numerator := 153004674044976504923750400 }, some { target := 172, numerator := 6166938389979469684565606400 }, some { target := 173, numerator := 148754544210393824231424000 }, some { target := 174, numerator := 148754544210393824231424000 }, some { target := 175, numerator := 127503895037480420769792000 }, some { target := 176, numerator := 148754544210393824231424000 }, some { target := 177, numerator := 1678801284660158873468928000 }, some { target := 178, numerator := 127503895037480420769792000 }, some { target := 179, numerator := 148754544210393824231424000 }, some { target := 180, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 119830049502817247297536000 }, some { target := 227, numerator := 123253765202897740077465600 }, some { target := 228, numerator := 119830049502817247297536000 }, some { target := 229, numerator := 106135186702495276177817600 }, some { target := 230, numerator := 4967811480816795023677849600 }, some { target := 231, numerator := 1352367701531794648072192000 }, some { target := 232, numerator := 123253765202897740077465600 }, some { target := 233, numerator := 4967811480816795023677849600 }, some { target := 234, numerator := 119830049502817247297536000 }, some { target := 235, numerator := 119830049502817247297536000 }, some { target := 236, numerator := 102711471002414783397888000 }, some { target := 237, numerator := 119830049502817247297536000 }, some { target := 238, numerator := 1352367701531794648072192000 }, some { target := 239, numerator := 102711471002414783397888000 }, some { target := 240, numerator := 119830049502817247297536000 }, some { target := 241, numerator := 106135186702495276177817600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 261, numerator := 148754544210393824231424000 }, some { target := 262, numerator := 153004674044976504923750400 }, some { target := 263, numerator := 148754544210393824231424000 }, some { target := 264, numerator := 131754024872063101462118400 }, some { target := 265, numerator := 6166938389979469684565606400 }, some { target := 266, numerator := 1678801284660158873468928000 }, some { target := 267, numerator := 153004674044976504923750400 }, some { target := 268, numerator := 6166938389979469684565606400 }, some { target := 269, numerator := 148754544210393824231424000 }, some { target := 270, numerator := 148754544210393824231424000 }, some { target := 271, numerator := 127503895037480420769792000 }, some { target := 272, numerator := 148754544210393824231424000 }, some { target := 273, numerator := 1678801284660158873468928000 }, some { target := 274, numerator := 127503895037480420769792000 }, some { target := 275, numerator := 148754544210393824231424000 }, some { target := 276, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 371, numerator := 148754544210393824231424000 }, some { target := 372, numerator := 153004674044976504923750400 }, some { target := 373, numerator := 148754544210393824231424000 }, some { target := 374, numerator := 131754024872063101462118400 }, some { target := 375, numerator := 6166938389979469684565606400 }, some { target := 376, numerator := 1678801284660158873468928000 }, some { target := 377, numerator := 153004674044976504923750400 }, some { target := 378, numerator := 6166938389979469684565606400 }, some { target := 379, numerator := 148754544210393824231424000 }, some { target := 380, numerator := 148754544210393824231424000 }, some { target := 381, numerator := 127503895037480420769792000 }, some { target := 382, numerator := 148754544210393824231424000 }, some { target := 383, numerator := 1678801284660158873468928000 }, some { target := 384, numerator := 127503895037480420769792000 }, some { target := 385, numerator := 148754544210393824231424000 }, some { target := 386, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 397, numerator := 6371652977011868804579328000 }, some { target := 398, numerator := 6553700204926493627567308800 }, some { target := 399, numerator := 6371652977011868804579328000 }, some { target := 400, numerator := 5643464065353369512627404800 }, some { target := 401, numerator := 264150527704120618155560140800 }, some { target := 402, numerator := 71908655026276805080252416000 }, some { target := 403, numerator := 6553700204926493627567308800 }, some { target := 404, numerator := 264150527704120618155560140800 }, some { target := 405, numerator := 6371652977011868804579328000 }, some { target := 406, numerator := 6371652977011868804579328000 }, some { target := 407, numerator := 5461416837438744689639424000 }, some { target := 408, numerator := 6371652977011868804579328000 }, some { target := 409, numerator := 71908655026276805080252416000 }, some { target := 410, numerator := 5461416837438744689639424000 }, some { target := 411, numerator := 6371652977011868804579328000 }, some { target := 412, numerator := 5643464065353369512627404800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 148754544210393824231424000 }, some { target := 433, numerator := 153004674044976504923750400 }, some { target := 434, numerator := 148754544210393824231424000 }, some { target := 435, numerator := 131754024872063101462118400 }, some { target := 436, numerator := 6166938389979469684565606400 }, some { target := 437, numerator := 1678801284660158873468928000 }, some { target := 438, numerator := 153004674044976504923750400 }, some { target := 439, numerator := 6166938389979469684565606400 }, some { target := 440, numerator := 148754544210393824231424000 }, some { target := 441, numerator := 148754544210393824231424000 }, some { target := 442, numerator := 127503895037480420769792000 }, some { target := 443, numerator := 148754544210393824231424000 }, some { target := 444, numerator := 1678801284660158873468928000 }, some { target := 445, numerator := 127503895037480420769792000 }, some { target := 446, numerator := 148754544210393824231424000 }, some { target := 447, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 493, numerator := 1235489131080770929033216000 }, some { target := 494, numerator := 1270788820540221527005593600 }, some { target := 495, numerator := 1235489131080770929033216000 }, some { target := 496, numerator := 1094290373242968537143705600 }, some { target := 497, numerator := 51219849405662817657919897600 }, some { target := 498, numerator := 13943377336482986199089152000 }, some { target := 499, numerator := 1270788820540221527005593600 }, some { target := 500, numerator := 51219849405662817657919897600 }, some { target := 501, numerator := 1235489131080770929033216000 }, some { target := 502, numerator := 1235489131080770929033216000 }, some { target := 503, numerator := 1058990683783517939171328000 }, some { target := 504, numerator := 1235489131080770929033216000 }, some { target := 505, numerator := 13943377336482986199089152000 }, some { target := 506, numerator := 1058990683783517939171328000 }, some { target := 507, numerator := 1235489131080770929033216000 }, some { target := 508, numerator := 1094290373242968537143705600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 6371652977011868804579328000 }, some { target := 529, numerator := 6553700204926493627567308800 }, some { target := 530, numerator := 6371652977011868804579328000 }, some { target := 531, numerator := 5643464065353369512627404800 }, some { target := 532, numerator := 264150527704120618155560140800 }, some { target := 533, numerator := 71908655026276805080252416000 }, some { target := 534, numerator := 6553700204926493627567308800 }, some { target := 535, numerator := 264150527704120618155560140800 }, some { target := 536, numerator := 6371652977011868804579328000 }, some { target := 537, numerator := 6371652977011868804579328000 }, some { target := 538, numerator := 5461416837438744689639424000 }, some { target := 539, numerator := 6371652977011868804579328000 }, some { target := 540, numerator := 71908655026276805080252416000 }, some { target := 541, numerator := 5461416837438744689639424000 }, some { target := 542, numerator := 6371652977011868804579328000 }, some { target := 543, numerator := 5643464065353369512627404800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 132226261520350065983488000 }, some { target := 625, numerator := 136004154706645782154444800 }, some { target := 626, numerator := 132226261520350065983488000 }, some { target := 627, numerator := 117114688775167201299660800 }, some { target := 628, numerator := 5481723013315084164058316800 }, some { target := 629, numerator := 1492267808586807887527936000 }, some { target := 630, numerator := 136004154706645782154444800 }, some { target := 631, numerator := 5481723013315084164058316800 }, some { target := 632, numerator := 132226261520350065983488000 }, some { target := 633, numerator := 132226261520350065983488000 }, some { target := 634, numerator := 113336795588871485128704000 }, some { target := 635, numerator := 132226261520350065983488000 }, some { target := 636, numerator := 1492267808586807887527936000 }, some { target := 637, numerator := 113336795588871485128704000 }, some { target := 638, numerator := 132226261520350065983488000 }, some { target := 639, numerator := 117114688775167201299660800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 760, numerator := 148754544210393824231424000 }, some { target := 761, numerator := 153004674044976504923750400 }, some { target := 762, numerator := 148754544210393824231424000 }, some { target := 763, numerator := 131754024872063101462118400 }, some { target := 764, numerator := 6166938389979469684565606400 }, some { target := 765, numerator := 1678801284660158873468928000 }, some { target := 766, numerator := 153004674044976504923750400 }, some { target := 767, numerator := 6166938389979469684565606400 }, some { target := 768, numerator := 148754544210393824231424000 }, some { target := 769, numerator := 148754544210393824231424000 }, some { target := 770, numerator := 127503895037480420769792000 }, some { target := 771, numerator := 148754544210393824231424000 }, some { target := 772, numerator := 1678801284660158873468928000 }, some { target := 773, numerator := 127503895037480420769792000 }, some { target := 774, numerator := 148754544210393824231424000 }, some { target := 775, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 795, numerator := 148754544210393824231424000 }, some { target := 796, numerator := 153004674044976504923750400 }, some { target := 797, numerator := 148754544210393824231424000 }, some { target := 798, numerator := 131754024872063101462118400 }, some { target := 799, numerator := 6166938389979469684565606400 }, some { target := 800, numerator := 1678801284660158873468928000 }, some { target := 801, numerator := 153004674044976504923750400 }, some { target := 802, numerator := 6166938389979469684565606400 }, some { target := 803, numerator := 148754544210393824231424000 }, some { target := 804, numerator := 148754544210393824231424000 }, some { target := 805, numerator := 127503895037480420769792000 }, some { target := 806, numerator := 148754544210393824231424000 }, some { target := 807, numerator := 1678801284660158873468928000 }, some { target := 808, numerator := 127503895037480420769792000 }, some { target := 809, numerator := 148754544210393824231424000 }, some { target := 810, numerator := 131754024872063101462118400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 891, numerator := 157018685555415703355392000 }, some { target := 892, numerator := 161504933714141866308403200 }, some { target := 893, numerator := 157018685555415703355392000 }, some { target := 894, numerator := 139073692920511051543347200 }, some { target := 895, numerator := 6509546078311662444819251200 }, some { target := 896, numerator := 1772068022696834366439424000 }, some { target := 897, numerator := 161504933714141866308403200 }, some { target := 898, numerator := 6509546078311662444819251200 }, some { target := 899, numerator := 157018685555415703355392000 }, some { target := 900, numerator := 157018685555415703355392000 }, some { target := 901, numerator := 134587444761784888590336000 }, some { target := 902, numerator := 157018685555415703355392000 }, some { target := 903, numerator := 1772068022696834366439424000 }, some { target := 904, numerator := 134587444761784888590336000 }, some { target := 905, numerator := 157018685555415703355392000 }, some { target := 906, numerator := 139073692920511051543347200 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 7, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 3, 5]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

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
  [some { target := 5, numerator := 606908573371999476672102400 }, some { target := 6, numerator := 12162447810374869512508932096 }, some { target := 7, numerator := 20416404408234062395249524736 }, some { target := 8, numerator := 19591008748448143106975465472 }, some { target := 9, numerator := 606908573371999476672102400 }, some { target := 10, numerator := 19591008748448143106975465472 }, some { target := 11, numerator := 13084948841900308717050527744 }, some { target := 12, numerator := 631184916306879455738986496 }, some { target := 13, numerator := 12162447810374869512508932096 }, some { target := 14, numerator := 582632230437119497605218304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 2171175349938226042031308800 }, some { target := 95, numerator := 43510354012762049882307428352 }, some { target := 96, numerator := 73038338771921924053933228032 }, some { target := 97, numerator := 70085540296005936636770648064 }, some { target := 98, numerator := 2171175349938226042031308800 }, some { target := 99, numerator := 70085540296005936636770648064 }, some { target := 100, numerator := 46810540544668153466195017728 }, some { target := 101, numerator := 2258022363935755083712561152 }, some { target := 102, numerator := 43510354012762049882307428352 }, some { target := 103, numerator := 2084328335940697000350056448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 606908371610736170473881600 }, some { target := 217, numerator := 12162443767079152856296587264 }, some { target := 218, numerator := 20416397620985164774741377024 }, some { target := 219, numerator := 19591002235594563582896898048 }, some { target := 220, numerator := 606908371610736170473881600 }, some { target := 221, numerator := 19591002235594563582896898048 }, some { target := 222, numerator := 13084944491927471835416887296 }, some { target := 223, numerator := 631184706475165617292836864 }, some { target := 224, numerator := 12162443767079152856296587264 }, some { target := 225, numerator := 582632036746306723654926336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left3.expected ++ Left5.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left3.routed_eq, Left5.routed_eq]
  rfl

end Slot21

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 1, numerator := 10348405015901225735484866560 }, some { target := 2, numerator := 9458635612664858662901121024 }, some { target := 3, numerator := 10348405015901225735484866560 }, some { target := 4, numerator := 9458635612664858662901121024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 10348405015901225735484866560 }, some { target := 91, numerator := 9458635612664858662901121024 }, some { target := 92, numerator := 10348405015901225735484866560 }, some { target := 93, numerator := 9458635612664858662901121024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot23

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2
