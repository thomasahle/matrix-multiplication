import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 1,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 3, #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 35, numerator := 12297042321392556136464384 }, some { target := 36, numerator := 13883757459636756928266240 }, some { target := 37, numerator := 11900363536831505938513920 }, some { target := 38, numerator := 156688119901614828190433280 }, some { target := 39, numerator := 13883757459636756928266240 }, some { target := 40, numerator := 11900363536831505938513920 }, some { target := 41, numerator := 13883757459636756928266240 }, some { target := 42, numerator := 13883757459636756928266240 }, some { target := 43, numerator := 575580916398083837226123264 }, some { target := 44, numerator := 14280436244197807126216704 }, some { target := 45, numerator := 156688119901614828190433280 }, some { target := 46, numerator := 575580916398083837226123264 }, some { target := 47, numerator := 12297042321392556136464384 }, some { target := 48, numerator := 13883757459636756928266240 }, some { target := 49, numerator := 14280436244197807126216704 }, some { target := 50, numerator := 13883757459636756928266240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 70, numerator := 245940846427851122729287680 }, some { target := 71, numerator := 277675149192735138565324800 }, some { target := 72, numerator := 238007270736630118770278400 }, some { target := 73, numerator := 3133762398032296563808665600 }, some { target := 74, numerator := 277675149192735138565324800 }, some { target := 75, numerator := 238007270736630118770278400 }, some { target := 76, numerator := 277675149192735138565324800 }, some { target := 77, numerator := 277675149192735138565324800 }, some { target := 78, numerator := 11511618327961676744522465280 }, some { target := 79, numerator := 285608724883956142524334080 }, some { target := 80, numerator := 3133762398032296563808665600 }, some { target := 81, numerator := 11511618327961676744522465280 }, some { target := 82, numerator := 245940846427851122729287680 }, some { target := 83, numerator := 277675149192735138565324800 }, some { target := 84, numerator := 285608724883956142524334080 }, some { target := 85, numerator := 277675149192735138565324800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 12736222404299433141338112 }, some { target := 97, numerator := 14379605940338069675704320 }, some { target := 98, numerator := 12325376520289774007746560 }, some { target := 99, numerator := 162284124183815357768663040 }, some { target := 100, numerator := 14379605940338069675704320 }, some { target := 101, numerator := 12325376520289774007746560 }, some { target := 102, numerator := 14379605940338069675704320 }, some { target := 103, numerator := 14379605940338069675704320 }, some { target := 104, numerator := 596137377698015402841341952 }, some { target := 105, numerator := 14790451824347728809295872 }, some { target := 106, numerator := 162284124183815357768663040 }, some { target := 107, numerator := 596137377698015402841341952 }, some { target := 108, numerator := 12736222404299433141338112 }, some { target := 109, numerator := 14379605940338069675704320 }, some { target := 110, numerator := 14790451824347728809295872 }, some { target := 111, numerator := 14379605940338069675704320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 228812823194482919539212288 }, some { target := 146, numerator := 258337058445383941415239680 }, some { target := 147, numerator := 221431764381757664070205440 }, some { target := 148, numerator := 2915518231026475910257704960 }, some { target := 149, numerator := 258337058445383941415239680 }, some { target := 150, numerator := 221431764381757664070205440 }, some { target := 151, numerator := 258337058445383941415239680 }, some { target := 152, numerator := 258337058445383941415239680 }, some { target := 153, numerator := 10709916337264345685528936448 }, some { target := 154, numerator := 265718117258109196884246528 }, some { target := 155, numerator := 2915518231026475910257704960 }, some { target := 156, numerator := 10709916337264345685528936448 }, some { target := 157, numerator := 228812823194482919539212288 }, some { target := 158, numerator := 258337058445383941415239680 }, some { target := 159, numerator := 265718117258109196884246528 }, some { target := 160, numerator := 258337058445383941415239680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 342560464667364063801507840 }, some { target := 172, numerator := 386761814947023943001702400 }, some { target := 173, numerator := 331510127097449094001459200 }, some { target := 174, numerator := 4364883340116413071019212800 }, some { target := 175, numerator := 386761814947023943001702400 }, some { target := 176, numerator := 331510127097449094001459200 }, some { target := 177, numerator := 386761814947023943001702400 }, some { target := 178, numerator := 386761814947023943001702400 }, some { target := 179, numerator := 16034039813946621179870576640 }, some { target := 180, numerator := 397812152516938912801751040 }, some { target := 181, numerator := 4364883340116413071019212800 }, some { target := 182, numerator := 16034039813946621179870576640 }, some { target := 183, numerator := 342560464667364063801507840 }, some { target := 184, numerator := 386761814947023943001702400 }, some { target := 185, numerator := 397812152516938912801751040 }, some { target := 186, numerator := 386761814947023943001702400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 12297042321392556136464384 }, some { target := 217, numerator := 13883757459636756928266240 }, some { target := 218, numerator := 11900363536831505938513920 }, some { target := 219, numerator := 156688119901614828190433280 }, some { target := 220, numerator := 13883757459636756928266240 }, some { target := 221, numerator := 11900363536831505938513920 }, some { target := 222, numerator := 13883757459636756928266240 }, some { target := 223, numerator := 13883757459636756928266240 }, some { target := 224, numerator := 575580916398083837226123264 }, some { target := 225, numerator := 14280436244197807126216704 }, some { target := 226, numerator := 156688119901614828190433280 }, some { target := 227, numerator := 575580916398083837226123264 }, some { target := 228, numerator := 12297042321392556136464384 }, some { target := 229, numerator := 13883757459636756928266240 }, some { target := 230, numerator := 14280436244197807126216704 }, some { target := 231, numerator := 13883757459636756928266240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 342999644750270940806381568 }, some { target := 286, numerator := 387257663427725255749140480 }, some { target := 287, numerator := 331935140080907362070691840 }, some { target := 288, numerator := 4370479344398613600597442560 }, some { target := 289, numerator := 387257663427725255749140480 }, some { target := 290, numerator := 331935140080907362070691840 }, some { target := 291, numerator := 387257663427725255749140480 }, some { target := 292, numerator := 387257663427725255749140480 }, some { target := 293, numerator := 16054596275246552745485795328 }, some { target := 294, numerator := 398322168097088834484830208 }, some { target := 295, numerator := 4370479344398613600597442560 }, some { target := 296, numerator := 16054596275246552745485795328 }, some { target := 297, numerator := 342999644750270940806381568 }, some { target := 298, numerator := 387257663427725255749140480 }, some { target := 299, numerator := 398322168097088834484830208 }, some { target := 300, numerator := 387257663427725255749140480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 342999644750270940806381568 }, some { target := 312, numerator := 387257663427725255749140480 }, some { target := 313, numerator := 331935140080907362070691840 }, some { target := 314, numerator := 4370479344398613600597442560 }, some { target := 315, numerator := 387257663427725255749140480 }, some { target := 316, numerator := 331935140080907362070691840 }, some { target := 317, numerator := 387257663427725255749140480 }, some { target := 318, numerator := 387257663427725255749140480 }, some { target := 319, numerator := 16054596275246552745485795328 }, some { target := 320, numerator := 398322168097088834484830208 }, some { target := 321, numerator := 4370479344398613600597442560 }, some { target := 322, numerator := 16054596275246552745485795328 }, some { target := 323, numerator := 342999644750270940806381568 }, some { target := 324, numerator := 387257663427725255749140480 }, some { target := 325, numerator := 398322168097088834484830208 }, some { target := 326, numerator := 387257663427725255749140480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 245501666344944245724413952 }, some { target := 357, numerator := 277179300712033825817886720 }, some { target := 358, numerator := 237582257753171850701045760 }, some { target := 359, numerator := 3128166393750096034230435840 }, some { target := 360, numerator := 277179300712033825817886720 }, some { target := 361, numerator := 237582257753171850701045760 }, some { target := 362, numerator := 277179300712033825817886720 }, some { target := 363, numerator := 277179300712033825817886720 }, some { target := 364, numerator := 11491061866661745178907246592 }, some { target := 365, numerator := 285098709303806220841254912 }, some { target := 366, numerator := 3128166393750096034230435840 }, some { target := 367, numerator := 11491061866661745178907246592 }, some { target := 368, numerator := 245501666344944245724413952 }, some { target := 369, numerator := 277179300712033825817886720 }, some { target := 370, numerator := 285098709303806220841254912 }, some { target := 371, numerator := 277179300712033825817886720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 12736222404299433141338112 }, some { target := 428, numerator := 14379605940338069675704320 }, some { target := 429, numerator := 12325376520289774007746560 }, some { target := 430, numerator := 162284124183815357768663040 }, some { target := 431, numerator := 14379605940338069675704320 }, some { target := 432, numerator := 12325376520289774007746560 }, some { target := 433, numerator := 14379605940338069675704320 }, some { target := 434, numerator := 14379605940338069675704320 }, some { target := 435, numerator := 596137377698015402841341952 }, some { target := 436, numerator := 14790451824347728809295872 }, some { target := 437, numerator := 162284124183815357768663040 }, some { target := 438, numerator := 596137377698015402841341952 }, some { target := 439, numerator := 12736222404299433141338112 }, some { target := 440, numerator := 14379605940338069675704320 }, some { target := 441, numerator := 14790451824347728809295872 }, some { target := 442, numerator := 14379605940338069675704320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent2
