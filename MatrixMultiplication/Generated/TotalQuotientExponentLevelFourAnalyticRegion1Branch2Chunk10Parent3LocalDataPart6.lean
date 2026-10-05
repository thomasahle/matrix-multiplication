import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 418, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 35, numerator := 68845017224864440575949012992 }, some { target := 36, numerator := 67410746032679764730616741888 }, some { target := 37, numerator := 53068034110833006277294030848 }, some { target := 38, numerator := 1668057396510778008121431293952 }, some { target := 39, numerator := 53068034110833006277294030848 }, some { target := 40, numerator := 53068034110833006277294030848 }, some { target := 41, numerator := 54502305303017682122626301952 }, some { target := 42, numerator := 54502305303017682122626301952 }, some { target := 43, numerator := 922236376574746568548650319872 }, some { target := 44, numerator := 50199491726463654586629488640 }, some { target := 45, numerator := 1668057396510778008121431293952 }, some { target := 46, numerator := 922236376574746568548650319872 }, some { target := 47, numerator := 68845017224864440575949012992 }, some { target := 48, numerator := 53068034110833006277294030848 }, some { target := 49, numerator := 50199491726463654586629488640 }, some { target := 50, numerator := 67410746032679764730616741888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 250404167866237835028977418240 }, some { target := 146, numerator := 245187414369024546799207055360 }, some { target := 147, numerator := 193019879396891664501503426560 }, some { target := 148, numerator := 6067084317259054211222932029440 }, some { target := 149, numerator := 193019879396891664501503426560 }, some { target := 150, numerator := 193019879396891664501503426560 }, some { target := 151, numerator := 198236632894104952731273789440 }, some { target := 152, numerator := 198236632894104952731273789440 }, some { target := 153, numerator := 3354372498708144331742343331840 }, some { target := 154, numerator := 182586372402465088041962700800 }, some { target := 155, numerator := 6067084317259054211222932029440 }, some { target := 156, numerator := 3354372498708144331742343331840 }, some { target := 157, numerator := 250404167866237835028977418240 }, some { target := 158, numerator := 193019879396891664501503426560 }, some { target := 159, numerator := 182586372402465088041962700800 }, some { target := 160, numerator := 245187414369024546799207055360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 68845017224864440575949012992 }, some { target := 217, numerator := 67410746032679764730616741888 }, some { target := 218, numerator := 53068034110833006277294030848 }, some { target := 219, numerator := 1668057396510778008121431293952 }, some { target := 220, numerator := 53068034110833006277294030848 }, some { target := 221, numerator := 53068034110833006277294030848 }, some { target := 222, numerator := 54502305303017682122626301952 }, some { target := 223, numerator := 54502305303017682122626301952 }, some { target := 224, numerator := 922236376574746568548650319872 }, some { target := 225, numerator := 50199491726463654586629488640 }, some { target := 226, numerator := 1668057396510778008121431293952 }, some { target := 227, numerator := 922236376574746568548650319872 }, some { target := 228, numerator := 68845017224864440575949012992 }, some { target := 229, numerator := 53068034110833006277294030848 }, some { target := 230, numerator := 50199491726463654586629488640 }, some { target := 231, numerator := 67410746032679764730616741888 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 926, #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 16, numerator := 53734347641494796748623708160 }, some { target := 17, numerator := 1432915937106527913296632217600 }, some { target := 18, numerator := 1370225864858117317089904558080 }, some { target := 19, numerator := 44778623034578997290519756800 }, some { target := 20, numerator := 1406048763285780514922320363520 }, some { target := 21, numerator := 44778623034578997290519756800 }, some { target := 22, numerator := 1370225864858117317089904558080 }, some { target := 23, numerator := 779148040801674552855043768320 }, some { target := 24, numerator := 1406048763285780514922320363520 }, some { target := 25, numerator := 21950481011550624471812784783360 }, some { target := 26, numerator := 859749562263916747977979330560 }, some { target := 27, numerator := 1432915937106527913296632217600 }, some { target := 28, numerator := 1370225864858117317089904558080 }, some { target := 29, numerator := 44778623034578997290519756800 }, some { target := 30, numerator := 859749562263916747977979330560 }, some { target := 31, numerator := 44778623034578997290519756800 }, some { target := 32, numerator := 1379181589465033116548008509440 }, some { target := 33, numerator := 779148040801674552855043768320 }, some { target := 34, numerator := 53734347641494796748623708160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 53734322018967278366056513536 }, some { target := 127, numerator := 1432915253839127423094840360960 }, some { target := 128, numerator := 1370225211483665598334441095168 }, some { target := 129, numerator := 44778601682472731971713761280 }, some { target := 130, numerator := 1406048092829643783911812104192 }, some { target := 131, numerator := 44778601682472731971713761280 }, some { target := 132, numerator := 1370225211483665598334441095168 }, some { target := 133, numerator := 779147669275025536307819446272 }, some { target := 134, numerator := 1406048092829643783911812104192 }, some { target := 135, numerator := 21950470544748133212534085779456 }, some { target := 136, numerator := 859749152303476453856904216576 }, some { target := 137, numerator := 1432915253839127423094840360960 }, some { target := 138, numerator := 1370225211483665598334441095168 }, some { target := 139, numerator := 44778601682472731971713761280 }, some { target := 140, numerator := 859749152303476453856904216576 }, some { target := 141, numerator := 44778601682472731971713761280 }, some { target := 142, numerator := 1379180931820160144728783847424 }, some { target := 143, numerator := 779147669275025536307819446272 }, some { target := 144, numerator := 53734322018967278366056513536 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 66, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 44681898292956694297140264960 }, some { target := 1, numerator := 45958523958469742705629986816 }, some { target := 2, numerator := 44681898292956694297140264960 }, some { target := 3, numerator := 39575395630904500663181377536 }, some { target := 4, numerator := 1852383840659433240718586413056 }, some { target := 5, numerator := 504267137877654121353440133120 }, some { target := 6, numerator := 45958523958469742705629986816 }, some { target := 7, numerator := 1852383840659433240718586413056 }, some { target := 8, numerator := 44681898292956694297140264960 }, some { target := 9, numerator := 44681898292956694297140264960 }, some { target := 10, numerator := 38298769965391452254691655680 }, some { target := 11, numerator := 44681898292956694297140264960 }, some { target := 12, numerator := 504267137877654121353440133120 }, some { target := 13, numerator := 38298769965391452254691655680 }, some { target := 14, numerator := 44681898292956694297140264960 }, some { target := 15, numerator := 39575395630904500663181377536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot27

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent3
