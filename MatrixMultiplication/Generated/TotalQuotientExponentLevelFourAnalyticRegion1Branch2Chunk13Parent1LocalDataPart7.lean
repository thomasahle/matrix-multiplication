import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 53, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 35, numerator := 8822716632333523820879020032 }, some { target := 36, numerator := 8638910035826575407944040448 }, some { target := 37, numerator := 6800844070757091278594244608 }, some { target := 38, numerator := 213767071737581004243381256192 }, some { target := 39, numerator := 6800844070757091278594244608 }, some { target := 40, numerator := 6800844070757091278594244608 }, some { target := 41, numerator := 6984650667264039691529224192 }, some { target := 42, numerator := 6984650667264039691529224192 }, some { target := 43, numerator := 118187641553967829517191872512 }, some { target := 44, numerator := 6433230877743194452724285440 }, some { target := 45, numerator := 213767071737581004243381256192 }, some { target := 46, numerator := 118187641553967829517191872512 }, some { target := 47, numerator := 8822716632333523820879020032 }, some { target := 48, numerator := 6800844070757091278594244608 }, some { target := 49, numerator := 6433230877743194452724285440 }, some { target := 50, numerator := 8638910035826575407944040448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 31562686229959126005300854784 }, some { target := 146, numerator := 30905130266834977546857086976 }, some { target := 147, numerator := 24329570635593492962419408896 }, some { target := 148, numerator := 764737585113384657170101960704 }, some { target := 149, numerator := 24329570635593492962419408896 }, some { target := 150, numerator := 24329570635593492962419408896 }, some { target := 151, numerator := 24987126598717641420863176704 }, some { target := 152, numerator := 24987126598717641420863176704 }, some { target := 153, numerator := 422808484288827458779342700544 }, some { target := 154, numerator := 23014458709345196045531873280 }, some { target := 155, numerator := 764737585113384657170101960704 }, some { target := 156, numerator := 422808484288827458779342700544 }, some { target := 157, numerator := 31562686229959126005300854784 }, some { target := 158, numerator := 24329570635593492962419408896 }, some { target := 159, numerator := 23014458709345196045531873280 }, some { target := 160, numerator := 30905130266834977546857086976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 8822713699301216101060313088 }, some { target := 217, numerator := 8638907163899107432288223232 }, some { target := 218, numerator := 6800841809878020744567324672 }, some { target := 219, numerator := 213767000672652381781940502528 }, some { target := 220, numerator := 6800841809878020744567324672 }, some { target := 221, numerator := 6800841809878020744567324672 }, some { target := 222, numerator := 6984648345280129413339414528 }, some { target := 223, numerator := 6984648345280129413339414528 }, some { target := 224, numerator := 118187602263555874020453777408 }, some { target := 225, numerator := 6433228739073803407023144960 }, some { target := 226, numerator := 213767000672652381781940502528 }, some { target := 227, numerator := 118187602263555874020453777408 }, some { target := 228, numerator := 8822713699301216101060313088 }, some { target := 229, numerator := 6800841809878020744567324672 }, some { target := 230, numerator := 6433228739073803407023144960 }, some { target := 231, numerator := 8638907163899107432288223232 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 155, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 16, numerator := 8994408097932841059813949440 }, some { target := 17, numerator := 239850882611542428261705318400 }, some { target := 18, numerator := 229357406497287447025255710720 }, some { target := 19, numerator := 7495340081610700883178291200 }, some { target := 20, numerator := 235353678562576007731798343680 }, some { target := 21, numerator := 7495340081610700883178291200 }, some { target := 22, numerator := 229357406497287447025255710720 }, some { target := 23, numerator := 130418917420026195367302266880 }, some { target := 24, numerator := 235353678562576007731798343680 }, some { target := 25, numerator := 3674215708005565572933998346240 }, some { target := 26, numerator := 143910529566925456957023191040 }, some { target := 27, numerator := 239850882611542428261705318400 }, some { target := 28, numerator := 229357406497287447025255710720 }, some { target := 29, numerator := 7495340081610700883178291200 }, some { target := 30, numerator := 143910529566925456957023191040 }, some { target := 31, numerator := 7495340081610700883178291200 }, some { target := 32, numerator := 230856474513609587201891368960 }, some { target := 33, numerator := 130418917420026195367302266880 }, some { target := 34, numerator := 8994408097932841059813949440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 8994408097932841059813949440 }, some { target := 127, numerator := 239850882611542428261705318400 }, some { target := 128, numerator := 229357406497287447025255710720 }, some { target := 129, numerator := 7495340081610700883178291200 }, some { target := 130, numerator := 235353678562576007731798343680 }, some { target := 131, numerator := 7495340081610700883178291200 }, some { target := 132, numerator := 229357406497287447025255710720 }, some { target := 133, numerator := 130418917420026195367302266880 }, some { target := 134, numerator := 235353678562576007731798343680 }, some { target := 135, numerator := 3674215708005565572933998346240 }, some { target := 136, numerator := 143910529566925456957023191040 }, some { target := 137, numerator := 239850882611542428261705318400 }, some { target := 138, numerator := 229357406497287447025255710720 }, some { target := 139, numerator := 7495340081610700883178291200 }, some { target := 140, numerator := 143910529566925456957023191040 }, some { target := 141, numerator := 7495340081610700883178291200 }, some { target := 142, numerator := 230856474513609587201891368960 }, some { target := 143, numerator := 130418917420026195367302266880 }, some { target := 144, numerator := 8994408097932841059813949440 }]

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

end Slot28

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 27, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 0, numerator := 18278958392573193121557381120 }, some { target := 1, numerator := 18801214346646712925030449152 }, some { target := 2, numerator := 18278958392573193121557381120 }, some { target := 3, numerator := 16189934576279113907665108992 }, some { target := 4, numerator := 757793389360677234839421714432 }, some { target := 5, numerator := 206291101859040322371861872640 }, some { target := 6, numerator := 18801214346646712925030449152 }, some { target := 7, numerator := 757793389360677234839421714432 }, some { target := 8, numerator := 18278958392573193121557381120 }, some { target := 9, numerator := 18278958392573193121557381120 }, some { target := 10, numerator := 15667678622205594104192040960 }, some { target := 11, numerator := 18278958392573193121557381120 }, some { target := 12, numerator := 206291101859040322371861872640 }, some { target := 13, numerator := 15667678622205594104192040960 }, some { target := 14, numerator := 18278958392573193121557381120 }, some { target := 15, numerator := 16189934576279113907665108992 }]

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

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1
