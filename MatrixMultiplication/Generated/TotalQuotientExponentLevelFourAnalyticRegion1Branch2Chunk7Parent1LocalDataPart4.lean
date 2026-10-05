import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 1323, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 8304875610015859925990768640 }, some { target := 30, numerator := 695360050213770036766555766784 }, some { target := 35, numerator := 695360301863957704536666144768 }, some { target := 43, numerator := 8304623959828192155880390656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 300971441030534992002684026880 }, some { target := 105, numerator := 25200078384738608770369431011328 }, some { target := 110, numerator := 25200087504624706357410247213056 }, some { target := 118, numerator := 300962321144437404961867825152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 300971551636364936810279731200 }, some { target := 227, numerator := 25200087645669064080372761886720 }, some { target := 232, numerator := 25200096765558513189961271869440 }, some { target := 240, numerator := 300962431746915827221769748480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 8304765004185915118395064320 }, some { target := 625, numerator := 695350789283314726763224891392 }, some { target := 630, numerator := 695351040930150871985641488384 }, some { target := 638, numerator := 8304513357349769895978467328 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 55, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 69184159826222285218004336640 }, some { target := 7, numerator := 670122828442648862695442350080 }, some { target := 12, numerator := 69184159826222285218004336640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 234515617181213788345718538240 }, some { target := 96, numerator := 2271535407731924124690578145280 }, some { target := 101, numerator := 234515617181213788345718538240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 69184159826222285218004336640 }, some { target := 218, numerator := 670122828442648862695442350080 }, some { target := 223, numerator := 69184159826222285218004336640 }]

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

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 9903520314283042199192993792 }, some { target := 2, numerator := 9903520314283042199192993792 }, some { target := 3, numerator := 9903520314283042199192993792 }, some { target := 4, numerator := 9903520314283042199192993792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 9903520314283042199192993792 }, some { target := 91, numerator := 9903520314283042199192993792 }, some { target := 92, numerator := 9903520314283042199192993792 }, some { target := 93, numerator := 9903520314283042199192993792 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 23, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 234607166868963974216417280 }, some { target := 201, numerator := 229719517559193891420241920 }, some { target := 202, numerator := 180843024461493063458488320 }, some { target := 203, numerator := 5684336147262606291951943680 }, some { target := 204, numerator := 180843024461493063458488320 }, some { target := 205, numerator := 180843024461493063458488320 }, some { target := 206, numerator := 185730673771263146254663680 }, some { target := 207, numerator := 185730673771263146254663680 }, some { target := 208, numerator := 3142758506182163237940756480 }, some { target := 209, numerator := 171067725841952897866137600 }, some { target := 210, numerator := 5684336147262606291951943680 }, some { target := 211, numerator := 3142758506182163237940756480 }, some { target := 212, numerator := 234607166868963974216417280 }, some { target := 213, numerator := 180843024461493063458488320 }, some { target := 214, numerator := 171067725841952897866137600 }, some { target := 215, numerator := 229719517559193891420241920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 182472240898083091057213440 }, some { target := 297, numerator := 178670735879373026660188160 }, some { target := 298, numerator := 140655685692272382689935360 }, some { target := 299, numerator := 4421150336759804893740400640 }, some { target := 300, numerator := 140655685692272382689935360 }, some { target := 301, numerator := 140655685692272382689935360 }, some { target := 302, numerator := 144457190710982447086960640 }, some { target := 303, numerator := 144457190710982447086960640 }, some { target := 304, numerator := 2444367727030571407287255040 }, some { target := 305, numerator := 133052675654852253895884800 }, some { target := 306, numerator := 4421150336759804893740400640 }, some { target := 307, numerator := 2444367727030571407287255040 }, some { target := 308, numerator := 182472240898083091057213440 }, some { target := 309, numerator := 140655685692272382689935360 }, some { target := 310, numerator := 133052675654852253895884800 }, some { target := 311, numerator := 178670735879373026660188160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 208539703883523532636815360 }, some { target := 332, numerator := 204195126719283459040215040 }, some { target := 333, numerator := 160749355076882723074211840 }, some { target := 334, numerator := 5052743242011205592846172160 }, some { target := 335, numerator := 160749355076882723074211840 }, some { target := 336, numerator := 160749355076882723074211840 }, some { target := 337, numerator := 165093932241122796670812160 }, some { target := 338, numerator := 165093932241122796670812160 }, some { target := 339, numerator := 2793563116606367322614005760 }, some { target := 340, numerator := 152060200748402575881011200 }, some { target := 341, numerator := 5052743242011205592846172160 }, some { target := 342, numerator := 2793563116606367322614005760 }, some { target := 343, numerator := 208539703883523532636815360 }, some { target := 344, numerator := 160749355076882723074211840 }, some { target := 345, numerator := 152060200748402575881011200 }, some { target := 346, numerator := 204195126719283459040215040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 245034152063140150848258048 }, some { target := 468, numerator := 239929273895158064372252672 }, some { target := 469, numerator := 188880492215337199612198912 }, some { target := 470, numerator := 5936973309363166571594252288 }, some { target := 471, numerator := 188880492215337199612198912 }, some { target := 472, numerator := 188880492215337199612198912 }, some { target := 473, numerator := 193985370383319286088204288 }, some { target := 474, numerator := 193985370383319286088204288 }, some { target := 475, numerator := 3282436662012481604071456768 }, some { target := 476, numerator := 178670735879373026660188160 }, some { target := 477, numerator := 5936973309363166571594252288 }, some { target := 478, numerator := 3282436662012481604071456768 }, some { target := 479, numerator := 245034152063140150848258048 }, some { target := 480, numerator := 188880492215337199612198912 }, some { target := 481, numerator := 178670735879373026660188160 }, some { target := 482, numerator := 239929273895158064372252672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 2893488391383889015335813120 }, some { target := 564, numerator := 2833207383230057994182983680 }, some { target := 565, numerator := 2230397301691747782654689280 }, some { target := 566, numerator := 70106812482905477600740638720 }, some { target := 567, numerator := 2230397301691747782654689280 }, some { target := 568, numerator := 2230397301691747782654689280 }, some { target := 569, numerator := 2290678309845578803807518720 }, some { target := 570, numerator := 2290678309845578803807518720 }, some { target := 571, numerator := 38760688242913346601269329920 }, some { target := 572, numerator := 2109835285384085740349030400 }, some { target := 573, numerator := 70106812482905477600740638720 }, some { target := 574, numerator := 38760688242913346601269329920 }, some { target := 575, numerator := 2893488391383889015335813120 }, some { target := 576, numerator := 2230397301691747782654689280 }, some { target := 577, numerator := 2109835285384085740349030400 }, some { target := 578, numerator := 2833207383230057994182983680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 6506438761165934218268639232 }, some { target := 599, numerator := 6370887953641643922054709248 }, some { target := 600, numerator := 5015379878398740959915409408 }, some { target := 601, numerator := 157645589150749614496800571392 }, some { target := 602, numerator := 5015379878398740959915409408 }, some { target := 603, numerator := 5015379878398740959915409408 }, some { target := 604, numerator := 5150930685923031256129339392 }, some { target := 605, numerator := 5150930685923031256129339392 }, some { target := 606, numerator := 87159169238118660465556979712 }, some { target := 607, numerator := 4744278263350160367487549440 }, some { target := 608, numerator := 157645589150749614496800571392 }, some { target := 609, numerator := 87159169238118660465556979712 }, some { target := 610, numerator := 6506438761165934218268639232 }, some { target := 611, numerator := 5015379878398740959915409408 }, some { target := 612, numerator := 4744278263350160367487549440 }, some { target := 613, numerator := 6370887953641643922054709248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 182472240898083091057213440 }, some { target := 660, numerator := 178670735879373026660188160 }, some { target := 661, numerator := 140655685692272382689935360 }, some { target := 662, numerator := 4421150336759804893740400640 }, some { target := 663, numerator := 140655685692272382689935360 }, some { target := 664, numerator := 140655685692272382689935360 }, some { target := 665, numerator := 144457190710982447086960640 }, some { target := 666, numerator := 144457190710982447086960640 }, some { target := 667, numerator := 2444367727030571407287255040 }, some { target := 668, numerator := 133052675654852253895884800 }, some { target := 669, numerator := 4421150336759804893740400640 }, some { target := 670, numerator := 2444367727030571407287255040 }, some { target := 671, numerator := 182472240898083091057213440 }, some { target := 672, numerator := 140655685692272382689935360 }, some { target := 673, numerator := 133052675654852253895884800 }, some { target := 674, numerator := 178670735879373026660188160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 2893488391383889015335813120 }, some { target := 695, numerator := 2833207383230057994182983680 }, some { target := 696, numerator := 2230397301691747782654689280 }, some { target := 697, numerator := 70106812482905477600740638720 }, some { target := 698, numerator := 2230397301691747782654689280 }, some { target := 699, numerator := 2230397301691747782654689280 }, some { target := 700, numerator := 2290678309845578803807518720 }, some { target := 701, numerator := 2290678309845578803807518720 }, some { target := 702, numerator := 38760688242913346601269329920 }, some { target := 703, numerator := 2109835285384085740349030400 }, some { target := 704, numerator := 70106812482905477600740638720 }, some { target := 705, numerator := 38760688242913346601269329920 }, some { target := 706, numerator := 2893488391383889015335813120 }, some { target := 707, numerator := 2230397301691747782654689280 }, some { target := 708, numerator := 2109835285384085740349030400 }, some { target := 709, numerator := 2833207383230057994182983680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 208539703883523532636815360 }, some { target := 721, numerator := 204195126719283459040215040 }, some { target := 722, numerator := 160749355076882723074211840 }, some { target := 723, numerator := 5052743242011205592846172160 }, some { target := 724, numerator := 160749355076882723074211840 }, some { target := 725, numerator := 160749355076882723074211840 }, some { target := 726, numerator := 165093932241122796670812160 }, some { target := 727, numerator := 165093932241122796670812160 }, some { target := 728, numerator := 2793563116606367322614005760 }, some { target := 729, numerator := 152060200748402575881011200 }, some { target := 730, numerator := 5052743242011205592846172160 }, some { target := 731, numerator := 2793563116606367322614005760 }, some { target := 732, numerator := 208539703883523532636815360 }, some { target := 733, numerator := 160749355076882723074211840 }, some { target := 734, numerator := 152060200748402575881011200 }, some { target := 735, numerator := 204195126719283459040215040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 203326211286435444320894976 }, some { target := 831, numerator := 199090248551301372564209664 }, some { target := 832, numerator := 156730621199960654997356544 }, some { target := 833, numerator := 4926424660960925453025017856 }, some { target := 834, numerator := 156730621199960654997356544 }, some { target := 835, numerator := 156730621199960654997356544 }, some { target := 836, numerator := 160966583935094726754041856 }, some { target := 837, numerator := 160966583935094726754041856 }, some { target := 838, numerator := 2723724038691208139548655616 }, some { target := 839, numerator := 148258695729692511483985920 }, some { target := 840, numerator := 4926424660960925453025017856 }, some { target := 841, numerator := 2723724038691208139548655616 }, some { target := 842, numerator := 203326211286435444320894976 }, some { target := 843, numerator := 156730621199960654997356544 }, some { target := 844, numerator := 148258695729692511483985920 }, some { target := 845, numerator := 199090248551301372564209664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 203326211286435444320894976 }, some { target := 866, numerator := 199090248551301372564209664 }, some { target := 867, numerator := 156730621199960654997356544 }, some { target := 868, numerator := 4926424660960925453025017856 }, some { target := 869, numerator := 156730621199960654997356544 }, some { target := 870, numerator := 156730621199960654997356544 }, some { target := 871, numerator := 160966583935094726754041856 }, some { target := 872, numerator := 160966583935094726754041856 }, some { target := 873, numerator := 2723724038691208139548655616 }, some { target := 874, numerator := 148258695729692511483985920 }, some { target := 875, numerator := 4926424660960925453025017856 }, some { target := 876, numerator := 2723724038691208139548655616 }, some { target := 877, numerator := 203326211286435444320894976 }, some { target := 878, numerator := 156730621199960654997356544 }, some { target := 879, numerator := 148258695729692511483985920 }, some { target := 880, numerator := 199090248551301372564209664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 203326211286435444320894976 }, some { target := 927, numerator := 199090248551301372564209664 }, some { target := 928, numerator := 156730621199960654997356544 }, some { target := 929, numerator := 4926424660960925453025017856 }, some { target := 930, numerator := 156730621199960654997356544 }, some { target := 931, numerator := 156730621199960654997356544 }, some { target := 932, numerator := 160966583935094726754041856 }, some { target := 933, numerator := 160966583935094726754041856 }, some { target := 934, numerator := 2723724038691208139548655616 }, some { target := 935, numerator := 148258695729692511483985920 }, some { target := 936, numerator := 4926424660960925453025017856 }, some { target := 937, numerator := 2723724038691208139548655616 }, some { target := 938, numerator := 203326211286435444320894976 }, some { target := 939, numerator := 156730621199960654997356544 }, some { target := 940, numerator := 148258695729692511483985920 }, some { target := 941, numerator := 199090248551301372564209664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 6506438761165934218268639232 }, some { target := 962, numerator := 6370887953641643922054709248 }, some { target := 963, numerator := 5015379878398740959915409408 }, some { target := 964, numerator := 157645589150749614496800571392 }, some { target := 965, numerator := 5015379878398740959915409408 }, some { target := 966, numerator := 5015379878398740959915409408 }, some { target := 967, numerator := 5150930685923031256129339392 }, some { target := 968, numerator := 5150930685923031256129339392 }, some { target := 969, numerator := 87159169238118660465556979712 }, some { target := 970, numerator := 4744278263350160367487549440 }, some { target := 971, numerator := 157645589150749614496800571392 }, some { target := 972, numerator := 87159169238118660465556979712 }, some { target := 973, numerator := 6506438761165934218268639232 }, some { target := 974, numerator := 5015379878398740959915409408 }, some { target := 975, numerator := 4744278263350160367487549440 }, some { target := 976, numerator := 6370887953641643922054709248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 203326211286435444320894976 }, some { target := 988, numerator := 199090248551301372564209664 }, some { target := 989, numerator := 156730621199960654997356544 }, some { target := 990, numerator := 4926424660960925453025017856 }, some { target := 991, numerator := 156730621199960654997356544 }, some { target := 992, numerator := 156730621199960654997356544 }, some { target := 993, numerator := 160966583935094726754041856 }, some { target := 994, numerator := 160966583935094726754041856 }, some { target := 995, numerator := 2723724038691208139548655616 }, some { target := 996, numerator := 148258695729692511483985920 }, some { target := 997, numerator := 4926424660960925453025017856 }, some { target := 998, numerator := 2723724038691208139548655616 }, some { target := 999, numerator := 203326211286435444320894976 }, some { target := 1000, numerator := 156730621199960654997356544 }, some { target := 1001, numerator := 148258695729692511483985920 }, some { target := 1002, numerator := 199090248551301372564209664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 234607166868963974216417280 }, some { target := 1037, numerator := 229719517559193891420241920 }, some { target := 1038, numerator := 180843024461493063458488320 }, some { target := 1039, numerator := 5684336147262606291951943680 }, some { target := 1040, numerator := 180843024461493063458488320 }, some { target := 1041, numerator := 180843024461493063458488320 }, some { target := 1042, numerator := 185730673771263146254663680 }, some { target := 1043, numerator := 185730673771263146254663680 }, some { target := 1044, numerator := 3142758506182163237940756480 }, some { target := 1045, numerator := 171067725841952897866137600 }, some { target := 1046, numerator := 5684336147262606291951943680 }, some { target := 1047, numerator := 3142758506182163237940756480 }, some { target := 1048, numerator := 234607166868963974216417280 }, some { target := 1049, numerator := 180843024461493063458488320 }, some { target := 1050, numerator := 171067725841952897866137600 }, some { target := 1051, numerator := 229719517559193891420241920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 245034152063140150848258048 }, some { target := 1063, numerator := 239929273895158064372252672 }, some { target := 1064, numerator := 188880492215337199612198912 }, some { target := 1065, numerator := 5936973309363166571594252288 }, some { target := 1066, numerator := 188880492215337199612198912 }, some { target := 1067, numerator := 188880492215337199612198912 }, some { target := 1068, numerator := 193985370383319286088204288 }, some { target := 1069, numerator := 193985370383319286088204288 }, some { target := 1070, numerator := 3282436662012481604071456768 }, some { target := 1071, numerator := 178670735879373026660188160 }, some { target := 1072, numerator := 5936973309363166571594252288 }, some { target := 1073, numerator := 3282436662012481604071456768 }, some { target := 1074, numerator := 245034152063140150848258048 }, some { target := 1075, numerator := 188880492215337199612198912 }, some { target := 1076, numerator := 178670735879373026660188160 }, some { target := 1077, numerator := 239929273895158064372252672 }]

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

end Slot18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
