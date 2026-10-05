import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 2296, #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 56, numerator := 3319631975786434742986997760 }, some { target := 57, numerator := 48134663648903303773311467520 }, some { target := 58, numerator := 85203887378518491736666275840 }, some { target := 59, numerator := 2766359979822028952489164800 }, some { target := 60, numerator := 53114111612582955887791964160 }, some { target := 61, numerator := 2766359979822028952489164800 }, some { target := 62, numerator := 84650615382554085946168442880 }, some { target := 63, numerator := 88523519354304926479653273600 }, some { target := 64, numerator := 53114111612582955887791964160 }, some { target := 65, numerator := 1356069662108758592510188584960 }, some { target := 66, numerator := 86863703366411709108159774720 }, some { target := 67, numerator := 48134663648903303773311467520 }, some { target := 68, numerator := 84650615382554085946168442880 }, some { target := 69, numerator := 2766359979822028952489164800 }, some { target := 70, numerator := 86863703366411709108159774720 }, some { target := 71, numerator := 2766359979822028952489164800 }, some { target := 72, numerator := 84650615382554085946168442880 }, some { target := 73, numerator := 88523519354304926479653273600 }, some { target := 74, numerator := 3319631975786434742986997760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 129913664752302617343031246848 }, some { target := 153, numerator := 1883748138908387951473953079296 }, some { target := 154, numerator := 3334450728642433845137802002432 }, some { target := 155, numerator := 108261387293585514452526039040 }, some { target := 156, numerator := 2078618636036841877488499949568 }, some { target := 157, numerator := 108261387293585514452526039040 }, some { target := 158, numerator := 3312798451183716742247296794624 }, some { target := 159, numerator := 3464364393394736462480833249280 }, some { target := 160, numerator := 2078618636036841877488499949568 }, some { target := 161, numerator := 53069732051315619184628264337408 }, some { target := 162, numerator := 3399407561018585153809317625856 }, some { target := 163, numerator := 1883748138908387951473953079296 }, some { target := 164, numerator := 3312798451183716742247296794624 }, some { target := 165, numerator := 108261387293585514452526039040 }, some { target := 166, numerator := 3399407561018585153809317625856 }, some { target := 167, numerator := 108261387293585514452526039040 }, some { target := 168, numerator := 3312798451183716742247296794624 }, some { target := 169, numerator := 3464364393394736462480833249280 }, some { target := 170, numerator := 129913664752302617343031246848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 129913664752302617343031246848 }, some { target := 284, numerator := 1883748138908387951473953079296 }, some { target := 285, numerator := 3334450728642433845137802002432 }, some { target := 286, numerator := 108261387293585514452526039040 }, some { target := 287, numerator := 2078618636036841877488499949568 }, some { target := 288, numerator := 108261387293585514452526039040 }, some { target := 289, numerator := 3312798451183716742247296794624 }, some { target := 290, numerator := 3464364393394736462480833249280 }, some { target := 291, numerator := 2078618636036841877488499949568 }, some { target := 292, numerator := 53069732051315619184628264337408 }, some { target := 293, numerator := 3399407561018585153809317625856 }, some { target := 294, numerator := 1883748138908387951473953079296 }, some { target := 295, numerator := 3312798451183716742247296794624 }, some { target := 296, numerator := 108261387293585514452526039040 }, some { target := 297, numerator := 3399407561018585153809317625856 }, some { target := 298, numerator := 108261387293585514452526039040 }, some { target := 299, numerator := 3312798451183716742247296794624 }, some { target := 300, numerator := 3464364393394736462480833249280 }, some { target := 301, numerator := 129913664752302617343031246848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 3319631975786434742986997760 }, some { target := 661, numerator := 48134663648903303773311467520 }, some { target := 662, numerator := 85203887378518491736666275840 }, some { target := 663, numerator := 2766359979822028952489164800 }, some { target := 664, numerator := 53114111612582955887791964160 }, some { target := 665, numerator := 2766359979822028952489164800 }, some { target := 666, numerator := 84650615382554085946168442880 }, some { target := 667, numerator := 88523519354304926479653273600 }, some { target := 668, numerator := 53114111612582955887791964160 }, some { target := 669, numerator := 1356069662108758592510188584960 }, some { target := 670, numerator := 86863703366411709108159774720 }, some { target := 671, numerator := 48134663648903303773311467520 }, some { target := 672, numerator := 84650615382554085946168442880 }, some { target := 673, numerator := 2766359979822028952489164800 }, some { target := 674, numerator := 86863703366411709108159774720 }, some { target := 675, numerator := 2766359979822028952489164800 }, some { target := 676, numerator := 84650615382554085946168442880 }, some { target := 677, numerator := 88523519354304926479653273600 }, some { target := 678, numerator := 3319631975786434742986997760 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 321, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 141527497263939969808859136 }, some { target := 111, numerator := 159789109814125772364840960 }, some { target := 112, numerator := 136962094126393519169863680 }, some { target := 113, numerator := 1803334239330848002403205120 }, some { target := 114, numerator := 159789109814125772364840960 }, some { target := 115, numerator := 136962094126393519169863680 }, some { target := 116, numerator := 159789109814125772364840960 }, some { target := 117, numerator := 159789109814125772364840960 }, some { target := 118, numerator := 6624399952579899877182406656 }, some { target := 119, numerator := 164354512951672223003836416 }, some { target := 120, numerator := 1803334239330848002403205120 }, some { target := 121, numerator := 6624399952579899877182406656 }, some { target := 122, numerator := 141527497263939969808859136 }, some { target := 123, numerator := 159789109814125772364840960 }, some { target := 124, numerator := 164354512951672223003836416 }, some { target := 125, numerator := 159789109814125772364840960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 16727641537023830886853902336 }, some { target := 207, numerator := 18886046896639809065802792960 }, some { target := 208, numerator := 16188040197119836342116679680 }, some { target := 209, numerator := 213142529262077845171202949120 }, some { target := 210, numerator := 18886046896639809065802792960 }, some { target := 211, numerator := 16188040197119836342116679680 }, some { target := 212, numerator := 18886046896639809065802792960 }, some { target := 213, numerator := 18886046896639809065802792960 }, some { target := 214, numerator := 782961544200696084413710073856 }, some { target := 215, numerator := 19425648236543803610540015616 }, some { target := 216, numerator := 213142529262077845171202949120 }, some { target := 217, numerator := 782961544200696084413710073856 }, some { target := 218, numerator := 16727641537023830886853902336 }, some { target := 219, numerator := 18886046896639809065802792960 }, some { target := 220, numerator := 19425648236543803610540015616 }, some { target := 221, numerator := 18886046896639809065802792960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 158741983754465364623958736896 }, some { target := 303, numerator := 179224820367944766510921154560 }, some { target := 304, numerator := 153621274601095514152218132480 }, some { target := 305, numerator := 2022680115581090936337538744320 }, some { target := 306, numerator := 179224820367944766510921154560 }, some { target := 307, numerator := 153621274601095514152218132480 }, some { target := 308, numerator := 179224820367944766510921154560 }, some { target := 309, numerator := 179224820367944766510921154560 }, some { target := 310, numerator := 7430148981539653034495617007616 }, some { target := 311, numerator := 184345529521314616982661758976 }, some { target := 312, numerator := 2022680115581090936337538744320 }, some { target := 313, numerator := 7430148981539653034495617007616 }, some { target := 314, numerator := 158741983754465364623958736896 }, some { target := 315, numerator := 179224820367944766510921154560 }, some { target := 316, numerator := 184345529521314616982661758976 }, some { target := 317, numerator := 179224820367944766510921154560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 16727653009745723229588160512 }, some { target := 680, numerator := 18886059849712913323728568320 }, some { target := 681, numerator := 16188051299753925706053058560 }, some { target := 682, numerator := 213142675446760021796365271040 }, some { target := 683, numerator := 18886059849712913323728568320 }, some { target := 684, numerator := 16188051299753925706053058560 }, some { target := 685, numerator := 18886059849712913323728568320 }, some { target := 686, numerator := 18886059849712913323728568320 }, some { target := 687, numerator := 782962081198098206649432932352 }, some { target := 688, numerator := 19425661559704710847263670272 }, some { target := 689, numerator := 213142675446760021796365271040 }, some { target := 690, numerator := 782962081198098206649432932352 }, some { target := 691, numerator := 16727653009745723229588160512 }, some { target := 692, numerator := 18886059849712913323728568320 }, some { target := 693, numerator := 19425661559704710847263670272 }, some { target := 694, numerator := 18886059849712913323728568320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 141527497263939969808859136 }, some { target := 967, numerator := 159789109814125772364840960 }, some { target := 968, numerator := 136962094126393519169863680 }, some { target := 969, numerator := 1803334239330848002403205120 }, some { target := 970, numerator := 159789109814125772364840960 }, some { target := 971, numerator := 136962094126393519169863680 }, some { target := 972, numerator := 159789109814125772364840960 }, some { target := 973, numerator := 159789109814125772364840960 }, some { target := 974, numerator := 6624399952579899877182406656 }, some { target := 975, numerator := 164354512951672223003836416 }, some { target := 976, numerator := 1803334239330848002403205120 }, some { target := 977, numerator := 6624399952579899877182406656 }, some { target := 978, numerator := 141527497263939969808859136 }, some { target := 979, numerator := 159789109814125772364840960 }, some { target := 980, numerator := 164354512951672223003836416 }, some { target := 981, numerator := 159789109814125772364840960 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 3, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 16320498564797493858533376 }, some { target := 258, numerator := 340690407540147684296884224 }, some { target := 259, numerator := 17680540111863951680077824 }, some { target := 260, numerator := 366531196934410382906228736 }, some { target := 261, numerator := 548776764241315730993184768 }, some { target := 262, numerator := 17000519338330722769305600 }, some { target := 263, numerator := 548776764241315730993184768 }, some { target := 264, numerator := 571897470541445513959440384 }, some { target := 265, numerator := 340690407540147684296884224 }, some { target := 266, numerator := 17000519338330722769305600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 12240373923598120393900032 }, some { target := 354, numerator := 255517805655110763222663168 }, some { target := 355, numerator := 13260405083897963760058368 }, some { target := 356, numerator := 274898397700807787179671552 }, some { target := 357, numerator := 411582573180986798244888576 }, some { target := 358, numerator := 12750389503748042076979200 }, some { target := 359, numerator := 411582573180986798244888576 }, some { target := 360, numerator := 428923102906084135469580288 }, some { target := 361, numerator := 255517805655110763222663168 }, some { target := 362, numerator := 12750389503748042076979200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 12920394697131349304672256 }, some { target := 380, numerator := 269713239302616916735033344 }, some { target := 381, numerator := 13997094255225628413394944 }, some { target := 382, numerator := 290170530906408219800764416 }, some { target := 383, numerator := 434448271691041620369604608 }, some { target := 384, numerator := 13458744476178488859033600 }, some { target := 385, numerator := 434448271691041620369604608 }, some { target := 386, numerator := 452752164178644365217890304 }, some { target := 387, numerator := 269713239302616916735033344 }, some { target := 388, numerator := 13458744476178488859033600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 16660508951564108313919488 }, some { target := 525, numerator := 347788124363900761053069312 }, some { target := 526, numerator := 18048884697527784006746112 }, some { target := 527, numerator := 374167263537210599216775168 }, some { target := 528, numerator := 560209613496343142055542784 }, some { target := 529, numerator := 17354696824545946160332800 }, some { target := 530, numerator := 560209613496343142055542784 }, some { target := 531, numerator := 583812001177725628833595392 }, some { target := 532, numerator := 347788124363900761053069312 }, some { target := 533, numerator := 17354696824545946160332800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 223046813718899082733289472 }, some { target := 621, numerator := 4656102236382018352057417728 }, some { target := 622, numerator := 241634048195474006294396928 }, some { target := 623, numerator := 5009259691436941899718459392 }, some { target := 624, numerator := 7499949111297981656906858496 }, some { target := 625, numerator := 232340430957186544513843200 }, some { target := 626, numerator := 7499949111297981656906858496 }, some { target := 627, numerator := 7815932097399755357445685248 }, some { target := 628, numerator := 4656102236382018352057417728 }, some { target := 629, numerator := 232340430957186544513843200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 389991913621306780327870464 }, some { target := 647, numerator := 8141081196844779039344295936 }, some { target := 648, numerator := 422491239756415678688526336 }, some { target := 649, numerator := 8758568393411848108196757504 }, some { target := 650, numerator := 13113478095516440488524644352 }, some { target := 651, numerator := 406241576688861229508198400 }, some { target := 652, numerator := 13113478095516440488524644352 }, some { target := 653, numerator := 13665966639813291760655794176 }, some { target := 654, numerator := 8141081196844779039344295936 }, some { target := 655, numerator := 406241576688861229508198400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 11900363536831505938513920 }, some { target := 696, numerator := 248420088831357686466478080 }, some { target := 697, numerator := 12892060498234131433390080 }, some { target := 698, numerator := 267262331098007570869125120 }, some { target := 699, numerator := 400149723925959387182530560 }, some { target := 700, numerator := 12396212017532818685952000 }, some { target := 701, numerator := 400149723925959387182530560 }, some { target := 702, numerator := 417008572269804020595425280 }, some { target := 703, numerator := 248420088831357686466478080 }, some { target := 704, numerator := 12396212017532818685952000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 223046813718899082733289472 }, some { target := 722, numerator := 4656102236382018352057417728 }, some { target := 723, numerator := 241634048195474006294396928 }, some { target := 724, numerator := 5009259691436941899718459392 }, some { target := 725, numerator := 7499949111297981656906858496 }, some { target := 726, numerator := 232340430957186544513843200 }, some { target := 727, numerator := 7499949111297981656906858496 }, some { target := 728, numerator := 7815932097399755357445685248 }, some { target := 729, numerator := 4656102236382018352057417728 }, some { target := 730, numerator := 232340430957186544513843200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 12580384310364734849286144 }, some { target := 736, numerator := 262615522478863839978848256 }, some { target := 737, numerator := 13628749669561796086726656 }, some { target := 738, numerator := 282534464303608003490217984 }, some { target := 739, numerator := 423015422436014209307246592 }, some { target := 740, numerator := 13104566989963265468006400 }, some { target := 741, numerator := 423015422436014209307246592 }, some { target := 742, numerator := 440837633542364250343735296 }, some { target := 743, numerator := 262615522478863839978848256 }, some { target := 744, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 12920394697131349304672256 }, some { target := 837, numerator := 269713239302616916735033344 }, some { target := 838, numerator := 13997094255225628413394944 }, some { target := 839, numerator := 290170530906408219800764416 }, some { target := 840, numerator := 434448271691041620369604608 }, some { target := 841, numerator := 13458744476178488859033600 }, some { target := 842, numerator := 434448271691041620369604608 }, some { target := 843, numerator := 452752164178644365217890304 }, some { target := 844, numerator := 269713239302616916735033344 }, some { target := 845, numerator := 13458744476178488859033600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 12920394697131349304672256 }, some { target := 863, numerator := 269713239302616916735033344 }, some { target := 864, numerator := 13997094255225628413394944 }, some { target := 865, numerator := 290170530906408219800764416 }, some { target := 866, numerator := 434448271691041620369604608 }, some { target := 867, numerator := 13458744476178488859033600 }, some { target := 868, numerator := 434448271691041620369604608 }, some { target := 869, numerator := 452752164178644365217890304 }, some { target := 870, numerator := 269713239302616916735033344 }, some { target := 871, numerator := 13458744476178488859033600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 12580384310364734849286144 }, some { target := 912, numerator := 262615522478863839978848256 }, some { target := 913, numerator := 13628749669561796086726656 }, some { target := 914, numerator := 282534464303608003490217984 }, some { target := 915, numerator := 423015422436014209307246592 }, some { target := 916, numerator := 13104566989963265468006400 }, some { target := 917, numerator := 423015422436014209307246592 }, some { target := 918, numerator := 440837633542364250343735296 }, some { target := 919, numerator := 262615522478863839978848256 }, some { target := 920, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 389991913621306780327870464 }, some { target := 938, numerator := 8141081196844779039344295936 }, some { target := 939, numerator := 422491239756415678688526336 }, some { target := 940, numerator := 8758568393411848108196757504 }, some { target := 941, numerator := 13113478095516440488524644352 }, some { target := 942, numerator := 406241576688861229508198400 }, some { target := 943, numerator := 13113478095516440488524644352 }, some { target := 944, numerator := 13665966639813291760655794176 }, some { target := 945, numerator := 8141081196844779039344295936 }, some { target := 946, numerator := 406241576688861229508198400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 12580384310364734849286144 }, some { target := 952, numerator := 262615522478863839978848256 }, some { target := 953, numerator := 13628749669561796086726656 }, some { target := 954, numerator := 282534464303608003490217984 }, some { target := 955, numerator := 423015422436014209307246592 }, some { target := 956, numerator := 13104566989963265468006400 }, some { target := 957, numerator := 423015422436014209307246592 }, some { target := 958, numerator := 440837633542364250343735296 }, some { target := 959, numerator := 262615522478863839978848256 }, some { target := 960, numerator := 13104566989963265468006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 16320498564797493858533376 }, some { target := 983, numerator := 340690407540147684296884224 }, some { target := 984, numerator := 17680540111863951680077824 }, some { target := 985, numerator := 366531196934410382906228736 }, some { target := 986, numerator := 548776764241315730993184768 }, some { target := 987, numerator := 17000519338330722769305600 }, some { target := 988, numerator := 548776764241315730993184768 }, some { target := 989, numerator := 571897470541445513959440384 }, some { target := 990, numerator := 340690407540147684296884224 }, some { target := 991, numerator := 17000519338330722769305600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 16660508951564108313919488 }, some { target := 997, numerator := 347788124363900761053069312 }, some { target := 998, numerator := 18048884697527784006746112 }, some { target := 999, numerator := 374167263537210599216775168 }, some { target := 1000, numerator := 560209613496343142055542784 }, some { target := 1001, numerator := 17354696824545946160332800 }, some { target := 1002, numerator := 560209613496343142055542784 }, some { target := 1003, numerator := 583812001177725628833595392 }, some { target := 1004, numerator := 347788124363900761053069312 }, some { target := 1005, numerator := 17354696824545946160332800 }]

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

end Slot25

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3
