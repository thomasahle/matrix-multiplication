import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[67070209294336, 73667279060992, 67070209294336, 73667279060992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 0, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 56, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 110536247797089048421466112 }, some { target := 201, numerator := 125888504435573638480003072 }, some { target := 202, numerator := 98254442486301376374636544 }, some { target := 203, numerator := 1317223619581977827022471168 }, some { target := 204, numerator := 116677150452482884444880896 }, some { target := 205, numerator := 98254442486301376374636544 }, some { target := 206, numerator := 116677150452482884444880896 }, some { target := 207, numerator := 113606699124785966433173504 }, some { target := 208, numerator := 4292490956120291380366934016 }, some { target := 209, numerator := 113606699124785966433173504 }, some { target := 210, numerator := 1317223619581977827022471168 }, some { target := 211, numerator := 4292490956120291380366934016 }, some { target := 212, numerator := 110536247797089048421466112 }, some { target := 213, numerator := 113606699124785966433173504 }, some { target := 214, numerator := 113606699124785966433173504 }, some { target := 215, numerator := 125888504435573638480003072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 19387019370947650281239740416 }, some { target := 297, numerator := 22079660950245935042523037696 }, some { target := 298, numerator := 17232906107509022472213102592 }, some { target := 299, numerator := 231028647503792832518106906624 }, some { target := 300, numerator := 20464076002666964185753059328 }, some { target := 301, numerator := 17232906107509022472213102592 }, some { target := 302, numerator := 20464076002666964185753059328 }, some { target := 303, numerator := 19925547686807307233496399872 }, some { target := 304, numerator := 752862585571800419254809919488 }, some { target := 305, numerator := 19925547686807307233496399872 }, some { target := 306, numerator := 231028647503792832518106906624 }, some { target := 307, numerator := 752862585571800419254809919488 }, some { target := 308, numerator := 19387019370947650281239740416 }, some { target := 309, numerator := 19925547686807307233496399872 }, some { target := 310, numerator := 19925547686807307233496399872 }, some { target := 311, numerator := 22079660950245935042523037696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 19387021695237403568643244032 }, some { target := 660, numerator := 22079663597353709619843694592 }, some { target := 661, numerator := 17232908173544358727682883584 }, some { target := 662, numerator := 231028675201579059192998658048 }, some { target := 663, numerator := 20464078456083925989123424256 }, some { target := 664, numerator := 17232908173544358727682883584 }, some { target := 665, numerator := 20464078456083925989123424256 }, some { target := 666, numerator := 19925550075660664778883334144 }, some { target := 667, numerator := 752862675831719171915645976576 }, some { target := 668, numerator := 19925550075660664778883334144 }, some { target := 669, numerator := 231028675201579059192998658048 }, some { target := 670, numerator := 752862675831719171915645976576 }, some { target := 671, numerator := 19387021695237403568643244032 }, some { target := 672, numerator := 19925550075660664778883334144 }, some { target := 673, numerator := 19925550075660664778883334144 }, some { target := 674, numerator := 22079663597353709619843694592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 110533923507335761017962496 }, some { target := 1037, numerator := 125885857327799061159346176 }, some { target := 1038, numerator := 98252376450965120904855552 }, some { target := 1039, numerator := 1317195921795751152130719744 }, some { target := 1040, numerator := 116674697035521081074515968 }, some { target := 1041, numerator := 98252376450965120904855552 }, some { target := 1042, numerator := 116674697035521081074515968 }, some { target := 1043, numerator := 113604310271428421046239232 }, some { target := 1044, numerator := 4292400696201538719530876928 }, some { target := 1045, numerator := 113604310271428421046239232 }, some { target := 1046, numerator := 1317195921795751152130719744 }, some { target := 1047, numerator := 4292400696201538719530876928 }, some { target := 1048, numerator := 110533923507335761017962496 }, some { target := 1049, numerator := 113604310271428421046239232 }, some { target := 1050, numerator := 113604310271428421046239232 }, some { target := 1051, numerator := 125885857327799061159346176 }]

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

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 7, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 347, numerator := 742570030231851405810860032 }, some { target := 350, numerator := 2712250635422256182643916800 }, some { target := 352, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 614, numerator := 17989357829165174379482447872 }, some { target := 617, numerator := 65706458942003690102115532800 }, some { target := 619, numerator := 17989351768256824661287895040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 710, numerator := 13629753135545917738915463168 }, some { target := 713, numerator := 49782922953395605416915763200 }, some { target := 715, numerator := 13629748543459564889843957760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 736, numerator := 15186754811838509396260814848 }, some { target := 739, numerator := 55469900092184207090201395200 }, some { target := 741, numerator := 15186749695172871951073935360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 881, numerator := 742570030231851405810860032 }, some { target := 884, numerator := 2712250635422256182643916800 }, some { target := 886, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 977, numerator := 15186754811838509396260814848 }, some { target := 980, numerator := 55469900092184207090201395200 }, some { target := 982, numerator := 15186749695172871951073935360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1003, numerator := 15162800939895546447686270976 }, some { target := 1006, numerator := 55382408136202843987535462400 }, some { target := 1008, numerator := 15162795831300359534747320320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1052, numerator := 742570030231851405810860032 }, some { target := 1055, numerator := 2712250635422256182643916800 }, some { target := 1057, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1078, numerator := 17989357829165174379482447872 }, some { target := 1081, numerator := 65706458942003690102115532800 }, some { target := 1083, numerator := 17989351768256824661287895040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1092, numerator := 742570030231851405810860032 }, some { target := 1095, numerator := 2712250635422256182643916800 }, some { target := 1097, numerator := 742569780047884906125066240 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 562, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 47958066603758976805896192 }, some { target := 72, numerator := 719370999056384652088442880 }, some { target := 73, numerator := 1262895753898986389221933056 }, some { target := 74, numerator := 47958066603758976805896192 }, some { target := 75, numerator := 799301110062649613431603200 }, some { target := 76, numerator := 47958066603758976805896192 }, some { target := 77, numerator := 1262895753898986389221933056 }, some { target := 78, numerator := 1254902742798359893087617024 }, some { target := 79, numerator := 799301110062649613431603200 }, some { target := 80, numerator := 19367065896818000133447745536 }, some { target := 81, numerator := 1238916720597106900818984960 }, some { target := 82, numerator := 719370999056384652088442880 }, some { target := 83, numerator := 1262895753898986389221933056 }, some { target := 84, numerator := 47958066603758976805896192 }, some { target := 85, numerator := 1238916720597106900818984960 }, some { target := 86, numerator := 47958066603758976805896192 }, some { target := 87, numerator := 1262895753898986389221933056 }, some { target := 88, numerator := 1262895753898986389221933056 }, some { target := 89, numerator := 47958066603758976805896192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 5668335570580279142847086592 }, some { target := 147, numerator := 85025033558704187142706298880 }, some { target := 148, numerator := 149266170025280684094973280256 }, some { target := 149, numerator := 5668335570580279142847086592 }, some { target := 150, numerator := 94472259509671319047451443200 }, some { target := 151, numerator := 5668335570580279142847086592 }, some { target := 152, numerator := 149266170025280684094973280256 }, some { target := 153, numerator := 148321447430183970904498765824 }, some { target := 154, numerator := 94472259509671319047451443200 }, some { target := 155, numerator := 2289062847919336060519748468736 }, some { target := 156, numerator := 146432002239990544523549736960 }, some { target := 157, numerator := 85025033558704187142706298880 }, some { target := 158, numerator := 149266170025280684094973280256 }, some { target := 159, numerator := 5668335570580279142847086592 }, some { target := 160, numerator := 146432002239990544523549736960 }, some { target := 161, numerator := 5668335570580279142847086592 }, some { target := 162, numerator := 149266170025280684094973280256 }, some { target := 163, numerator := 149266170025280684094973280256 }, some { target := 164, numerator := 5668335570580279142847086592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 53791374657829083460153638912 }, some { target := 243, numerator := 806870619867436251902304583680 }, some { target := 244, numerator := 1416506199322832531117379158016 }, some { target := 245, numerator := 53791374657829083460153638912 }, some { target := 246, numerator := 896522910963818057669227315200 }, some { target := 247, numerator := 53791374657829083460153638912 }, some { target := 248, numerator := 1416506199322832531117379158016 }, some { target := 249, numerator := 1407540970213194350540686884864 }, some { target := 250, numerator := 896522910963818057669227315200 }, some { target := 251, numerator := 21722750132653311537325377847296 }, some { target := 252, numerator := 1389610511993917989387302338560 }, some { target := 253, numerator := 806870619867436251902304583680 }, some { target := 254, numerator := 1416506199322832531117379158016 }, some { target := 255, numerator := 53791374657829083460153638912 }, some { target := 256, numerator := 1389610511993917989387302338560 }, some { target := 257, numerator := 53791374657829083460153638912 }, some { target := 258, numerator := 1416506199322832531117379158016 }, some { target := 259, numerator := 1416506199322832531117379158016 }, some { target := 260, numerator := 53791374657829083460153638912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 5668339458231592677135089664 }, some { target := 641, numerator := 85025091873473890157026344960 }, some { target := 642, numerator := 149266272400098607164557361152 }, some { target := 643, numerator := 5668339458231592677135089664 }, some { target := 644, numerator := 94472324303859877952251494400 }, some { target := 645, numerator := 5668339458231592677135089664 }, some { target := 646, numerator := 149266272400098607164557361152 }, some { target := 647, numerator := 148321549157060008385034846208 }, some { target := 648, numerator := 94472324303859877952251494400 }, some { target := 649, numerator := 2289064417882524842783053709312 }, some { target := 650, numerator := 146432102670982810825989816320 }, some { target := 651, numerator := 85025091873473890157026344960 }, some { target := 652, numerator := 149266272400098607164557361152 }, some { target := 653, numerator := 5668339458231592677135089664 }, some { target := 654, numerator := 146432102670982810825989816320 }, some { target := 655, numerator := 5668339458231592677135089664 }, some { target := 656, numerator := 149266272400098607164557361152 }, some { target := 657, numerator := 149266272400098607164557361152 }, some { target := 658, numerator := 5668339458231592677135089664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 47958066603758976805896192 }, some { target := 1018, numerator := 719370999056384652088442880 }, some { target := 1019, numerator := 1262895753898986389221933056 }, some { target := 1020, numerator := 47958066603758976805896192 }, some { target := 1021, numerator := 799301110062649613431603200 }, some { target := 1022, numerator := 47958066603758976805896192 }, some { target := 1023, numerator := 1262895753898986389221933056 }, some { target := 1024, numerator := 1254902742798359893087617024 }, some { target := 1025, numerator := 799301110062649613431603200 }, some { target := 1026, numerator := 19367065896818000133447745536 }, some { target := 1027, numerator := 1238916720597106900818984960 }, some { target := 1028, numerator := 719370999056384652088442880 }, some { target := 1029, numerator := 1262895753898986389221933056 }, some { target := 1030, numerator := 47958066603758976805896192 }, some { target := 1031, numerator := 1238916720597106900818984960 }, some { target := 1032, numerator := 47958066603758976805896192 }, some { target := 1033, numerator := 1262895753898986389221933056 }, some { target := 1034, numerator := 1262895753898986389221933056 }, some { target := 1035, numerator := 47958066603758976805896192 }]

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

end Slot6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
