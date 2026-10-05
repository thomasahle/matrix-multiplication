import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 1,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 3, #[140737505132544, 0, 140737471578112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 118842257938495954999251566592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 50, numerator := 118842229604297057781380284416 }]

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

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 7, #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 24868968094011534336944242688 }, some { target := 2, numerator := 24796393284398660209501798400 }, some { target := 3, numerator := 24627052061968620578802761728 }, some { target := 4, numerator := 24796393284398660209501798400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 89452938682703728834210955264 }, some { target := 52, numerator := 89191889250750313283138355200 }, some { target := 53, numerator := 88582773909525676997302288384 }, some { target := 54, numerator := 89191889250750313283138355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 24868976390434681487815081984 }, some { target := 141, numerator := 24796401556610455763628851200 }, some { target := 142, numerator := 24627060277687262407194312704 }, some { target := 143, numerator := 24796401556610455763628851200 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 28, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 209841301533678460171452416 }, some { target := 11, numerator := 5144496424696633217106575360 }, some { target := 12, numerator := 3804219724578299826334072832 }, some { target := 13, numerator := 4244209550374722404112924672 }, some { target := 14, numerator := 209841301533678460171452416 }, some { target := 15, numerator := 4237440476131700518300942336 }, some { target := 16, numerator := 4311900292804941262232748032 }, some { target := 17, numerator := 209841301533678460171452416 }, some { target := 18, numerator := 5144496424696633217106575360 }, some { target := 19, numerator := 209841301533678460171452416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 8184940590606172527731408896 }, some { target := 56, numerator := 200663059640667455518576476160 }, some { target := 57, numerator := 148385051997440934212421025792 }, some { target := 58, numerator := 165547024203550650802825592832 }, some { target := 59, numerator := 8184940590606172527731408896 }, some { target := 60, numerator := 165282993861918193624511676416 }, some { target := 61, numerator := 168187327619875222585964756992 }, some { target := 62, numerator := 8184940590606172527731408896 }, some { target := 63, numerator := 200663059640667455518576476160 }, some { target := 64, numerator := 8184940590606172527731408896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 8184937588398574531501883392 }, some { target := 145, numerator := 200662986038158601417465528320 }, some { target := 146, numerator := 148384997570322544732388982784 }, some { target := 147, numerator := 165546963481480846169409060864 }, some { target := 148, numerator := 8184937588398574531501883392 }, some { target := 149, numerator := 165282933236693795378070290432 }, some { target := 150, numerator := 168187265929351354082796765184 }, some { target := 151, numerator := 8184937588398574531501883392 }, some { target := 152, numerator := 200662986038158601417465528320 }, some { target := 153, numerator := 8184937588398574531501883392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 209842302269544458914627584 }, some { target := 483, numerator := 5144520958866251250810224640 }, some { target := 484, numerator := 3804237866951096319678087168 }, some { target := 485, numerator := 4244229791064657281918435328 }, some { target := 486, numerator := 209842302269544458914627584 }, some { target := 487, numerator := 4237460684539833267114737664 }, some { target := 488, numerator := 4311920856312897429955411968 }, some { target := 489, numerator := 209842302269544458914627584 }, some { target := 490, numerator := 5144520958866251250810224640 }, some { target := 491, numerator := 209842302269544458914627584 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 59, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 34, numerator := 78570733541985157065474048 }, some { target := 35, numerator := 58510120722754904197693440 }, some { target := 36, numerator := 61853556192626613008990208 }, some { target := 37, numerator := 80242451276921011471122432 }, some { target := 38, numerator := 1074914503563754382831910912 }, some { target := 39, numerator := 1944207725730398673769070592 }, some { target := 40, numerator := 58510120722754904197693440 }, some { target := 41, numerator := 1074914503563754382831910912 }, some { target := 42, numerator := 63525273927562467414638592 }, some { target := 43, numerator := 63525273927562467414638592 }, some { target := 44, numerator := 61853556192626613008990208 }, some { target := 45, numerator := 61853556192626613008990208 }, some { target := 46, numerator := 1944207725730398673769070592 }, some { target := 47, numerator := 61853556192626613008990208 }, some { target := 48, numerator := 78570733541985157065474048 }, some { target := 49, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 1178561003129777355982110720 }, some { target := 80, numerator := 877651810841323562965401600 }, some { target := 81, numerator := 927803342889399195134853120 }, some { target := 82, numerator := 1203636769153815172066836480 }, some { target := 83, numerator := 16123717553456315742478663680 }, some { target := 84, numerator := 29163115885955980106536058880 }, some { target := 85, numerator := 877651810841323562965401600 }, some { target := 86, numerator := 16123717553456315742478663680 }, some { target := 87, numerator := 952879108913437011219578880 }, some { target := 88, numerator := 952879108913437011219578880 }, some { target := 89, numerator := 927803342889399195134853120 }, some { target := 90, numerator := 927803342889399195134853120 }, some { target := 91, numerator := 29163115885955980106536058880 }, some { target := 92, numerator := 927803342889399195134853120 }, some { target := 93, numerator := 1178561003129777355982110720 }, some { target := 94, numerator := 1203636769153815172066836480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 105, numerator := 2069029316605609136057483264 }, some { target := 106, numerator := 1540766512365879143872593920 }, some { target := 107, numerator := 1628810313072500809236742144 }, some { target := 108, numerator := 2113051216958919968739557376 }, some { target := 109, numerator := 28306081927178865414573654016 }, some { target := 110, numerator := 51197470110900498409252192256 }, some { target := 111, numerator := 1540766512365879143872593920 }, some { target := 112, numerator := 28306081927178865414573654016 }, some { target := 113, numerator := 1672832213425811641918816256 }, some { target := 114, numerator := 1672832213425811641918816256 }, some { target := 115, numerator := 1628810313072500809236742144 }, some { target := 116, numerator := 1628810313072500809236742144 }, some { target := 117, numerator := 51197470110900498409252192256 }, some { target := 118, numerator := 1628810313072500809236742144 }, some { target := 119, numerator := 2069029316605609136057483264 }, some { target := 120, numerator := 2113051216958919968739557376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 78570733541985157065474048 }, some { target := 155, numerator := 58510120722754904197693440 }, some { target := 156, numerator := 61853556192626613008990208 }, some { target := 157, numerator := 80242451276921011471122432 }, some { target := 158, numerator := 1074914503563754382831910912 }, some { target := 159, numerator := 1944207725730398673769070592 }, some { target := 160, numerator := 58510120722754904197693440 }, some { target := 161, numerator := 1074914503563754382831910912 }, some { target := 162, numerator := 63525273927562467414638592 }, some { target := 163, numerator := 63525273927562467414638592 }, some { target := 164, numerator := 61853556192626613008990208 }, some { target := 165, numerator := 61853556192626613008990208 }, some { target := 166, numerator := 1944207725730398673769070592 }, some { target := 167, numerator := 61853556192626613008990208 }, some { target := 168, numerator := 78570733541985157065474048 }, some { target := 169, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 180, numerator := 1309512225699752617757900800 }, some { target := 181, numerator := 975168678712581736628224000 }, some { target := 182, numerator := 1030892603210443550149836800 }, some { target := 183, numerator := 1337374187948683524518707200 }, some { target := 184, numerator := 17915241726062573047198515200 }, some { target := 185, numerator := 32403462095506644562817843200 }, some { target := 186, numerator := 975168678712581736628224000 }, some { target := 187, numerator := 17915241726062573047198515200 }, some { target := 188, numerator := 1058754565459374456910643200 }, some { target := 189, numerator := 1058754565459374456910643200 }, some { target := 190, numerator := 1030892603210443550149836800 }, some { target := 191, numerator := 1030892603210443550149836800 }, some { target := 192, numerator := 32403462095506644562817843200 }, some { target := 193, numerator := 1030892603210443550149836800 }, some { target := 194, numerator := 1309512225699752617757900800 }, some { target := 195, numerator := 1337374187948683524518707200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 78570733541985157065474048 }, some { target := 216, numerator := 58510120722754904197693440 }, some { target := 217, numerator := 61853556192626613008990208 }, some { target := 218, numerator := 80242451276921011471122432 }, some { target := 219, numerator := 1074914503563754382831910912 }, some { target := 220, numerator := 1944207725730398673769070592 }, some { target := 221, numerator := 58510120722754904197693440 }, some { target := 222, numerator := 1074914503563754382831910912 }, some { target := 223, numerator := 63525273927562467414638592 }, some { target := 224, numerator := 63525273927562467414638592 }, some { target := 225, numerator := 61853556192626613008990208 }, some { target := 226, numerator := 61853556192626613008990208 }, some { target := 227, numerator := 1944207725730398673769070592 }, some { target := 228, numerator := 61853556192626613008990208 }, some { target := 229, numerator := 78570733541985157065474048 }, some { target := 230, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 295, numerator := 2069029316605609136057483264 }, some { target := 296, numerator := 1540766512365879143872593920 }, some { target := 297, numerator := 1628810313072500809236742144 }, some { target := 298, numerator := 2113051216958919968739557376 }, some { target := 299, numerator := 28306081927178865414573654016 }, some { target := 300, numerator := 51197470110900498409252192256 }, some { target := 301, numerator := 1540766512365879143872593920 }, some { target := 302, numerator := 28306081927178865414573654016 }, some { target := 303, numerator := 1672832213425811641918816256 }, some { target := 304, numerator := 1672832213425811641918816256 }, some { target := 305, numerator := 1628810313072500809236742144 }, some { target := 306, numerator := 1628810313072500809236742144 }, some { target := 307, numerator := 51197470110900498409252192256 }, some { target := 308, numerator := 1628810313072500809236742144 }, some { target := 309, numerator := 2069029316605609136057483264 }, some { target := 310, numerator := 2113051216958919968739557376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 321, numerator := 2055934194348611609879904256 }, some { target := 322, numerator := 1531014825578753326506311680 }, some { target := 323, numerator := 1618501387040396373735243776 }, some { target := 324, numerator := 2099677475079433133494370304 }, some { target := 325, numerator := 28126929509918239684101668864 }, some { target := 326, numerator := 50873435489945431963624013824 }, some { target := 327, numerator := 1531014825578753326506311680 }, some { target := 328, numerator := 28126929509918239684101668864 }, some { target := 329, numerator := 1662244667771217897349709824 }, some { target := 330, numerator := 1662244667771217897349709824 }, some { target := 331, numerator := 1618501387040396373735243776 }, some { target := 332, numerator := 1618501387040396373735243776 }, some { target := 333, numerator := 50873435489945431963624013824 }, some { target := 334, numerator := 1618501387040396373735243776 }, some { target := 335, numerator := 2055934194348611609879904256 }, some { target := 336, numerator := 2099677475079433133494370304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 370, numerator := 1309512225699752617757900800 }, some { target := 371, numerator := 975168678712581736628224000 }, some { target := 372, numerator := 1030892603210443550149836800 }, some { target := 373, numerator := 1337374187948683524518707200 }, some { target := 374, numerator := 17915241726062573047198515200 }, some { target := 375, numerator := 32403462095506644562817843200 }, some { target := 376, numerator := 975168678712581736628224000 }, some { target := 377, numerator := 17915241726062573047198515200 }, some { target := 378, numerator := 1058754565459374456910643200 }, some { target := 379, numerator := 1058754565459374456910643200 }, some { target := 380, numerator := 1030892603210443550149836800 }, some { target := 381, numerator := 1030892603210443550149836800 }, some { target := 382, numerator := 32403462095506644562817843200 }, some { target := 383, numerator := 1030892603210443550149836800 }, some { target := 384, numerator := 1309512225699752617757900800 }, some { target := 385, numerator := 1337374187948683524518707200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 396, numerator := 31729481228705005928273936384 }, some { target := 397, numerator := 23628337085205855478501867520 }, some { target := 398, numerator := 24978527775789047220130545664 }, some { target := 399, numerator := 32404576573996601799088275456 }, some { target := 400, numerator := 434086307022496144933620023296 }, some { target := 401, numerator := 785135886574125997757076340736 }, some { target := 402, numerator := 23628337085205855478501867520 }, some { target := 403, numerator := 434086307022496144933620023296 }, some { target := 404, numerator := 25653623121080643090944884736 }, some { target := 405, numerator := 25653623121080643090944884736 }, some { target := 406, numerator := 24978527775789047220130545664 }, some { target := 407, numerator := 24978527775789047220130545664 }, some { target := 408, numerator := 785135886574125997757076340736 }, some { target := 409, numerator := 24978527775789047220130545664 }, some { target := 410, numerator := 31729481228705005928273936384 }, some { target := 411, numerator := 32404576573996601799088275456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 431, numerator := 2029743949834616557524746240 }, some { target := 432, numerator := 1511511452004501691773747200 }, some { target := 433, numerator := 1597883534976187502732247040 }, some { target := 434, numerator := 2072929991320459463003996160 }, some { target := 435, numerator := 27768624675396988223157698560 }, some { target := 436, numerator := 50225366248035299072367656960 }, some { target := 437, numerator := 1511511452004501691773747200 }, some { target := 438, numerator := 27768624675396988223157698560 }, some { target := 439, numerator := 1641069576462030408211496960 }, some { target := 440, numerator := 1641069576462030408211496960 }, some { target := 441, numerator := 1597883534976187502732247040 }, some { target := 442, numerator := 1597883534976187502732247040 }, some { target := 443, numerator := 50225366248035299072367656960 }, some { target := 444, numerator := 1597883534976187502732247040 }, some { target := 445, numerator := 2029743949834616557524746240 }, some { target := 446, numerator := 2072929991320459463003996160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 1178561003129777355982110720 }, some { target := 493, numerator := 877651810841323562965401600 }, some { target := 494, numerator := 927803342889399195134853120 }, some { target := 495, numerator := 1203636769153815172066836480 }, some { target := 496, numerator := 16123717553456315742478663680 }, some { target := 497, numerator := 29163115885955980106536058880 }, some { target := 498, numerator := 877651810841323562965401600 }, some { target := 499, numerator := 16123717553456315742478663680 }, some { target := 500, numerator := 952879108913437011219578880 }, some { target := 501, numerator := 952879108913437011219578880 }, some { target := 502, numerator := 927803342889399195134853120 }, some { target := 503, numerator := 927803342889399195134853120 }, some { target := 504, numerator := 29163115885955980106536058880 }, some { target := 505, numerator := 927803342889399195134853120 }, some { target := 506, numerator := 1178561003129777355982110720 }, some { target := 507, numerator := 1203636769153815172066836480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 527, numerator := 2069029316605609136057483264 }, some { target := 528, numerator := 1540766512365879143872593920 }, some { target := 529, numerator := 1628810313072500809236742144 }, some { target := 530, numerator := 2113051216958919968739557376 }, some { target := 531, numerator := 28306081927178865414573654016 }, some { target := 532, numerator := 51197470110900498409252192256 }, some { target := 533, numerator := 1540766512365879143872593920 }, some { target := 534, numerator := 28306081927178865414573654016 }, some { target := 535, numerator := 1672832213425811641918816256 }, some { target := 536, numerator := 1672832213425811641918816256 }, some { target := 537, numerator := 1628810313072500809236742144 }, some { target := 538, numerator := 1628810313072500809236742144 }, some { target := 539, numerator := 51197470110900498409252192256 }, some { target := 540, numerator := 1628810313072500809236742144 }, some { target := 541, numerator := 2069029316605609136057483264 }, some { target := 542, numerator := 2113051216958919968739557376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 637, numerator := 78570733541985157065474048 }, some { target := 638, numerator := 58510120722754904197693440 }, some { target := 639, numerator := 61853556192626613008990208 }, some { target := 640, numerator := 80242451276921011471122432 }, some { target := 641, numerator := 1074914503563754382831910912 }, some { target := 642, numerator := 1944207725730398673769070592 }, some { target := 643, numerator := 58510120722754904197693440 }, some { target := 644, numerator := 1074914503563754382831910912 }, some { target := 645, numerator := 63525273927562467414638592 }, some { target := 646, numerator := 63525273927562467414638592 }, some { target := 647, numerator := 61853556192626613008990208 }, some { target := 648, numerator := 61853556192626613008990208 }, some { target := 649, numerator := 1944207725730398673769070592 }, some { target := 650, numerator := 61853556192626613008990208 }, some { target := 651, numerator := 78570733541985157065474048 }, some { target := 652, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 663, numerator := 2029743949834616557524746240 }, some { target := 664, numerator := 1511511452004501691773747200 }, some { target := 665, numerator := 1597883534976187502732247040 }, some { target := 666, numerator := 2072929991320459463003996160 }, some { target := 667, numerator := 27768624675396988223157698560 }, some { target := 668, numerator := 50225366248035299072367656960 }, some { target := 669, numerator := 1511511452004501691773747200 }, some { target := 670, numerator := 27768624675396988223157698560 }, some { target := 671, numerator := 1641069576462030408211496960 }, some { target := 672, numerator := 1641069576462030408211496960 }, some { target := 673, numerator := 1597883534976187502732247040 }, some { target := 674, numerator := 1597883534976187502732247040 }, some { target := 675, numerator := 50225366248035299072367656960 }, some { target := 676, numerator := 1597883534976187502732247040 }, some { target := 677, numerator := 2029743949834616557524746240 }, some { target := 678, numerator := 2072929991320459463003996160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 78570733541985157065474048 }, some { target := 699, numerator := 58510120722754904197693440 }, some { target := 700, numerator := 61853556192626613008990208 }, some { target := 701, numerator := 80242451276921011471122432 }, some { target := 702, numerator := 1074914503563754382831910912 }, some { target := 703, numerator := 1944207725730398673769070592 }, some { target := 704, numerator := 58510120722754904197693440 }, some { target := 705, numerator := 1074914503563754382831910912 }, some { target := 706, numerator := 63525273927562467414638592 }, some { target := 707, numerator := 63525273927562467414638592 }, some { target := 708, numerator := 61853556192626613008990208 }, some { target := 709, numerator := 61853556192626613008990208 }, some { target := 710, numerator := 1944207725730398673769070592 }, some { target := 711, numerator := 61853556192626613008990208 }, some { target := 712, numerator := 78570733541985157065474048 }, some { target := 713, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 759, numerator := 2069029316605609136057483264 }, some { target := 760, numerator := 1540766512365879143872593920 }, some { target := 761, numerator := 1628810313072500809236742144 }, some { target := 762, numerator := 2113051216958919968739557376 }, some { target := 763, numerator := 28306081927178865414573654016 }, some { target := 764, numerator := 51197470110900498409252192256 }, some { target := 765, numerator := 1540766512365879143872593920 }, some { target := 766, numerator := 28306081927178865414573654016 }, some { target := 767, numerator := 1672832213425811641918816256 }, some { target := 768, numerator := 1672832213425811641918816256 }, some { target := 769, numerator := 1628810313072500809236742144 }, some { target := 770, numerator := 1628810313072500809236742144 }, some { target := 771, numerator := 51197470110900498409252192256 }, some { target := 772, numerator := 1628810313072500809236742144 }, some { target := 773, numerator := 2069029316605609136057483264 }, some { target := 774, numerator := 2113051216958919968739557376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 794, numerator := 2069029316605609136057483264 }, some { target := 795, numerator := 1540766512365879143872593920 }, some { target := 796, numerator := 1628810313072500809236742144 }, some { target := 797, numerator := 2113051216958919968739557376 }, some { target := 798, numerator := 28306081927178865414573654016 }, some { target := 799, numerator := 51197470110900498409252192256 }, some { target := 800, numerator := 1540766512365879143872593920 }, some { target := 801, numerator := 28306081927178865414573654016 }, some { target := 802, numerator := 1672832213425811641918816256 }, some { target := 803, numerator := 1672832213425811641918816256 }, some { target := 804, numerator := 1628810313072500809236742144 }, some { target := 805, numerator := 1628810313072500809236742144 }, some { target := 806, numerator := 51197470110900498409252192256 }, some { target := 807, numerator := 1628810313072500809236742144 }, some { target := 808, numerator := 2069029316605609136057483264 }, some { target := 809, numerator := 2113051216958919968739557376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 78570733541985157065474048 }, some { target := 891, numerator := 58510120722754904197693440 }, some { target := 892, numerator := 61853556192626613008990208 }, some { target := 893, numerator := 80242451276921011471122432 }, some { target := 894, numerator := 1074914503563754382831910912 }, some { target := 895, numerator := 1944207725730398673769070592 }, some { target := 896, numerator := 58510120722754904197693440 }, some { target := 897, numerator := 1074914503563754382831910912 }, some { target := 898, numerator := 63525273927562467414638592 }, some { target := 899, numerator := 63525273927562467414638592 }, some { target := 900, numerator := 61853556192626613008990208 }, some { target := 901, numerator := 61853556192626613008990208 }, some { target := 902, numerator := 1944207725730398673769070592 }, some { target := 903, numerator := 61853556192626613008990208 }, some { target := 904, numerator := 78570733541985157065474048 }, some { target := 905, numerator := 80242451276921011471122432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot19

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1
