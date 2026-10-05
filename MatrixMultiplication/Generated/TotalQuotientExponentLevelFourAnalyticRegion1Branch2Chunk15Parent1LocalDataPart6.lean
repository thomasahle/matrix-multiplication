import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 647, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 6849262132654800249120882688 }, some { target := 27, numerator := 718132781504713491016300101632 }, some { target := 29, numerator := 7740753611750145810619170816000 }, some { target := 37, numerator := 718133329314209824280336662528 }, some { target := 44, numerator := 6849262132654800249120882688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 24502783055217122226110201856 }, some { target := 158, numerator := 2569072610925063122233520553984 }, some { target := 160, numerator := 27692034960718519033493716992000 }, some { target := 168, numerator := 2569074570677366986675832487936 }, some { target := 175, numerator := 24502783055217122226110201856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 6849259855679583171895099392 }, some { target := 268, numerator := 718132542767968658158138687488 }, some { target := 270, numerator := 7740751038406653608139423744000 }, some { target := 278, numerator := 718133090577282877112243453952 }, some { target := 285, numerator := 6849259855679583171895099392 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 133, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 31091269926827863421401169920 }, some { target := 11, numerator := 2603245133672461361563935178752 }, some { target := 16, numerator := 2603246075784574694058155311104 }, some { target := 24, numerator := 31090327814714530927181037568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 31091269926827863421401169920 }, some { target := 142, numerator := 2603245133672461361563935178752 }, some { target := 147, numerator := 2603246075784574694058155311104 }, some { target := 155, numerator := 31090327814714530927181037568 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 4, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 27118831769720607911398342656 }, some { target := 2, numerator := 262674986517616134551379116032 }, some { target := 7, numerator := 27118831769720607911398342656 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 7, #[2061584302080, 36696200577024, 2061584302080, 32641751449600, 55731495632896, 2061584302080, 55731495632896, 55731495632896, 36696200577024, 2061584302080, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 5950181768415752969256960 }, some { target := 27, numerator := 158671513824420079180185600 }, some { target := 28, numerator := 151729635094601700716052480 }, some { target := 29, numerator := 4958484807013127474380800 }, some { target := 30, numerator := 155696422940212202695557120 }, some { target := 31, numerator := 4958484807013127474380800 }, some { target := 32, numerator := 151729635094601700716052480 }, some { target := 33, numerator := 86277635642028418054225920 }, some { target := 34, numerator := 155696422940212202695557120 }, some { target := 35, numerator := 2430649252397835087941468160 }, some { target := 36, numerator := 95202908294652047508111360 }, some { target := 37, numerator := 158671513824420079180185600 }, some { target := 38, numerator := 151729635094601700716052480 }, some { target := 39, numerator := 4958484807013127474380800 }, some { target := 40, numerator := 95202908294652047508111360 }, some { target := 41, numerator := 4958484807013127474380800 }, some { target := 42, numerator := 152721332056004326210928640 }, some { target := 43, numerator := 86277635642028418054225920 }, some { target := 44, numerator := 5950181768415752969256960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 105913235477800402852773888 }, some { target := 62, numerator := 2824352946074677409407303680 }, some { target := 63, numerator := 2700787504683910272745734144 }, some { target := 64, numerator := 88261029564833669043978240 }, some { target := 65, numerator := 2771396328335777207980916736 }, some { target := 66, numerator := 88261029564833669043978240 }, some { target := 67, numerator := 2700787504683910272745734144 }, some { target := 68, numerator := 1535741914428105841365221376 }, some { target := 69, numerator := 2771396328335777207980916736 }, some { target := 70, numerator := 43265556692681464565358133248 }, some { target := 71, numerator := 1694611767644806445644382208 }, some { target := 72, numerator := 2824352946074677409407303680 }, some { target := 73, numerator := 2700787504683910272745734144 }, some { target := 74, numerator := 88261029564833669043978240 }, some { target := 75, numerator := 1694611767644806445644382208 }, some { target := 76, numerator := 88261029564833669043978240 }, some { target := 77, numerator := 2718439710596877006554529792 }, some { target := 78, numerator := 1535741914428105841365221376 }, some { target := 79, numerator := 105913235477800402852773888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 5950181768415752969256960 }, some { target := 97, numerator := 158671513824420079180185600 }, some { target := 98, numerator := 151729635094601700716052480 }, some { target := 99, numerator := 4958484807013127474380800 }, some { target := 100, numerator := 155696422940212202695557120 }, some { target := 101, numerator := 4958484807013127474380800 }, some { target := 102, numerator := 151729635094601700716052480 }, some { target := 103, numerator := 86277635642028418054225920 }, some { target := 104, numerator := 155696422940212202695557120 }, some { target := 105, numerator := 2430649252397835087941468160 }, some { target := 106, numerator := 95202908294652047508111360 }, some { target := 107, numerator := 158671513824420079180185600 }, some { target := 108, numerator := 151729635094601700716052480 }, some { target := 109, numerator := 4958484807013127474380800 }, some { target := 110, numerator := 95202908294652047508111360 }, some { target := 111, numerator := 4958484807013127474380800 }, some { target := 112, numerator := 152721332056004326210928640 }, some { target := 113, numerator := 86277635642028418054225920 }, some { target := 114, numerator := 5950181768415752969256960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 94211211333249422013235200 }, some { target := 158, numerator := 2512298968886651253686272000 }, some { target := 159, numerator := 2402385888997860261337497600 }, some { target := 160, numerator := 78509342777707851677696000 }, some { target := 161, numerator := 2465193363220026542679654400 }, some { target := 162, numerator := 78509342777707851677696000 }, some { target := 163, numerator := 2402385888997860261337497600 }, some { target := 164, numerator := 1366062564332116619191910400 }, some { target := 165, numerator := 2465193363220026542679654400 }, some { target := 166, numerator := 38485279829632388892406579200 }, some { target := 167, numerator := 1507379381331990752211763200 }, some { target := 168, numerator := 2512298968886651253686272000 }, some { target := 169, numerator := 2402385888997860261337497600 }, some { target := 170, numerator := 78509342777707851677696000 }, some { target := 171, numerator := 1507379381331990752211763200 }, some { target := 172, numerator := 78509342777707851677696000 }, some { target := 173, numerator := 2418087757553401831673036800 }, some { target := 174, numerator := 1366062564332116619191910400 }, some { target := 175, numerator := 94211211333249422013235200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 192, numerator := 160853247139505855268913152 }, some { target := 193, numerator := 4289419923720156140504350720 }, some { target := 194, numerator := 4101757802057399309357285376 }, some { target := 195, numerator := 134044372616254879390760960 }, some { target := 196, numerator := 4208993300150403212869894144 }, some { target := 197, numerator := 134044372616254879390760960 }, some { target := 198, numerator := 4101757802057399309357285376 }, some { target := 199, numerator := 2332372083522834901399240704 }, some { target := 200, numerator := 4208993300150403212869894144 }, some { target := 201, numerator := 65708551456488141877351022592 }, some { target := 202, numerator := 2573651954232093684302610432 }, some { target := 203, numerator := 4289419923720156140504350720 }, some { target := 204, numerator := 4101757802057399309357285376 }, some { target := 205, numerator := 134044372616254879390760960 }, some { target := 206, numerator := 2573651954232093684302610432 }, some { target := 207, numerator := 134044372616254879390760960 }, some { target := 208, numerator := 4128566676580650285235437568 }, some { target := 209, numerator := 2332372083522834901399240704 }, some { target := 210, numerator := 160853247139505855268913152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 5950181768415752969256960 }, some { target := 268, numerator := 158671513824420079180185600 }, some { target := 269, numerator := 151729635094601700716052480 }, some { target := 270, numerator := 4958484807013127474380800 }, some { target := 271, numerator := 155696422940212202695557120 }, some { target := 272, numerator := 4958484807013127474380800 }, some { target := 273, numerator := 151729635094601700716052480 }, some { target := 274, numerator := 86277635642028418054225920 }, some { target := 275, numerator := 155696422940212202695557120 }, some { target := 276, numerator := 2430649252397835087941468160 }, some { target := 277, numerator := 95202908294652047508111360 }, some { target := 278, numerator := 158671513824420079180185600 }, some { target := 279, numerator := 151729635094601700716052480 }, some { target := 280, numerator := 4958484807013127474380800 }, some { target := 281, numerator := 95202908294652047508111360 }, some { target := 282, numerator := 4958484807013127474380800 }, some { target := 283, numerator := 152721332056004326210928640 }, some { target := 284, numerator := 86277635642028418054225920 }, some { target := 285, numerator := 5950181768415752969256960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 373, numerator := 160853247139505855268913152 }, some { target := 374, numerator := 4289419923720156140504350720 }, some { target := 375, numerator := 4101757802057399309357285376 }, some { target := 376, numerator := 134044372616254879390760960 }, some { target := 377, numerator := 4208993300150403212869894144 }, some { target := 378, numerator := 134044372616254879390760960 }, some { target := 379, numerator := 4101757802057399309357285376 }, some { target := 380, numerator := 2332372083522834901399240704 }, some { target := 381, numerator := 4208993300150403212869894144 }, some { target := 382, numerator := 65708551456488141877351022592 }, some { target := 383, numerator := 2573651954232093684302610432 }, some { target := 384, numerator := 4289419923720156140504350720 }, some { target := 385, numerator := 4101757802057399309357285376 }, some { target := 386, numerator := 134044372616254879390760960 }, some { target := 387, numerator := 2573651954232093684302610432 }, some { target := 388, numerator := 134044372616254879390760960 }, some { target := 389, numerator := 4128566676580650285235437568 }, some { target := 390, numerator := 2332372083522834901399240704 }, some { target := 391, numerator := 160853247139505855268913152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 160853247139505855268913152 }, some { target := 409, numerator := 4289419923720156140504350720 }, some { target := 410, numerator := 4101757802057399309357285376 }, some { target := 411, numerator := 134044372616254879390760960 }, some { target := 412, numerator := 4208993300150403212869894144 }, some { target := 413, numerator := 134044372616254879390760960 }, some { target := 414, numerator := 4101757802057399309357285376 }, some { target := 415, numerator := 2332372083522834901399240704 }, some { target := 416, numerator := 4208993300150403212869894144 }, some { target := 417, numerator := 65708551456488141877351022592 }, some { target := 418, numerator := 2573651954232093684302610432 }, some { target := 419, numerator := 4289419923720156140504350720 }, some { target := 420, numerator := 4101757802057399309357285376 }, some { target := 421, numerator := 134044372616254879390760960 }, some { target := 422, numerator := 2573651954232093684302610432 }, some { target := 423, numerator := 134044372616254879390760960 }, some { target := 424, numerator := 4128566676580650285235437568 }, some { target := 425, numerator := 2332372083522834901399240704 }, some { target := 426, numerator := 160853247139505855268913152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 483, numerator := 105913235477800402852773888 }, some { target := 484, numerator := 2824352946074677409407303680 }, some { target := 485, numerator := 2700787504683910272745734144 }, some { target := 486, numerator := 88261029564833669043978240 }, some { target := 487, numerator := 2771396328335777207980916736 }, some { target := 488, numerator := 88261029564833669043978240 }, some { target := 489, numerator := 2700787504683910272745734144 }, some { target := 490, numerator := 1535741914428105841365221376 }, some { target := 491, numerator := 2771396328335777207980916736 }, some { target := 492, numerator := 43265556692681464565358133248 }, some { target := 493, numerator := 1694611767644806445644382208 }, some { target := 494, numerator := 2824352946074677409407303680 }, some { target := 495, numerator := 2700787504683910272745734144 }, some { target := 496, numerator := 88261029564833669043978240 }, some { target := 497, numerator := 1694611767644806445644382208 }, some { target := 498, numerator := 88261029564833669043978240 }, some { target := 499, numerator := 2718439710596877006554529792 }, some { target := 500, numerator := 1535741914428105841365221376 }, some { target := 501, numerator := 105913235477800402852773888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 623, numerator := 5950181768415752969256960 }, some { target := 624, numerator := 158671513824420079180185600 }, some { target := 625, numerator := 151729635094601700716052480 }, some { target := 626, numerator := 4958484807013127474380800 }, some { target := 627, numerator := 155696422940212202695557120 }, some { target := 628, numerator := 4958484807013127474380800 }, some { target := 629, numerator := 151729635094601700716052480 }, some { target := 630, numerator := 86277635642028418054225920 }, some { target := 631, numerator := 155696422940212202695557120 }, some { target := 632, numerator := 2430649252397835087941468160 }, some { target := 633, numerator := 95202908294652047508111360 }, some { target := 634, numerator := 158671513824420079180185600 }, some { target := 635, numerator := 151729635094601700716052480 }, some { target := 636, numerator := 4958484807013127474380800 }, some { target := 637, numerator := 95202908294652047508111360 }, some { target := 638, numerator := 4958484807013127474380800 }, some { target := 639, numerator := 152721332056004326210928640 }, some { target := 640, numerator := 86277635642028418054225920 }, some { target := 641, numerator := 5950181768415752969256960 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 4, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 1353996917968384675670917120 }, some { target := 11, numerator := 1392682544196052809261514752 }, some { target := 12, numerator := 1353996917968384675670917120 }, some { target := 13, numerator := 1199254413057712141308526592 }, some { target := 14, numerator := 56132843656346461839957164032 }, some { target := 15, numerator := 15280822359928912768286064640 }, some { target := 16, numerator := 1392682544196052809261514752 }, some { target := 17, numerator := 56132843656346461839957164032 }, some { target := 18, numerator := 1353996917968384675670917120 }, some { target := 19, numerator := 1353996917968384675670917120 }, some { target := 20, numerator := 1160568786830044007717928960 }, some { target := 21, numerator := 1353996917968384675670917120 }, some { target := 22, numerator := 15280822359928912768286064640 }, some { target := 23, numerator := 1160568786830044007717928960 }, some { target := 24, numerator := 1353996917968384675670917120 }, some { target := 25, numerator := 1199254413057712141308526592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 1353996917968384675670917120 }, some { target := 142, numerator := 1392682544196052809261514752 }, some { target := 143, numerator := 1353996917968384675670917120 }, some { target := 144, numerator := 1199254413057712141308526592 }, some { target := 145, numerator := 56132843656346461839957164032 }, some { target := 146, numerator := 15280822359928912768286064640 }, some { target := 147, numerator := 1392682544196052809261514752 }, some { target := 148, numerator := 56132843656346461839957164032 }, some { target := 149, numerator := 1353996917968384675670917120 }, some { target := 150, numerator := 1353996917968384675670917120 }, some { target := 151, numerator := 1160568786830044007717928960 }, some { target := 152, numerator := 1353996917968384675670917120 }, some { target := 153, numerator := 15280822359928912768286064640 }, some { target := 154, numerator := 1160568786830044007717928960 }, some { target := 155, numerator := 1353996917968384675670917120 }, some { target := 156, numerator := 1199254413057712141308526592 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot28

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1
