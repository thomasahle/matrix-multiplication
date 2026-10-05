import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨1, 4, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 263, numerator := 1353996917968384675670917120 }, some { target := 265, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 1392682544196052809261514752 }, some { target := 340, numerator := 1392682544196052809261514752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 352, numerator := 1353996917968384675670917120 }, some { target := 354, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 479, numerator := 1199254413057712141308526592 }, some { target := 481, numerator := 1199254413057712141308526592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 554, numerator := 56132843656346461839957164032 }, some { target := 556, numerator := 56132843656346461839957164032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 568, numerator := 15280822359928912768286064640 }, some { target := 570, numerator := 15280822359928912768286064640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 1392682544196052809261514752 }, some { target := 601, numerator := 1392682544196052809261514752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 613, numerator := 56132843656346461839957164032 }, some { target := 615, numerator := 56132843656346461839957164032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 618, numerator := 1353996917968384675670917120 }, some { target := 620, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 1353996917968384675670917120 }, some { target := 696, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 708, numerator := 1160568786830044007717928960 }, some { target := 710, numerator := 1160568786830044007717928960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 1353996917968384675670917120 }, some { target := 741, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 753, numerator := 15280822359928912768286064640 }, some { target := 755, numerator := 15280822359928912768286064640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1160568786830044007717928960 }, some { target := 760, numerator := 1160568786830044007717928960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 1353996917968384675670917120 }, some { target := 775, numerator := 1353996917968384675670917120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 778, numerator := 1199254413057712141308526592 }, some { target := 780, numerator := 1199254413057712141308526592 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 7, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[2061584302080, 36696200577024, 2061584302080, 32641751449600, 55731495632896, 2061584302080, 55731495632896, 55731495632896, 36696200577024, 2061584302080, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 5950181768415752969256960 }, some { target := 132, numerator := 105913235477800402852773888 }, some { target := 133, numerator := 5950181768415752969256960 }, some { target := 134, numerator := 94211211333249422013235200 }, some { target := 135, numerator := 160853247139505855268913152 }, some { target := 136, numerator := 5950181768415752969256960 }, some { target := 137, numerator := 160853247139505855268913152 }, some { target := 138, numerator := 160853247139505855268913152 }, some { target := 139, numerator := 105913235477800402852773888 }, some { target := 140, numerator := 5950181768415752969256960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 158671513824420079180185600 }, some { target := 228, numerator := 2824352946074677409407303680 }, some { target := 229, numerator := 158671513824420079180185600 }, some { target := 230, numerator := 2512298968886651253686272000 }, some { target := 231, numerator := 4289419923720156140504350720 }, some { target := 232, numerator := 158671513824420079180185600 }, some { target := 233, numerator := 4289419923720156140504350720 }, some { target := 234, numerator := 4289419923720156140504350720 }, some { target := 235, numerator := 2824352946074677409407303680 }, some { target := 236, numerator := 158671513824420079180185600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 151729635094601700716052480 }, some { target := 254, numerator := 2700787504683910272745734144 }, some { target := 255, numerator := 151729635094601700716052480 }, some { target := 256, numerator := 2402385888997860261337497600 }, some { target := 257, numerator := 4101757802057399309357285376 }, some { target := 258, numerator := 151729635094601700716052480 }, some { target := 259, numerator := 4101757802057399309357285376 }, some { target := 260, numerator := 4101757802057399309357285376 }, some { target := 261, numerator := 2700787504683910272745734144 }, some { target := 262, numerator := 151729635094601700716052480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 4958484807013127474380800 }, some { target := 303, numerator := 88261029564833669043978240 }, some { target := 304, numerator := 4958484807013127474380800 }, some { target := 305, numerator := 78509342777707851677696000 }, some { target := 306, numerator := 134044372616254879390760960 }, some { target := 307, numerator := 4958484807013127474380800 }, some { target := 308, numerator := 134044372616254879390760960 }, some { target := 309, numerator := 134044372616254879390760960 }, some { target := 310, numerator := 88261029564833669043978240 }, some { target := 311, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 155696422940212202695557120 }, some { target := 329, numerator := 2771396328335777207980916736 }, some { target := 330, numerator := 155696422940212202695557120 }, some { target := 331, numerator := 2465193363220026542679654400 }, some { target := 332, numerator := 4208993300150403212869894144 }, some { target := 333, numerator := 155696422940212202695557120 }, some { target := 334, numerator := 4208993300150403212869894144 }, some { target := 335, numerator := 4208993300150403212869894144 }, some { target := 336, numerator := 2771396328335777207980916736 }, some { target := 337, numerator := 155696422940212202695557120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 4958484807013127474380800 }, some { target := 343, numerator := 88261029564833669043978240 }, some { target := 344, numerator := 4958484807013127474380800 }, some { target := 345, numerator := 78509342777707851677696000 }, some { target := 346, numerator := 134044372616254879390760960 }, some { target := 347, numerator := 4958484807013127474380800 }, some { target := 348, numerator := 134044372616254879390760960 }, some { target := 349, numerator := 134044372616254879390760960 }, some { target := 350, numerator := 88261029564833669043978240 }, some { target := 351, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 151729635094601700716052480 }, some { target := 444, numerator := 2700787504683910272745734144 }, some { target := 445, numerator := 151729635094601700716052480 }, some { target := 446, numerator := 2402385888997860261337497600 }, some { target := 447, numerator := 4101757802057399309357285376 }, some { target := 448, numerator := 151729635094601700716052480 }, some { target := 449, numerator := 4101757802057399309357285376 }, some { target := 450, numerator := 4101757802057399309357285376 }, some { target := 451, numerator := 2700787504683910272745734144 }, some { target := 452, numerator := 151729635094601700716052480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 86277635642028418054225920 }, some { target := 470, numerator := 1535741914428105841365221376 }, some { target := 471, numerator := 86277635642028418054225920 }, some { target := 472, numerator := 1366062564332116619191910400 }, some { target := 473, numerator := 2332372083522834901399240704 }, some { target := 474, numerator := 86277635642028418054225920 }, some { target := 475, numerator := 2332372083522834901399240704 }, some { target := 476, numerator := 2332372083522834901399240704 }, some { target := 477, numerator := 1535741914428105841365221376 }, some { target := 478, numerator := 86277635642028418054225920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 155696422940212202695557120 }, some { target := 519, numerator := 2771396328335777207980916736 }, some { target := 520, numerator := 155696422940212202695557120 }, some { target := 521, numerator := 2465193363220026542679654400 }, some { target := 522, numerator := 4208993300150403212869894144 }, some { target := 523, numerator := 155696422940212202695557120 }, some { target := 524, numerator := 4208993300150403212869894144 }, some { target := 525, numerator := 4208993300150403212869894144 }, some { target := 526, numerator := 2771396328335777207980916736 }, some { target := 527, numerator := 155696422940212202695557120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 2430649252397835087941468160 }, some { target := 545, numerator := 43265556692681464565358133248 }, some { target := 546, numerator := 2430649252397835087941468160 }, some { target := 547, numerator := 38485279829632388892406579200 }, some { target := 548, numerator := 65708551456488141877351022592 }, some { target := 549, numerator := 2430649252397835087941468160 }, some { target := 550, numerator := 65708551456488141877351022592 }, some { target := 551, numerator := 65708551456488141877351022592 }, some { target := 552, numerator := 43265556692681464565358133248 }, some { target := 553, numerator := 2430649252397835087941468160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 95202908294652047508111360 }, some { target := 559, numerator := 1694611767644806445644382208 }, some { target := 560, numerator := 95202908294652047508111360 }, some { target := 561, numerator := 1507379381331990752211763200 }, some { target := 562, numerator := 2573651954232093684302610432 }, some { target := 563, numerator := 95202908294652047508111360 }, some { target := 564, numerator := 2573651954232093684302610432 }, some { target := 565, numerator := 2573651954232093684302610432 }, some { target := 566, numerator := 1694611767644806445644382208 }, some { target := 567, numerator := 95202908294652047508111360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 158671513824420079180185600 }, some { target := 590, numerator := 2824352946074677409407303680 }, some { target := 591, numerator := 158671513824420079180185600 }, some { target := 592, numerator := 2512298968886651253686272000 }, some { target := 593, numerator := 4289419923720156140504350720 }, some { target := 594, numerator := 158671513824420079180185600 }, some { target := 595, numerator := 4289419923720156140504350720 }, some { target := 596, numerator := 4289419923720156140504350720 }, some { target := 597, numerator := 2824352946074677409407303680 }, some { target := 598, numerator := 158671513824420079180185600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 151729635094601700716052480 }, some { target := 604, numerator := 2700787504683910272745734144 }, some { target := 605, numerator := 151729635094601700716052480 }, some { target := 606, numerator := 2402385888997860261337497600 }, some { target := 607, numerator := 4101757802057399309357285376 }, some { target := 608, numerator := 151729635094601700716052480 }, some { target := 609, numerator := 4101757802057399309357285376 }, some { target := 610, numerator := 4101757802057399309357285376 }, some { target := 611, numerator := 2700787504683910272745734144 }, some { target := 612, numerator := 151729635094601700716052480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 4958484807013127474380800 }, some { target := 659, numerator := 88261029564833669043978240 }, some { target := 660, numerator := 4958484807013127474380800 }, some { target := 661, numerator := 78509342777707851677696000 }, some { target := 662, numerator := 134044372616254879390760960 }, some { target := 663, numerator := 4958484807013127474380800 }, some { target := 664, numerator := 134044372616254879390760960 }, some { target := 665, numerator := 134044372616254879390760960 }, some { target := 666, numerator := 88261029564833669043978240 }, some { target := 667, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 95202908294652047508111360 }, some { target := 685, numerator := 1694611767644806445644382208 }, some { target := 686, numerator := 95202908294652047508111360 }, some { target := 687, numerator := 1507379381331990752211763200 }, some { target := 688, numerator := 2573651954232093684302610432 }, some { target := 689, numerator := 95202908294652047508111360 }, some { target := 690, numerator := 2573651954232093684302610432 }, some { target := 691, numerator := 2573651954232093684302610432 }, some { target := 692, numerator := 1694611767644806445644382208 }, some { target := 693, numerator := 95202908294652047508111360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 4958484807013127474380800 }, some { target := 699, numerator := 88261029564833669043978240 }, some { target := 700, numerator := 4958484807013127474380800 }, some { target := 701, numerator := 78509342777707851677696000 }, some { target := 702, numerator := 134044372616254879390760960 }, some { target := 703, numerator := 4958484807013127474380800 }, some { target := 704, numerator := 134044372616254879390760960 }, some { target := 705, numerator := 134044372616254879390760960 }, some { target := 706, numerator := 88261029564833669043978240 }, some { target := 707, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 152721332056004326210928640 }, some { target := 730, numerator := 2718439710596877006554529792 }, some { target := 731, numerator := 152721332056004326210928640 }, some { target := 732, numerator := 2418087757553401831673036800 }, some { target := 733, numerator := 4128566676580650285235437568 }, some { target := 734, numerator := 152721332056004326210928640 }, some { target := 735, numerator := 4128566676580650285235437568 }, some { target := 736, numerator := 4128566676580650285235437568 }, some { target := 737, numerator := 2718439710596877006554529792 }, some { target := 738, numerator := 152721332056004326210928640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 86277635642028418054225920 }, some { target := 744, numerator := 1535741914428105841365221376 }, some { target := 745, numerator := 86277635642028418054225920 }, some { target := 746, numerator := 1366062564332116619191910400 }, some { target := 747, numerator := 2332372083522834901399240704 }, some { target := 748, numerator := 86277635642028418054225920 }, some { target := 749, numerator := 2332372083522834901399240704 }, some { target := 750, numerator := 2332372083522834901399240704 }, some { target := 751, numerator := 1535741914428105841365221376 }, some { target := 752, numerator := 86277635642028418054225920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 5950181768415752969256960 }, some { target := 764, numerator := 105913235477800402852773888 }, some { target := 765, numerator := 5950181768415752969256960 }, some { target := 766, numerator := 94211211333249422013235200 }, some { target := 767, numerator := 160853247139505855268913152 }, some { target := 768, numerator := 5950181768415752969256960 }, some { target := 769, numerator := 160853247139505855268913152 }, some { target := 770, numerator := 160853247139505855268913152 }, some { target := 771, numerator := 105913235477800402852773888 }, some { target := 772, numerator := 5950181768415752969256960 }]

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

end Slot2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1
