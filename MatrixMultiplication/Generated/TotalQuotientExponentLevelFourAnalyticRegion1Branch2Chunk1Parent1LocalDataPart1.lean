import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 555, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648]⟩

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
  [some { target := 71, numerator := 48001875315091027777290240 }, some { target := 72, numerator := 5032910052182131077399183360 }, some { target := 74, numerator := 54249739974844387877191680000 }, some { target := 82, numerator := 5032913891410741418199613440 }, some { target := 89, numerator := 48001875315091027777290240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 1280050008402427407394406400 }, some { target := 147, numerator := 134210934724856828730644889600 }, some { target := 149, numerator := 1446659732662517010058444800000 }, some { target := 157, numerator := 134211037104286437818656358400 }, some { target := 164, numerator := 1280050008402427407394406400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 1224047820534821208320901120 }, some { target := 182, numerator := 128339206330644342473679175680 }, some { target := 184, numerator := 1383368369358531890868387840000 }, some { target := 192, numerator := 128339304230973906164090142720 }, some { target := 199, numerator := 1224047820534821208320901120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 40001562762575856481075200 }, some { target := 243, numerator := 4194091710151775897832652800 }, some { target := 245, numerator := 45208116645703656564326400000 }, some { target := 253, numerator := 4194094909508951181833011200 }, some { target := 260, numerator := 40001562762575856481075200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 1256049070744881893505761280 }, some { target := 278, numerator := 131694479698765763191945297920 }, some { target := 280, numerator := 1419534862675094816119848960000 }, some { target := 288, numerator := 131694580158581067109556551680 }, some { target := 295, numerator := 1256049070744881893505761280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 40001562762575856481075200 }, some { target := 313, numerator := 4194091710151775897832652800 }, some { target := 315, numerator := 45208116645703656564326400000 }, some { target := 323, numerator := 4194094909508951181833011200 }, some { target := 330, numerator := 40001562762575856481075200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 1224047820534821208320901120 }, some { target := 414, numerator := 128339206330644342473679175680 }, some { target := 416, numerator := 1383368369358531890868387840000 }, some { target := 424, numerator := 128339304230973906164090142720 }, some { target := 431, numerator := 1224047820534821208320901120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 696027192068819902770708480 }, some { target := 449, numerator := 72977195756640900622288158720 }, some { target := 451, numerator := 786621229635243624219279360000 }, some { target := 459, numerator := 72977251425455750563894394880 }, some { target := 466, numerator := 696027192068819902770708480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 1256049070744881893505761280 }, some { target := 510, numerator := 131694479698765763191945297920 }, some { target := 512, numerator := 1419534862675094816119848960000 }, some { target := 520, numerator := 131694580158581067109556551680 }, some { target := 527, numerator := 1256049070744881893505761280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 19608766066214684847023063040 }, some { target := 545, numerator := 2055943756316400545117566402560 }, some { target := 547, numerator := 22161018779723932447832801280000 }, some { target := 555, numerator := 2055945324641287869334542090240 }, some { target := 562, numerator := 19608766066214684847023063040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 768030005041456444436643840 }, some { target := 580, numerator := 80526560834914097238386933760 }, some { target := 582, numerator := 867995839597510206035066880000 }, some { target := 590, numerator := 80526622262571862691193815040 }, some { target := 597, numerator := 768030005041456444436643840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 1280050008402427407394406400 }, some { target := 641, numerator := 134210934724856828730644889600 }, some { target := 643, numerator := 1446659732662517010058444800000 }, some { target := 651, numerator := 134211037104286437818656358400 }, some { target := 658, numerator := 1280050008402427407394406400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 1224047820534821208320901120 }, some { target := 676, numerator := 128339206330644342473679175680 }, some { target := 678, numerator := 1383368369358531890868387840000 }, some { target := 686, numerator := 128339304230973906164090142720 }, some { target := 693, numerator := 1224047820534821208320901120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 40001562762575856481075200 }, some { target := 777, numerator := 4194091710151775897832652800 }, some { target := 779, numerator := 45208116645703656564326400000 }, some { target := 787, numerator := 4194094909508951181833011200 }, some { target := 794, numerator := 40001562762575856481075200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 768030005041456444436643840 }, some { target := 812, numerator := 80526560834914097238386933760 }, some { target := 814, numerator := 867995839597510206035066880000 }, some { target := 822, numerator := 80526622262571862691193815040 }, some { target := 829, numerator := 768030005041456444436643840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 40001562762575856481075200 }, some { target := 847, numerator := 4194091710151775897832652800 }, some { target := 849, numerator := 45208116645703656564326400000 }, some { target := 857, numerator := 4194094909508951181833011200 }, some { target := 864, numerator := 40001562762575856481075200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 1232048133087336379617116160 }, some { target := 908, numerator := 129178024672674697653245706240 }, some { target := 910, numerator := 1392409992687672622181253120000 }, some { target := 918, numerator := 129178123212875696400456744960 }, some { target := 925, numerator := 1232048133087336379617116160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 696027192068819902770708480 }, some { target := 943, numerator := 72977195756640900622288158720 }, some { target := 945, numerator := 786621229635243624219279360000 }, some { target := 953, numerator := 72977251425455750563894394880 }, some { target := 960, numerator := 696027192068819902770708480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 48001875315091027777290240 }, some { target := 1018, numerator := 5032910052182131077399183360 }, some { target := 1020, numerator := 54249739974844387877191680000 }, some { target := 1028, numerator := 5032913891410741418199613440 }, some { target := 1035, numerator := 48001875315091027777290240 }]

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

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 50, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 273947984552642123661312000 }, some { target := 30, numerator := 22937427752048238030697267200 }, some { target := 35, numerator := 22937436053083071199995494400 }, some { target := 43, numerator := 273939683517808954363084800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 268240734874462079418368000 }, some { target := 56, numerator := 22459564673880566405057740800 }, some { target := 61, numerator := 22459572801977173883328921600 }, some { target := 69, numerator := 268232606777854601147187200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 211168238092661636988928000 }, some { target := 105, numerator := 17680933892203850148662476800 }, some { target := 110, numerator := 17680940290918200716663193600 }, some { target := 118, numerator := 211161839378311068988211200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 130, numerator := 6637531375723391454543872000 }, some { target := 131, numerator := 555754759909002100618769203200 }, some { target := 136, numerator := 555754961036158579283224166400 }, some { target := 144, numerator := 6637330248566912790088908800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 165, numerator := 211168238092661636988928000 }, some { target := 166, numerator := 17680933892203850148662476800 }, some { target := 171, numerator := 17680940290918200716663193600 }, some { target := 179, numerator := 211161839378311068988211200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 211168238092661636988928000 }, some { target := 227, numerator := 17680933892203850148662476800 }, some { target := 232, numerator := 17680940290918200716663193600 }, some { target := 240, numerator := 211161839378311068988211200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 261, numerator := 216875487770841681231872000 }, some { target := 262, numerator := 18158796970371521774302003200 }, some { target := 267, numerator := 18158803542024098033329766400 }, some { target := 275, numerator := 216868916118265422204108800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 371, numerator := 216875487770841681231872000 }, some { target := 372, numerator := 18158796970371521774302003200 }, some { target := 377, numerator := 18158803542024098033329766400 }, some { target := 385, numerator := 216868916118265422204108800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 397, numerator := 3669761543069768448212992000 }, some { target := 398, numerator := 307265959261812855286215475200 }, some { target := 403, numerator := 307266070461091974616606310400 }, some { target := 411, numerator := 3669650343790649117822156800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 199753738736301548503040000 }, some { target := 433, numerator := 16725207735868506897383424000 }, some { target := 438, numerator := 16725213788706406083330048000 }, some { target := 446, numerator := 199747685898402362556416000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 493, numerator := 6637531375723391454543872000 }, some { target := 494, numerator := 555754759909002100618769203200 }, some { target := 499, numerator := 555754961036158579283224166400 }, some { target := 507, numerator := 6637330248566912790088908800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 3669761543069768448212992000 }, some { target := 529, numerator := 307265959261812855286215475200 }, some { target := 534, numerator := 307266070461091974616606310400 }, some { target := 542, numerator := 3669650343790649117822156800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 273947984552642123661312000 }, some { target := 625, numerator := 22937427752048238030697267200 }, some { target := 630, numerator := 22937436053083071199995494400 }, some { target := 638, numerator := 273939683517808954363084800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 760, numerator := 211168238092661636988928000 }, some { target := 761, numerator := 17680933892203850148662476800 }, some { target := 766, numerator := 17680940290918200716663193600 }, some { target := 774, numerator := 211161839378311068988211200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 795, numerator := 199753738736301548503040000 }, some { target := 796, numerator := 16725207735868506897383424000 }, some { target := 801, numerator := 16725213788706406083330048000 }, some { target := 809, numerator := 199747685898402362556416000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 891, numerator := 268240734874462079418368000 }, some { target := 892, numerator := 22459564673880566405057740800 }, some { target := 897, numerator := 22459572801977173883328921600 }, some { target := 905, numerator := 268232606777854601147187200 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 0, #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 0, #[70437463654400, 69956427317248, 70437463654400, 70643622084608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
