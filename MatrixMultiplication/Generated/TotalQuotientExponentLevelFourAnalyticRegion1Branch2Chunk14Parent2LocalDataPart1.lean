import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 60; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 224, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 101850376989054021528453120 }, some { target := 122, numerator := 16260126798662820186386595840 }, some { target := 124, numerator := 162251613457592411317799485440 }, some { target := 132, numerator := 16260126798662820186386595840 }, some { target := 139, numerator := 101838755540287584510935040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 79216959880375350077685760 }, some { target := 197, numerator := 12646765287848860144967352320 }, some { target := 199, numerator := 126195699355905208802732933120 }, some { target := 207, numerator := 12646765287848860144967352320 }, some { target := 214, numerator := 79207920975779232397393920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 90533668434714685803069440 }, some { target := 232, numerator := 14453446043255840165676974080 }, some { target := 234, numerator := 144223656406748810060266209280 }, some { target := 242, numerator := 14453446043255840165676974080 }, some { target := 249, numerator := 90523338258033408454164480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 106377060410789755818606592 }, some { target := 338, numerator := 16982799100825612194670444544 }, some { target := 340, numerator := 169462796277929851820812795904 }, some { target := 348, numerator := 16982799100825612194670444544 }, some { target := 355, numerator := 106364922453189254933643264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 1256154649531666265517588480 }, some { target := 413, numerator := 200541563850174782298768015360 }, some { target := 415, numerator := 2001103232643639739586193653760 }, some { target := 423, numerator := 200541563850174782298768015360 }, some { target := 430, numerator := 1256011318330213542301532160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 2824650455163098197055766528 }, some { target := 448, numerator := 450947516549582213169121591296 }, some { target := 450, numerator := 4499778079890562873880305729536 }, some { target := 458, numerator := 450947516549582213169121591296 }, some { target := 465, numerator := 2824328153650642343769931776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 79216959880375350077685760 }, some { target := 509, numerator := 12646765287848860144967352320 }, some { target := 511, numerator := 126195699355905208802732933120 }, some { target := 519, numerator := 12646765287848860144967352320 }, some { target := 526, numerator := 79207920975779232397393920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 1256154649531666265517588480 }, some { target := 544, numerator := 200541563850174782298768015360 }, some { target := 546, numerator := 2001103232643639739586193653760 }, some { target := 554, numerator := 200541563850174782298768015360 }, some { target := 561, numerator := 1256011318330213542301532160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 90533668434714685803069440 }, some { target := 579, numerator := 14453446043255840165676974080 }, some { target := 581, numerator := 144223656406748810060266209280 }, some { target := 589, numerator := 14453446043255840165676974080 }, some { target := 596, numerator := 90523338258033408454164480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 88270326723846818657992704 }, some { target := 680, numerator := 14092109892174444161535049728 }, some { target := 682, numerator := 140618064996580089808759554048 }, some { target := 690, numerator := 14092109892174444161535049728 }, some { target := 697, numerator := 88260254801582573242810368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 88270326723846818657992704 }, some { target := 715, numerator := 14092109892174444161535049728 }, some { target := 717, numerator := 140618064996580089808759554048 }, some { target := 725, numerator := 14092109892174444161535049728 }, some { target := 732, numerator := 88260254801582573242810368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 88270326723846818657992704 }, some { target := 776, numerator := 14092109892174444161535049728 }, some { target := 778, numerator := 140618064996580089808759554048 }, some { target := 786, numerator := 14092109892174444161535049728 }, some { target := 793, numerator := 88260254801582573242810368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 2824650455163098197055766528 }, some { target := 811, numerator := 450947516549582213169121591296 }, some { target := 813, numerator := 4499778079890562873880305729536 }, some { target := 821, numerator := 450947516549582213169121591296 }, some { target := 828, numerator := 2824328153650642343769931776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 88270326723846818657992704 }, some { target := 846, numerator := 14092109892174444161535049728 }, some { target := 848, numerator := 140618064996580089808759554048 }, some { target := 856, numerator := 14092109892174444161535049728 }, some { target := 863, numerator := 88260254801582573242810368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 101850376989054021528453120 }, some { target := 907, numerator := 16260126798662820186386595840 }, some { target := 909, numerator := 162251613457592411317799485440 }, some { target := 917, numerator := 16260126798662820186386595840 }, some { target := 924, numerator := 101838755540287584510935040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 106377060410789755818606592 }, some { target := 942, numerator := 16982799100825612194670444544 }, some { target := 944, numerator := 169462796277929851820812795904 }, some { target := 952, numerator := 16982799100825612194670444544 }, some { target := 959, numerator := 106364922453189254933643264 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 225, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 102305066172040869838848000 }, some { target := 35, numerator := 79570607022698454319104000 }, some { target := 36, numerator := 90937836597369662078976000 }, some { target := 37, numerator := 106851958001909352942796800 }, some { target := 38, numerator := 1261762482788504061345792000 }, some { target := 39, numerator := 2837260501837933456864051200 }, some { target := 40, numerator := 79570607022698454319104000 }, some { target := 41, numerator := 1261762482788504061345792000 }, some { target := 42, numerator := 90937836597369662078976000 }, some { target := 43, numerator := 88664390682435420527001600 }, some { target := 44, numerator := 88664390682435420527001600 }, some { target := 45, numerator := 88664390682435420527001600 }, some { target := 46, numerator := 2837260501837933456864051200 }, some { target := 47, numerator := 88664390682435420527001600 }, some { target := 48, numerator := 102305066172040869838848000 }, some { target := 49, numerator := 106851958001909352942796800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 16332716650442564919361536000 }, some { target := 80, numerator := 12703224061455328270614528000 }, some { target := 81, numerator := 14517970355948946594988032000 }, some { target := 82, numerator := 17058615168240012249110937600 }, some { target := 83, numerator := 201436838688791634005458944000 }, some { target := 84, numerator := 452960675105607133763626598400 }, some { target := 85, numerator := 12703224061455328270614528000 }, some { target := 86, numerator := 201436838688791634005458944000 }, some { target := 87, numerator := 14517970355948946594988032000 }, some { target := 88, numerator := 14155021097050222930113331200 }, some { target := 89, numerator := 14155021097050222930113331200 }, some { target := 90, numerator := 14155021097050222930113331200 }, some { target := 91, numerator := 452960675105607133763626598400 }, some { target := 92, numerator := 14155021097050222930113331200 }, some { target := 93, numerator := 16332716650442564919361536000 }, some { target := 94, numerator := 17058615168240012249110937600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 162975951017670948868325376000 }, some { target := 155, numerator := 126759073013744071342030848000 }, some { target := 156, numerator := 144867512015707510105178112000 }, some { target := 157, numerator := 170219326618456324373584281600 }, some { target := 158, numerator := 2010036729217941702709346304000 }, some { target := 159, numerator := 4519866374890074315281557094400 }, some { target := 160, numerator := 126759073013744071342030848000 }, some { target := 161, numerator := 2010036729217941702709346304000 }, some { target := 162, numerator := 144867512015707510105178112000 }, some { target := 163, numerator := 141245824215314822352548659200 }, some { target := 164, numerator := 141245824215314822352548659200 }, some { target := 165, numerator := 141245824215314822352548659200 }, some { target := 166, numerator := 4519866374890074315281557094400 }, some { target := 167, numerator := 141245824215314822352548659200 }, some { target := 168, numerator := 162975951017670948868325376000 }, some { target := 169, numerator := 170219326618456324373584281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 16332716650442564919361536000 }, some { target := 493, numerator := 12703224061455328270614528000 }, some { target := 494, numerator := 14517970355948946594988032000 }, some { target := 495, numerator := 17058615168240012249110937600 }, some { target := 496, numerator := 201436838688791634005458944000 }, some { target := 497, numerator := 452960675105607133763626598400 }, some { target := 498, numerator := 12703224061455328270614528000 }, some { target := 499, numerator := 201436838688791634005458944000 }, some { target := 500, numerator := 14517970355948946594988032000 }, some { target := 501, numerator := 14155021097050222930113331200 }, some { target := 502, numerator := 14155021097050222930113331200 }, some { target := 503, numerator := 14155021097050222930113331200 }, some { target := 504, numerator := 452960675105607133763626598400 }, some { target := 505, numerator := 14155021097050222930113331200 }, some { target := 506, numerator := 16332716650442564919361536000 }, some { target := 507, numerator := 17058615168240012249110937600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 102293392841806725513216000 }, some { target := 891, numerator := 79561527765849675399168000 }, some { target := 892, numerator := 90927460303828200456192000 }, some { target := 893, numerator := 106839765856998135536025600 }, some { target := 894, numerator := 1261618511715616281329664000 }, some { target := 895, numerator := 2836936761479439854233190400 }, some { target := 896, numerator := 79561527765849675399168000 }, some { target := 897, numerator := 1261618511715616281329664000 }, some { target := 898, numerator := 90927460303828200456192000 }, some { target := 899, numerator := 88654273796232495444787200 }, some { target := 900, numerator := 88654273796232495444787200 }, some { target := 901, numerator := 88654273796232495444787200 }, some { target := 902, numerator := 2836936761479439854233190400 }, some { target := 903, numerator := 88654273796232495444787200 }, some { target := 904, numerator := 102293392841806725513216000 }, some { target := 905, numerator := 106839765856998135536025600 }]

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

end Slot7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2
