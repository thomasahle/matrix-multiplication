import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 561, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

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
  [some { target := 71, numerator := 47872731965673996420120576 }, some { target := 72, numerator := 5658249564226933450422091776 }, some { target := 74, numerator := 53695660468046469432644468736 }, some { target := 82, numerator := 5658253444960717957069012992 }, some { target := 89, numerator := 47872731965673996420120576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 718090979485109946301808640 }, some { target := 147, numerator := 84873743463404001756331376640 }, some { target := 149, numerator := 805434907020697041489667031040 }, some { target := 157, numerator := 84873801674410769356035194880 }, some { target := 164, numerator := 718090979485109946301808640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 1260648608429415239063175168 }, some { target := 182, numerator := 149000571857975914194448416768 }, some { target := 184, numerator := 1413985725658557028392971010048 }, some { target := 192, numerator := 149000674050632239536150675456 }, some { target := 199, numerator := 1260648608429415239063175168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 47872731965673996420120576 }, some { target := 243, numerator := 5658249564226933450422091776 }, some { target := 245, numerator := 53695660468046469432644468736 }, some { target := 253, numerator := 5658253444960717957069012992 }, some { target := 260, numerator := 47872731965673996420120576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 797878866094566607002009600 }, some { target := 278, numerator := 94304159403782224173701529600 }, some { target := 280, numerator := 894927674467441157210741145600 }, some { target := 288, numerator := 94304224082678632617816883200 }, some { target := 295, numerator := 797878866094566607002009600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 47872731965673996420120576 }, some { target := 313, numerator := 5658249564226933450422091776 }, some { target := 315, numerator := 53695660468046469432644468736 }, some { target := 323, numerator := 5658253444960717957069012992 }, some { target := 330, numerator := 47872731965673996420120576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 1260648608429415239063175168 }, some { target := 414, numerator := 149000571857975914194448416768 }, some { target := 416, numerator := 1413985725658557028392971010048 }, some { target := 424, numerator := 149000674050632239536150675456 }, some { target := 431, numerator := 1260648608429415239063175168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 1252669819768469572993155072 }, some { target := 449, numerator := 148057530263938091952711401472 }, some { target := 451, numerator := 1405036448913882616820863598592 }, some { target := 459, numerator := 148057631809805453209972506624 }, some { target := 466, numerator := 1252669819768469572993155072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 797878866094566607002009600 }, some { target := 510, numerator := 94304159403782224173701529600 }, some { target := 512, numerator := 894927674467441157210741145600 }, some { target := 520, numerator := 94304224082678632617816883200 }, some { target := 527, numerator := 797878866094566607002009600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 19332604925471348887658692608 }, some { target := 545, numerator := 2284989782353643291728788062208 }, some { target := 547, numerator := 21684097552346099239216257957888 }, some { target := 555, numerator := 2284991349523303268329703079936 }, some { target := 562, numerator := 19332604925471348887658692608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 1236712242446578240853114880 }, some { target := 580, numerator := 146171447075862447469237370880 }, some { target := 582, numerator := 1387137895424533793676648775680 }, some { target := 590, numerator := 146171547328151880557616168960 }, some { target := 597, numerator := 1236712242446578240853114880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 718090979485109946301808640 }, some { target := 641, numerator := 84873743463404001756331376640 }, some { target := 643, numerator := 805434907020697041489667031040 }, some { target := 651, numerator := 84873801674410769356035194880 }, some { target := 658, numerator := 718090979485109946301808640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 1260648608429415239063175168 }, some { target := 676, numerator := 149000571857975914194448416768 }, some { target := 678, numerator := 1413985725658557028392971010048 }, some { target := 686, numerator := 149000674050632239536150675456 }, some { target := 693, numerator := 1260648608429415239063175168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 47872731965673996420120576 }, some { target := 777, numerator := 5658249564226933450422091776 }, some { target := 779, numerator := 53695660468046469432644468736 }, some { target := 787, numerator := 5658253444960717957069012992 }, some { target := 794, numerator := 47872731965673996420120576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 1236712242446578240853114880 }, some { target := 812, numerator := 146171447075862447469237370880 }, some { target := 814, numerator := 1387137895424533793676648775680 }, some { target := 822, numerator := 146171547328151880557616168960 }, some { target := 829, numerator := 1236712242446578240853114880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 47872731965673996420120576 }, some { target := 847, numerator := 5658249564226933450422091776 }, some { target := 849, numerator := 53695660468046469432644468736 }, some { target := 857, numerator := 5658253444960717957069012992 }, some { target := 864, numerator := 47872731965673996420120576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 1260648608429415239063175168 }, some { target := 908, numerator := 149000571857975914194448416768 }, some { target := 910, numerator := 1413985725658557028392971010048 }, some { target := 918, numerator := 149000674050632239536150675456 }, some { target := 925, numerator := 1260648608429415239063175168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 1260648608429415239063175168 }, some { target := 943, numerator := 149000571857975914194448416768 }, some { target := 945, numerator := 1413985725658557028392971010048 }, some { target := 953, numerator := 149000674050632239536150675456 }, some { target := 960, numerator := 1260648608429415239063175168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 47872731965673996420120576 }, some { target := 1018, numerator := 5658249564226933450422091776 }, some { target := 1020, numerator := 53695660468046469432644468736 }, some { target := 1028, numerator := 5658253444960717957069012992 }, some { target := 1035, numerator := 47872731965673996420120576 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 7, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 742570030231851405810860032 }, some { target := 6, numerator := 17989357829165174379482447872 }, some { target := 7, numerator := 13629753135545917738915463168 }, some { target := 8, numerator := 15186754811838509396260814848 }, some { target := 9, numerator := 742570030231851405810860032 }, some { target := 10, numerator := 15186754811838509396260814848 }, some { target := 11, numerator := 15162800939895546447686270976 }, some { target := 12, numerator := 742570030231851405810860032 }, some { target := 13, numerator := 17989357829165174379482447872 }, some { target := 14, numerator := 742570030231851405810860032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 2712250635422256182643916800 }, some { target := 95, numerator := 65706458942003690102115532800 }, some { target := 96, numerator := 49782922953395605416915763200 }, some { target := 97, numerator := 55469900092184207090201395200 }, some { target := 98, numerator := 2712250635422256182643916800 }, some { target := 99, numerator := 55469900092184207090201395200 }, some { target := 100, numerator := 55382408136202843987535462400 }, some { target := 101, numerator := 2712250635422256182643916800 }, some { target := 102, numerator := 65706458942003690102115532800 }, some { target := 103, numerator := 2712250635422256182643916800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 742569780047884906125066240 }, some { target := 217, numerator := 17989351768256824661287895040 }, some { target := 218, numerator := 13629748543459564889843957760 }, some { target := 219, numerator := 15186749695172871951073935360 }, some { target := 220, numerator := 742569780047884906125066240 }, some { target := 221, numerator := 15186749695172871951073935360 }, some { target := 222, numerator := 15162795831300359534747320320 }, some { target := 223, numerator := 742569780047884906125066240 }, some { target := 224, numerator := 17989351768256824661287895040 }, some { target := 225, numerator := 742569780047884906125066240 }]

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

end Slot10

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
