import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 48; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 5, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 1242608628897589038342471680 }, some { target := 3, numerator := 1238982339124541599514624000 }, some { target := 4, numerator := 1230520996320764242249646080 }, some { target := 5, numerator := 1238982339124541599514624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 48468426999672496304768942080 }, some { target := 23, numerator := 48326982173797965673529344000 }, some { target := 24, numerator := 47996944246757394200636948480 }, some { target := 25, numerator := 48326982173797965673529344000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 48468409221622895267188572160 }, some { target := 73, numerator := 48326964447629832343257088000 }, some { target := 74, numerator := 47996926641646018854083624960 }, some { target := 75, numerator := 48326964447629832343257088000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 1242614554914122717535928320 }, some { target := 302, numerator := 1238988247847252709605376000 }, some { target := 303, numerator := 1230526864691222691100753920 }, some { target := 304, numerator := 1238988247847252709605376000 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 7, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 6148521160696278068232192 }, some { target := 12, numerator := 150737938133199075221176320 }, some { target := 13, numerator := 111466738461655105624080384 }, some { target := 14, numerator := 124358798959889237057470464 }, some { target := 15, numerator := 6148521160696278068232192 }, some { target := 16, numerator := 124160459567608711958495232 }, some { target := 17, numerator := 126342192882694488047222784 }, some { target := 18, numerator := 6148521160696278068232192 }, some { target := 19, numerator := 150737938133199075221176320 }, some { target := 20, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 92227817410444171023482880 }, some { target := 32, numerator := 2261069071997986128317644800 }, some { target := 33, numerator := 1672001076924826584361205760 }, some { target := 34, numerator := 1865381984398338555862056960 }, some { target := 35, numerator := 92227817410444171023482880 }, some { target := 36, numerator := 1862406893514130679377428480 }, some { target := 37, numerator := 1895132893240417320708341760 }, some { target := 38, numerator := 92227817410444171023482880 }, some { target := 39, numerator := 2261069071997986128317644800 }, some { target := 40, numerator := 92227817410444171023482880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 45, numerator := 161911057231668655796781056 }, some { target := 46, numerator := 3969432370840908980824309760 }, some { target := 47, numerator := 2935290779490251114767450112 }, some { target := 48, numerator := 3274781705943749909180055552 }, some { target := 49, numerator := 161911057231668655796781056 }, some { target := 50, numerator := 3269558768613696081573707776 }, some { target := 51, numerator := 3327011079244288185243533312 }, some { target := 52, numerator := 161911057231668655796781056 }, some { target := 53, numerator := 3969432370840908980824309760 }, some { target := 54, numerator := 161911057231668655796781056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 6148521160696278068232192 }, some { target := 77, numerator := 150737938133199075221176320 }, some { target := 78, numerator := 111466738461655105624080384 }, some { target := 79, numerator := 124358798959889237057470464 }, some { target := 80, numerator := 6148521160696278068232192 }, some { target := 81, numerator := 124160459567608711958495232 }, some { target := 82, numerator := 126342192882694488047222784 }, some { target := 83, numerator := 6148521160696278068232192 }, some { target := 84, numerator := 150737938133199075221176320 }, some { target := 85, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 102475352678271301137203200 }, some { target := 91, numerator := 2512298968886651253686272000 }, some { target := 92, numerator := 1857778974360918427068006400 }, some { target := 93, numerator := 2072646649331487284291174400 }, some { target := 94, numerator := 102475352678271301137203200 }, some { target := 95, numerator := 2069340992793478532641587200 }, some { target := 96, numerator := 2105703214711574800787046400 }, some { target := 97, numerator := 102475352678271301137203200 }, some { target := 98, numerator := 2512298968886651253686272000 }, some { target := 99, numerator := 102475352678271301137203200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 116, numerator := 6148521160696278068232192 }, some { target := 117, numerator := 150737938133199075221176320 }, some { target := 118, numerator := 111466738461655105624080384 }, some { target := 119, numerator := 124358798959889237057470464 }, some { target := 120, numerator := 6148521160696278068232192 }, some { target := 121, numerator := 124160459567608711958495232 }, some { target := 122, numerator := 126342192882694488047222784 }, some { target := 123, numerator := 6148521160696278068232192 }, some { target := 124, numerator := 150737938133199075221176320 }, some { target := 125, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 161911057231668655796781056 }, some { target := 172, numerator := 3969432370840908980824309760 }, some { target := 173, numerator := 2935290779490251114767450112 }, some { target := 174, numerator := 3274781705943749909180055552 }, some { target := 175, numerator := 161911057231668655796781056 }, some { target := 176, numerator := 3269558768613696081573707776 }, some { target := 177, numerator := 3327011079244288185243533312 }, some { target := 178, numerator := 161911057231668655796781056 }, some { target := 179, numerator := 3969432370840908980824309760 }, some { target := 180, numerator := 161911057231668655796781056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 185, numerator := 160886303704885942785409024 }, some { target := 186, numerator := 3944309381152042468287447040 }, some { target := 187, numerator := 2916712989746641930496770048 }, some { target := 188, numerator := 3254055239450435036337143808 }, some { target := 189, numerator := 160886303704885942785409024 }, some { target := 190, numerator := 3248865358685761296247291904 }, some { target := 191, numerator := 3305954047097172437235662848 }, some { target := 192, numerator := 160886303704885942785409024 }, some { target := 193, numerator := 3944309381152042468287447040 }, some { target := 194, numerator := 160886303704885942785409024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 102475352678271301137203200 }, some { target := 217, numerator := 2512298968886651253686272000 }, some { target := 218, numerator := 1857778974360918427068006400 }, some { target := 219, numerator := 2072646649331487284291174400 }, some { target := 220, numerator := 102475352678271301137203200 }, some { target := 221, numerator := 2069340992793478532641587200 }, some { target := 222, numerator := 2105703214711574800787046400 }, some { target := 223, numerator := 102475352678271301137203200 }, some { target := 224, numerator := 2512298968886651253686272000 }, some { target := 225, numerator := 102475352678271301137203200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 230, numerator := 2482977795394513626554433536 }, some { target := 231, numerator := 60873004016123559876818370560 }, some { target := 232, numerator := 45013984548765053487857795072 }, some { target := 233, numerator := 50220228313301936898375155712 }, some { target := 234, numerator := 2482977795394513626554433536 }, some { target := 235, numerator := 50140132255385984845905657856 }, some { target := 236, numerator := 51021188892461457423070134272 }, some { target := 237, numerator := 2482977795394513626554433536 }, some { target := 238, numerator := 60873004016123559876818370560 }, some { target := 239, numerator := 2482977795394513626554433536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 256, numerator := 158836796651320516762664960 }, some { target := 257, numerator := 3894063401774309443213721600 }, some { target := 258, numerator := 2879557410259423561955409920 }, some { target := 259, numerator := 3212602306463805290651320320 }, some { target := 260, numerator := 158836796651320516762664960 }, some { target := 261, numerator := 3207478538829891725594460160 }, some { target := 262, numerator := 3263839982802940941219921920 }, some { target := 263, numerator := 158836796651320516762664960 }, some { target := 264, numerator := 3894063401774309443213721600 }, some { target := 265, numerator := 158836796651320516762664960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 92227817410444171023482880 }, some { target := 306, numerator := 2261069071997986128317644800 }, some { target := 307, numerator := 1672001076924826584361205760 }, some { target := 308, numerator := 1865381984398338555862056960 }, some { target := 309, numerator := 92227817410444171023482880 }, some { target := 310, numerator := 1862406893514130679377428480 }, some { target := 311, numerator := 1895132893240417320708341760 }, some { target := 312, numerator := 92227817410444171023482880 }, some { target := 313, numerator := 2261069071997986128317644800 }, some { target := 314, numerator := 92227817410444171023482880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 161911057231668655796781056 }, some { target := 332, numerator := 3969432370840908980824309760 }, some { target := 333, numerator := 2935290779490251114767450112 }, some { target := 334, numerator := 3274781705943749909180055552 }, some { target := 335, numerator := 161911057231668655796781056 }, some { target := 336, numerator := 3269558768613696081573707776 }, some { target := 337, numerator := 3327011079244288185243533312 }, some { target := 338, numerator := 161911057231668655796781056 }, some { target := 339, numerator := 3969432370840908980824309760 }, some { target := 340, numerator := 161911057231668655796781056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 6148521160696278068232192 }, some { target := 433, numerator := 150737938133199075221176320 }, some { target := 434, numerator := 111466738461655105624080384 }, some { target := 435, numerator := 124358798959889237057470464 }, some { target := 436, numerator := 6148521160696278068232192 }, some { target := 437, numerator := 124160459567608711958495232 }, some { target := 438, numerator := 126342192882694488047222784 }, some { target := 439, numerator := 6148521160696278068232192 }, some { target := 440, numerator := 150737938133199075221176320 }, some { target := 441, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 446, numerator := 158836796651320516762664960 }, some { target := 447, numerator := 3894063401774309443213721600 }, some { target := 448, numerator := 2879557410259423561955409920 }, some { target := 449, numerator := 3212602306463805290651320320 }, some { target := 450, numerator := 158836796651320516762664960 }, some { target := 451, numerator := 3207478538829891725594460160 }, some { target := 452, numerator := 3263839982802940941219921920 }, some { target := 453, numerator := 158836796651320516762664960 }, some { target := 454, numerator := 3894063401774309443213721600 }, some { target := 455, numerator := 158836796651320516762664960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 472, numerator := 6148521160696278068232192 }, some { target := 473, numerator := 150737938133199075221176320 }, some { target := 474, numerator := 111466738461655105624080384 }, some { target := 475, numerator := 124358798959889237057470464 }, some { target := 476, numerator := 6148521160696278068232192 }, some { target := 477, numerator := 124160459567608711958495232 }, some { target := 478, numerator := 126342192882694488047222784 }, some { target := 479, numerator := 6148521160696278068232192 }, some { target := 480, numerator := 150737938133199075221176320 }, some { target := 481, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 521, numerator := 161911057231668655796781056 }, some { target := 522, numerator := 3969432370840908980824309760 }, some { target := 523, numerator := 2935290779490251114767450112 }, some { target := 524, numerator := 3274781705943749909180055552 }, some { target := 525, numerator := 161911057231668655796781056 }, some { target := 526, numerator := 3269558768613696081573707776 }, some { target := 527, numerator := 3327011079244288185243533312 }, some { target := 528, numerator := 161911057231668655796781056 }, some { target := 529, numerator := 3969432370840908980824309760 }, some { target := 530, numerator := 161911057231668655796781056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 547, numerator := 161911057231668655796781056 }, some { target := 548, numerator := 3969432370840908980824309760 }, some { target := 549, numerator := 2935290779490251114767450112 }, some { target := 550, numerator := 3274781705943749909180055552 }, some { target := 551, numerator := 161911057231668655796781056 }, some { target := 552, numerator := 3269558768613696081573707776 }, some { target := 553, numerator := 3327011079244288185243533312 }, some { target := 554, numerator := 161911057231668655796781056 }, some { target := 555, numerator := 3969432370840908980824309760 }, some { target := 556, numerator := 161911057231668655796781056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 6148521160696278068232192 }, some { target := 644, numerator := 150737938133199075221176320 }, some { target := 645, numerator := 111466738461655105624080384 }, some { target := 646, numerator := 124358798959889237057470464 }, some { target := 647, numerator := 6148521160696278068232192 }, some { target := 648, numerator := 124160459567608711958495232 }, some { target := 649, numerator := 126342192882694488047222784 }, some { target := 650, numerator := 6148521160696278068232192 }, some { target := 651, numerator := 150737938133199075221176320 }, some { target := 652, numerator := 6148521160696278068232192 }]

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

end Slot14

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2
