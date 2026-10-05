import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 48; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 7, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 142, numerator := 6148521160696278068232192 }, some { target := 143, numerator := 92227817410444171023482880 }, some { target := 144, numerator := 161911057231668655796781056 }, some { target := 145, numerator := 6148521160696278068232192 }, some { target := 146, numerator := 102475352678271301137203200 }, some { target := 147, numerator := 6148521160696278068232192 }, some { target := 148, numerator := 161911057231668655796781056 }, some { target := 149, numerator := 160886303704885942785409024 }, some { target := 150, numerator := 102475352678271301137203200 }, some { target := 151, numerator := 2482977795394513626554433536 }, some { target := 152, numerator := 158836796651320516762664960 }, some { target := 153, numerator := 92227817410444171023482880 }, some { target := 154, numerator := 161911057231668655796781056 }, some { target := 155, numerator := 6148521160696278068232192 }, some { target := 156, numerator := 158836796651320516762664960 }, some { target := 157, numerator := 6148521160696278068232192 }, some { target := 158, numerator := 161911057231668655796781056 }, some { target := 159, numerator := 161911057231668655796781056 }, some { target := 160, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 150737938133199075221176320 }, some { target := 283, numerator := 2261069071997986128317644800 }, some { target := 284, numerator := 3969432370840908980824309760 }, some { target := 285, numerator := 150737938133199075221176320 }, some { target := 286, numerator := 2512298968886651253686272000 }, some { target := 287, numerator := 150737938133199075221176320 }, some { target := 288, numerator := 3969432370840908980824309760 }, some { target := 289, numerator := 3944309381152042468287447040 }, some { target := 290, numerator := 2512298968886651253686272000 }, some { target := 291, numerator := 60873004016123559876818370560 }, some { target := 292, numerator := 3894063401774309443213721600 }, some { target := 293, numerator := 2261069071997986128317644800 }, some { target := 294, numerator := 3969432370840908980824309760 }, some { target := 295, numerator := 150737938133199075221176320 }, some { target := 296, numerator := 3894063401774309443213721600 }, some { target := 297, numerator := 150737938133199075221176320 }, some { target := 298, numerator := 3969432370840908980824309760 }, some { target := 299, numerator := 3969432370840908980824309760 }, some { target := 300, numerator := 150737938133199075221176320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 111466738461655105624080384 }, some { target := 358, numerator := 1672001076924826584361205760 }, some { target := 359, numerator := 2935290779490251114767450112 }, some { target := 360, numerator := 111466738461655105624080384 }, some { target := 361, numerator := 1857778974360918427068006400 }, some { target := 362, numerator := 111466738461655105624080384 }, some { target := 363, numerator := 2935290779490251114767450112 }, some { target := 364, numerator := 2916712989746641930496770048 }, some { target := 365, numerator := 1857778974360918427068006400 }, some { target := 366, numerator := 45013984548765053487857795072 }, some { target := 367, numerator := 2879557410259423561955409920 }, some { target := 368, numerator := 1672001076924826584361205760 }, some { target := 369, numerator := 2935290779490251114767450112 }, some { target := 370, numerator := 111466738461655105624080384 }, some { target := 371, numerator := 2879557410259423561955409920 }, some { target := 372, numerator := 111466738461655105624080384 }, some { target := 373, numerator := 2935290779490251114767450112 }, some { target := 374, numerator := 2935290779490251114767450112 }, some { target := 375, numerator := 111466738461655105624080384 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 124358798959889237057470464 }, some { target := 393, numerator := 1865381984398338555862056960 }, some { target := 394, numerator := 3274781705943749909180055552 }, some { target := 395, numerator := 124358798959889237057470464 }, some { target := 396, numerator := 2072646649331487284291174400 }, some { target := 397, numerator := 124358798959889237057470464 }, some { target := 398, numerator := 3274781705943749909180055552 }, some { target := 399, numerator := 3254055239450435036337143808 }, some { target := 400, numerator := 2072646649331487284291174400 }, some { target := 401, numerator := 50220228313301936898375155712 }, some { target := 402, numerator := 3212602306463805290651320320 }, some { target := 403, numerator := 1865381984398338555862056960 }, some { target := 404, numerator := 3274781705943749909180055552 }, some { target := 405, numerator := 124358798959889237057470464 }, some { target := 406, numerator := 3212602306463805290651320320 }, some { target := 407, numerator := 124358798959889237057470464 }, some { target := 408, numerator := 3274781705943749909180055552 }, some { target := 409, numerator := 3274781705943749909180055552 }, some { target := 410, numerator := 124358798959889237057470464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 6148521160696278068232192 }, some { target := 499, numerator := 92227817410444171023482880 }, some { target := 500, numerator := 161911057231668655796781056 }, some { target := 501, numerator := 6148521160696278068232192 }, some { target := 502, numerator := 102475352678271301137203200 }, some { target := 503, numerator := 6148521160696278068232192 }, some { target := 504, numerator := 161911057231668655796781056 }, some { target := 505, numerator := 160886303704885942785409024 }, some { target := 506, numerator := 102475352678271301137203200 }, some { target := 507, numerator := 2482977795394513626554433536 }, some { target := 508, numerator := 158836796651320516762664960 }, some { target := 509, numerator := 92227817410444171023482880 }, some { target := 510, numerator := 161911057231668655796781056 }, some { target := 511, numerator := 6148521160696278068232192 }, some { target := 512, numerator := 158836796651320516762664960 }, some { target := 513, numerator := 6148521160696278068232192 }, some { target := 514, numerator := 161911057231668655796781056 }, some { target := 515, numerator := 161911057231668655796781056 }, some { target := 516, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 124160459567608711958495232 }, some { target := 574, numerator := 1862406893514130679377428480 }, some { target := 575, numerator := 3269558768613696081573707776 }, some { target := 576, numerator := 124160459567608711958495232 }, some { target := 577, numerator := 2069340992793478532641587200 }, some { target := 578, numerator := 124160459567608711958495232 }, some { target := 579, numerator := 3269558768613696081573707776 }, some { target := 580, numerator := 3248865358685761296247291904 }, some { target := 581, numerator := 2069340992793478532641587200 }, some { target := 582, numerator := 50140132255385984845905657856 }, some { target := 583, numerator := 3207478538829891725594460160 }, some { target := 584, numerator := 1862406893514130679377428480 }, some { target := 585, numerator := 3269558768613696081573707776 }, some { target := 586, numerator := 124160459567608711958495232 }, some { target := 587, numerator := 3207478538829891725594460160 }, some { target := 588, numerator := 124160459567608711958495232 }, some { target := 589, numerator := 3269558768613696081573707776 }, some { target := 590, numerator := 3269558768613696081573707776 }, some { target := 591, numerator := 124160459567608711958495232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 126342192882694488047222784 }, some { target := 609, numerator := 1895132893240417320708341760 }, some { target := 610, numerator := 3327011079244288185243533312 }, some { target := 611, numerator := 126342192882694488047222784 }, some { target := 612, numerator := 2105703214711574800787046400 }, some { target := 613, numerator := 126342192882694488047222784 }, some { target := 614, numerator := 3327011079244288185243533312 }, some { target := 615, numerator := 3305954047097172437235662848 }, some { target := 616, numerator := 2105703214711574800787046400 }, some { target := 617, numerator := 51021188892461457423070134272 }, some { target := 618, numerator := 3263839982802940941219921920 }, some { target := 619, numerator := 1895132893240417320708341760 }, some { target := 620, numerator := 3327011079244288185243533312 }, some { target := 621, numerator := 126342192882694488047222784 }, some { target := 622, numerator := 3263839982802940941219921920 }, some { target := 623, numerator := 126342192882694488047222784 }, some { target := 624, numerator := 3327011079244288185243533312 }, some { target := 625, numerator := 3327011079244288185243533312 }, some { target := 626, numerator := 126342192882694488047222784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 6148521160696278068232192 }, some { target := 670, numerator := 92227817410444171023482880 }, some { target := 671, numerator := 161911057231668655796781056 }, some { target := 672, numerator := 6148521160696278068232192 }, some { target := 673, numerator := 102475352678271301137203200 }, some { target := 674, numerator := 6148521160696278068232192 }, some { target := 675, numerator := 161911057231668655796781056 }, some { target := 676, numerator := 160886303704885942785409024 }, some { target := 677, numerator := 102475352678271301137203200 }, some { target := 678, numerator := 2482977795394513626554433536 }, some { target := 679, numerator := 158836796651320516762664960 }, some { target := 680, numerator := 92227817410444171023482880 }, some { target := 681, numerator := 161911057231668655796781056 }, some { target := 682, numerator := 6148521160696278068232192 }, some { target := 683, numerator := 158836796651320516762664960 }, some { target := 684, numerator := 6148521160696278068232192 }, some { target := 685, numerator := 161911057231668655796781056 }, some { target := 686, numerator := 161911057231668655796781056 }, some { target := 687, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 150737938133199075221176320 }, some { target := 705, numerator := 2261069071997986128317644800 }, some { target := 706, numerator := 3969432370840908980824309760 }, some { target := 707, numerator := 150737938133199075221176320 }, some { target := 708, numerator := 2512298968886651253686272000 }, some { target := 709, numerator := 150737938133199075221176320 }, some { target := 710, numerator := 3969432370840908980824309760 }, some { target := 711, numerator := 3944309381152042468287447040 }, some { target := 712, numerator := 2512298968886651253686272000 }, some { target := 713, numerator := 60873004016123559876818370560 }, some { target := 714, numerator := 3894063401774309443213721600 }, some { target := 715, numerator := 2261069071997986128317644800 }, some { target := 716, numerator := 3969432370840908980824309760 }, some { target := 717, numerator := 150737938133199075221176320 }, some { target := 718, numerator := 3894063401774309443213721600 }, some { target := 719, numerator := 150737938133199075221176320 }, some { target := 720, numerator := 3969432370840908980824309760 }, some { target := 721, numerator := 3969432370840908980824309760 }, some { target := 722, numerator := 150737938133199075221176320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 6148521160696278068232192 }, some { target := 740, numerator := 92227817410444171023482880 }, some { target := 741, numerator := 161911057231668655796781056 }, some { target := 742, numerator := 6148521160696278068232192 }, some { target := 743, numerator := 102475352678271301137203200 }, some { target := 744, numerator := 6148521160696278068232192 }, some { target := 745, numerator := 161911057231668655796781056 }, some { target := 746, numerator := 160886303704885942785409024 }, some { target := 747, numerator := 102475352678271301137203200 }, some { target := 748, numerator := 2482977795394513626554433536 }, some { target := 749, numerator := 158836796651320516762664960 }, some { target := 750, numerator := 92227817410444171023482880 }, some { target := 751, numerator := 161911057231668655796781056 }, some { target := 752, numerator := 6148521160696278068232192 }, some { target := 753, numerator := 158836796651320516762664960 }, some { target := 754, numerator := 6148521160696278068232192 }, some { target := 755, numerator := 161911057231668655796781056 }, some { target := 756, numerator := 161911057231668655796781056 }, some { target := 757, numerator := 6148521160696278068232192 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 5, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 411, numerator := 1242608628897589038342471680 }, some { target := 413, numerator := 48468426999672496304768942080 }, some { target := 416, numerator := 48468409221622895267188572160 }, some { target := 423, numerator := 1242614554914122717535928320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 1238982339124541599514624000 }, some { target := 629, numerator := 48326982173797965673529344000 }, some { target := 632, numerator := 48326964447629832343257088000 }, some { target := 639, numerator := 1238988247847252709605376000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 1230520996320764242249646080 }, some { target := 725, numerator := 47996944246757394200636948480 }, some { target := 728, numerator := 47996926641646018854083624960 }, some { target := 735, numerator := 1230526864691222691100753920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1238982339124541599514624000 }, some { target := 760, numerator := 48326982173797965673529344000 }, some { target := 763, numerator := 48326964447629832343257088000 }, some { target := 770, numerator := 1238988247847252709605376000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 5, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

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
  [some { target := 774, numerator := 70777719089126768096250429440 }, some { target := 777, numerator := 254585350781235737426992824320 }, some { target := 779, numerator := 70777742700959182444476497920 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 50, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 116444149628087859098419200 }, some { target := 56, numerator := 87333112221065894323814400 }, some { target := 57, numerator := 92184951788902888452915200 }, some { target := 58, numerator := 118870069412006356162969600 }, some { target := 59, numerator := 1591403378250534074345062400 }, some { target := 60, numerator := 2782529992154516133039308800 }, some { target := 61, numerator := 84907192437147397259264000 }, some { target := 62, numerator := 1591403378250534074345062400 }, some { target := 63, numerator := 89759032004984391388364800 }, some { target := 64, numerator := 92184951788902888452915200 }, some { target := 65, numerator := 92184951788902888452915200 }, some { target := 66, numerator := 89759032004984391388364800 }, some { target := 67, numerator := 2782529992154516133039308800 }, some { target := 68, numerator := 89759032004984391388364800 }, some { target := 69, numerator := 116444149628087859098419200 }, some { target := 70, numerator := 118870069412006356162969600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 23094931586972792295260160000 }, some { target := 101, numerator := 17321198690229594221445120000 }, some { target := 102, numerator := 18283487506353460567080960000 }, some { target := 103, numerator := 23576075995034725468078080000 }, some { target := 104, numerator := 315630731688628161368555520000 }, some { target := 105, numerator := 551872636047037349222154240000 }, some { target := 106, numerator := 16840054282167661048627200000 }, some { target := 107, numerator := 315630731688628161368555520000 }, some { target := 108, numerator := 17802343098291527394263040000 }, some { target := 109, numerator := 18283487506353460567080960000 }, some { target := 110, numerator := 18283487506353460567080960000 }, some { target := 111, numerator := 17802343098291527394263040000 }, some { target := 112, numerator := 551872636047037349222154240000 }, some { target := 113, numerator := 17802343098291527394263040000 }, some { target := 114, numerator := 23094931586972792295260160000 }, some { target := 115, numerator := 23576075995034725468078080000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 23094931586972792295260160000 }, some { target := 316, numerator := 17321198690229594221445120000 }, some { target := 317, numerator := 18283487506353460567080960000 }, some { target := 318, numerator := 23576075995034725468078080000 }, some { target := 319, numerator := 315630731688628161368555520000 }, some { target := 320, numerator := 551872636047037349222154240000 }, some { target := 321, numerator := 16840054282167661048627200000 }, some { target := 322, numerator := 315630731688628161368555520000 }, some { target := 323, numerator := 17802343098291527394263040000 }, some { target := 324, numerator := 18283487506353460567080960000 }, some { target := 325, numerator := 18283487506353460567080960000 }, some { target := 326, numerator := 17802343098291527394263040000 }, some { target := 327, numerator := 551872636047037349222154240000 }, some { target := 328, numerator := 17802343098291527394263040000 }, some { target := 329, numerator := 23094931586972792295260160000 }, some { target := 330, numerator := 23576075995034725468078080000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 116444149628087859098419200 }, some { target := 654, numerator := 87333112221065894323814400 }, some { target := 655, numerator := 92184951788902888452915200 }, some { target := 656, numerator := 118870069412006356162969600 }, some { target := 657, numerator := 1591403378250534074345062400 }, some { target := 658, numerator := 2782529992154516133039308800 }, some { target := 659, numerator := 84907192437147397259264000 }, some { target := 660, numerator := 1591403378250534074345062400 }, some { target := 661, numerator := 89759032004984391388364800 }, some { target := 662, numerator := 92184951788902888452915200 }, some { target := 663, numerator := 92184951788902888452915200 }, some { target := 664, numerator := 89759032004984391388364800 }, some { target := 665, numerator := 2782529992154516133039308800 }, some { target := 666, numerator := 89759032004984391388364800 }, some { target := 667, numerator := 116444149628087859098419200 }, some { target := 668, numerator := 118870069412006356162969600 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 36, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 7]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 142, numerator := 44428554304801733867470848 }, some { target := 143, numerator := 5251169877136502986477928448 }, some { target := 145, numerator := 49832555383456092040124694528 }, some { target := 153, numerator := 5251173478673006294011478016 }, some { target := 160, numerator := 44428554304801733867470848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 2008089828341219403547803648 }, some { target := 358, numerator := 237343325304419436954541621248 }, some { target := 360, numerator := 2252340845917498409681135075328 }, some { target := 368, numerator := 237343488087317324537178095616 }, some { target := 375, numerator := 2008089828341219403547803648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 44665682930456823406264320 }, some { target := 670, numerator := 5279196958267797095653048320 }, some { target := 672, numerator := 50098526796567838344106475520 }, some { target := 680, numerator := 5279200579026789512710717440 }, some { target := 687, numerator := 44665682930456823406264320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left7.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left7.routed_eq]
  rfl

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent2
