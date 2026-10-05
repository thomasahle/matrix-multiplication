import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 1,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 75, #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 560260187551064226004992000 }, some { target := 11, numerator := 13735411049638993927864320000 }, some { target := 12, numerator := 10156975013022519194025984000 }, some { target := 13, numerator := 11331714115952169990488064000 }, some { target := 14, numerator := 560260187551064226004992000 }, some { target := 15, numerator := 11313641206676329209004032000 }, some { target := 16, numerator := 11512443208710577805328384000 }, some { target := 17, numerator := 560260187551064226004992000 }, some { target := 18, numerator := 13735411049638993927864320000 }, some { target := 19, numerator := 560260187551064226004992000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 21925760057281038423529881600 }, some { target := 56, numerator := 537534762694631909738151936000 }, some { target := 57, numerator := 397492811361030438516896563200 }, some { target := 58, numerator := 443466179223071325533975347200 }, some { target := 59, numerator := 21925760057281038423529881600 }, some { target := 60, numerator := 442758896640578388810635673600 }, some { target := 61, numerator := 450539005048000692767372083200 }, some { target := 62, numerator := 21925760057281038423529881600 }, some { target := 63, numerator := 537534762694631909738151936000 }, some { target := 64, numerator := 21925760057281038423529881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 21925760057281038423529881600 }, some { target := 145, numerator := 537534762694631909738151936000 }, some { target := 146, numerator := 397492811361030438516896563200 }, some { target := 147, numerator := 443466179223071325533975347200 }, some { target := 148, numerator := 21925760057281038423529881600 }, some { target := 149, numerator := 442758896640578388810635673600 }, some { target := 150, numerator := 450539005048000692767372083200 }, some { target := 151, numerator := 21925760057281038423529881600 }, some { target := 152, numerator := 537534762694631909738151936000 }, some { target := 153, numerator := 21925760057281038423529881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 560260187551064226004992000 }, some { target := 483, numerator := 13735411049638993927864320000 }, some { target := 484, numerator := 10156975013022519194025984000 }, some { target := 485, numerator := 11331714115952169990488064000 }, some { target := 486, numerator := 560260187551064226004992000 }, some { target := 487, numerator := 11313641206676329209004032000 }, some { target := 488, numerator := 11512443208710577805328384000 }, some { target := 489, numerator := 560260187551064226004992000 }, some { target := 490, numerator := 13735411049638993927864320000 }, some { target := 491, numerator := 560260187551064226004992000 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 262, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 175135122229741411740155904 }, some { target := 35, numerator := 130419771873211689593733120 }, some { target := 36, numerator := 137872330265966643284803584 }, some { target := 37, numerator := 178861401426118888585691136 }, some { target := 38, numerator := 2395997523270717611679154176 }, some { target := 39, numerator := 4333662705387005571357474816 }, some { target := 40, numerator := 130419771873211689593733120 }, some { target := 41, numerator := 2395997523270717611679154176 }, some { target := 42, numerator := 141598609462344120130338816 }, some { target := 43, numerator := 141598609462344120130338816 }, some { target := 44, numerator := 137872330265966643284803584 }, some { target := 45, numerator := 137872330265966643284803584 }, some { target := 46, numerator := 4333662705387005571357474816 }, some { target := 47, numerator := 137872330265966643284803584 }, some { target := 48, numerator := 175135122229741411740155904 }, some { target := 49, numerator := 178861401426118888585691136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 20699847039183142753564360704 }, some { target := 80, numerator := 15414779710029999922867077120 }, some { target := 81, numerator := 16295624264888857061316624384 }, some { target := 82, numerator := 21140269316612571322789134336 }, some { target := 83, numerator := 283191524387122570011529445376 }, some { target := 84, numerator := 512211108650425426008411734016 }, some { target := 85, numerator := 15414779710029999922867077120 }, some { target := 86, numerator := 283191524387122570011529445376 }, some { target := 87, numerator := 16736046542318285630541398016 }, some { target := 88, numerator := 16736046542318285630541398016 }, some { target := 89, numerator := 16295624264888857061316624384 }, some { target := 90, numerator := 16295624264888857061316624384 }, some { target := 91, numerator := 512211108650425426008411734016 }, some { target := 92, numerator := 16295624264888857061316624384 }, some { target := 93, numerator := 20699847039183142753564360704 }, some { target := 94, numerator := 21140269316612571322789134336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 196437422163851522457986924544 }, some { target := 155, numerator := 146283186717761772043181752320 }, some { target := 156, numerator := 154642225958776730445649281024 }, some { target := 157, numerator := 200616941784359001659220688896 }, some { target := 158, numerator := 2687431115986309126393310478336 }, some { target := 159, numerator := 4860781318650198311034867941376 }, some { target := 160, numerator := 146283186717761772043181752320 }, some { target := 161, numerator := 2687431115986309126393310478336 }, some { target := 162, numerator := 158821745579284209646883045376 }, some { target := 163, numerator := 158821745579284209646883045376 }, some { target := 164, numerator := 154642225958776730445649281024 }, some { target := 165, numerator := 154642225958776730445649281024 }, some { target := 166, numerator := 4860781318650198311034867941376 }, some { target := 167, numerator := 154642225958776730445649281024 }, some { target := 168, numerator := 196437422163851522457986924544 }, some { target := 169, numerator := 200616941784359001659220688896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 20699861236258550482278023168 }, some { target := 493, numerator := 15414790282320197167653847040 }, some { target := 494, numerator := 16295635441309922720091209728 }, some { target := 495, numerator := 21140283815753413258496704512 }, some { target := 496, numerator := 283191718615196765108612104192 }, some { target := 497, numerator := 512211459952525408742326403072 }, some { target := 498, numerator := 15414790282320197167653847040 }, some { target := 499, numerator := 283191718615196765108612104192 }, some { target := 500, numerator := 16736058020804785496309891072 }, some { target := 501, numerator := 16736058020804785496309891072 }, some { target := 502, numerator := 16295635441309922720091209728 }, some { target := 503, numerator := 16295635441309922720091209728 }, some { target := 504, numerator := 512211459952525408742326403072 }, some { target := 505, numerator := 16295635441309922720091209728 }, some { target := 506, numerator := 20699861236258550482278023168 }, some { target := 507, numerator := 21140283815753413258496704512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 175135122229741411740155904 }, some { target := 891, numerator := 130419771873211689593733120 }, some { target := 892, numerator := 137872330265966643284803584 }, some { target := 893, numerator := 178861401426118888585691136 }, some { target := 894, numerator := 2395997523270717611679154176 }, some { target := 895, numerator := 4333662705387005571357474816 }, some { target := 896, numerator := 130419771873211689593733120 }, some { target := 897, numerator := 2395997523270717611679154176 }, some { target := 898, numerator := 141598609462344120130338816 }, some { target := 899, numerator := 141598609462344120130338816 }, some { target := 900, numerator := 137872330265966643284803584 }, some { target := 901, numerator := 137872330265966643284803584 }, some { target := 902, numerator := 4333662705387005571357474816 }, some { target := 903, numerator := 137872330265966643284803584 }, some { target := 904, numerator := 175135122229741411740155904 }, some { target := 905, numerator := 178861401426118888585691136 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 55, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 121, numerator := 74802285088655180184944640 }, some { target := 122, numerator := 1084633133785500112681697280 }, some { target := 123, numerator := 1919925317275482958080245760 }, some { target := 124, numerator := 62335237573879316820787200 }, some { target := 125, numerator := 1196836561418482882959114240 }, some { target := 126, numerator := 62335237573879316820787200 }, some { target := 127, numerator := 1907458269760707094716088320 }, some { target := 128, numerator := 1994727602364138138265190400 }, some { target := 129, numerator := 1196836561418482882959114240 }, some { target := 130, numerator := 30556733458715641105549885440 }, some { target := 131, numerator := 1957326459819810548172718080 }, some { target := 132, numerator := 1084633133785500112681697280 }, some { target := 133, numerator := 1907458269760707094716088320 }, some { target := 134, numerator := 62335237573879316820787200 }, some { target := 135, numerator := 1957326459819810548172718080 }, some { target := 136, numerator := 62335237573879316820787200 }, some { target := 137, numerator := 1907458269760707094716088320 }, some { target := 138, numerator := 1994727602364138138265190400 }, some { target := 139, numerator := 74802285088655180184944640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 56101713816491385138708480 }, some { target := 197, numerator := 813474850339125084511272960 }, some { target := 198, numerator := 1439943987956612218560184320 }, some { target := 199, numerator := 46751428180409487615590400 }, some { target := 200, numerator := 897627421063862162219335680 }, some { target := 201, numerator := 46751428180409487615590400 }, some { target := 202, numerator := 1430593702320530321037066240 }, some { target := 203, numerator := 1496045701773103603698892800 }, some { target := 204, numerator := 897627421063862162219335680 }, some { target := 205, numerator := 22917550094036730829162414080 }, some { target := 206, numerator := 1467994844864857911129538560 }, some { target := 207, numerator := 813474850339125084511272960 }, some { target := 208, numerator := 1430593702320530321037066240 }, some { target := 209, numerator := 46751428180409487615590400 }, some { target := 210, numerator := 1467994844864857911129538560 }, some { target := 211, numerator := 46751428180409487615590400 }, some { target := 212, numerator := 1430593702320530321037066240 }, some { target := 213, numerator := 1496045701773103603698892800 }, some { target := 214, numerator := 56101713816491385138708480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 59218475695185350979747840 }, some { target := 232, numerator := 858667897580187589206343680 }, some { target := 233, numerator := 1519940876176424008480194560 }, some { target := 234, numerator := 49348729745987792483123200 }, some { target := 235, numerator := 947495611122965615675965440 }, some { target := 236, numerator := 49348729745987792483123200 }, some { target := 237, numerator := 1510071130227226449983569920 }, some { target := 238, numerator := 1579159351871609359459942400 }, some { target := 239, numerator := 947495611122965615675965440 }, some { target := 240, numerator := 24190747321483215875226992640 }, some { target := 241, numerator := 1549550114024016683970068480 }, some { target := 242, numerator := 858667897580187589206343680 }, some { target := 243, numerator := 1510071130227226449983569920 }, some { target := 244, numerator := 49348729745987792483123200 }, some { target := 245, numerator := 1549550114024016683970068480 }, some { target := 246, numerator := 49348729745987792483123200 }, some { target := 247, numerator := 1510071130227226449983569920 }, some { target := 248, numerator := 1579159351871609359459942400 }, some { target := 249, numerator := 59218475695185350979747840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 76360666028002163105464320 }, some { target := 338, numerator := 1107229657406031365029232640 }, some { target := 339, numerator := 1959923761385388853040250880 }, some { target := 340, numerator := 63633888356668469254553600 }, some { target := 341, numerator := 1221770656448034609687429120 }, some { target := 342, numerator := 63633888356668469254553600 }, some { target := 343, numerator := 1947196983714055159189340160 }, some { target := 344, numerator := 2036284427413391016145715200 }, some { target := 345, numerator := 1221770656448034609687429120 }, some { target := 346, numerator := 31193332072438883628582174720 }, some { target := 347, numerator := 1998104094399389934592983040 }, some { target := 348, numerator := 1107229657406031365029232640 }, some { target := 349, numerator := 1947196983714055159189340160 }, some { target := 350, numerator := 63633888356668469254553600 }, some { target := 351, numerator := 1998104094399389934592983040 }, some { target := 352, numerator := 63633888356668469254553600 }, some { target := 353, numerator := 1947196983714055159189340160 }, some { target := 354, numerator := 2036284427413391016145715200 }, some { target := 355, numerator := 76360666028002163105464320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 1022297896211620795860910080 }, some { target := 413, numerator := 14823319495068501539983196160 }, some { target := 414, numerator := 26238979336098267093763358720 }, some { target := 415, numerator := 851914913509683996550758400 }, some { target := 416, numerator := 16356766339385932733774561280 }, some { target := 417, numerator := 851914913509683996550758400 }, some { target := 418, numerator := 26068596353396330294453207040 }, some { target := 419, numerator := 27261277232309887889624268800 }, some { target := 420, numerator := 16356766339385932733774561280 }, some { target := 421, numerator := 417608690602447095109181767680 }, some { target := 422, numerator := 26750128284204077491693813760 }, some { target := 423, numerator := 14823319495068501539983196160 }, some { target := 424, numerator := 26068596353396330294453207040 }, some { target := 425, numerator := 851914913509683996550758400 }, some { target := 426, numerator := 26750128284204077491693813760 }, some { target := 427, numerator := 851914913509683996550758400 }, some { target := 428, numerator := 26068596353396330294453207040 }, some { target := 429, numerator := 27261277232309887889624268800 }, some { target := 430, numerator := 1022297896211620795860910080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 1787462937430989409836072960 }, some { target := 448, numerator := 25918212592749346442623057920 }, some { target := 449, numerator := 45878215394062061519125872640 }, some { target := 450, numerator := 1489552447859157841530060800 }, some { target := 451, numerator := 28599406998895830557377167360 }, some { target := 452, numerator := 1489552447859157841530060800 }, some { target := 453, numerator := 45580304904490229950819860480 }, some { target := 454, numerator := 47665678331493050928961945600 }, some { target := 455, numerator := 28599406998895830557377167360 }, some { target := 456, numerator := 730178609940559173918035804160 }, some { target := 457, numerator := 46771946862777556224043909120 }, some { target := 458, numerator := 25918212592749346442623057920 }, some { target := 459, numerator := 45580304904490229950819860480 }, some { target := 460, numerator := 1489552447859157841530060800 }, some { target := 461, numerator := 46771946862777556224043909120 }, some { target := 462, numerator := 1489552447859157841530060800 }, some { target := 463, numerator := 45580304904490229950819860480 }, some { target := 464, numerator := 47665678331493050928961945600 }, some { target := 465, numerator := 1787462937430989409836072960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 54543332877144402218188800 }, some { target := 509, numerator := 790878326718593832163737600 }, some { target := 510, numerator := 1399945543846706323600179200 }, some { target := 511, numerator := 45452777397620335181824000 }, some { target := 512, numerator := 872693326034310435491020800 }, some { target := 513, numerator := 45452777397620335181824000 }, some { target := 514, numerator := 1390854988367182256563814400 }, some { target := 515, numerator := 1454488876723850725818368000 }, some { target := 516, numerator := 872693326034310435491020800 }, some { target := 517, numerator := 22280951480313488306130124800 }, some { target := 518, numerator := 1427217210285278524709273600 }, some { target := 519, numerator := 790878326718593832163737600 }, some { target := 520, numerator := 1390854988367182256563814400 }, some { target := 521, numerator := 45452777397620335181824000 }, some { target := 522, numerator := 1427217210285278524709273600 }, some { target := 523, numerator := 45452777397620335181824000 }, some { target := 524, numerator := 1390854988367182256563814400 }, some { target := 525, numerator := 1454488876723850725818368000 }, some { target := 526, numerator := 54543332877144402218188800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 1022297896211620795860910080 }, some { target := 544, numerator := 14823319495068501539983196160 }, some { target := 545, numerator := 26238979336098267093763358720 }, some { target := 546, numerator := 851914913509683996550758400 }, some { target := 547, numerator := 16356766339385932733774561280 }, some { target := 548, numerator := 851914913509683996550758400 }, some { target := 549, numerator := 26068596353396330294453207040 }, some { target := 550, numerator := 27261277232309887889624268800 }, some { target := 551, numerator := 16356766339385932733774561280 }, some { target := 552, numerator := 417608690602447095109181767680 }, some { target := 553, numerator := 26750128284204077491693813760 }, some { target := 554, numerator := 14823319495068501539983196160 }, some { target := 555, numerator := 26068596353396330294453207040 }, some { target := 556, numerator := 851914913509683996550758400 }, some { target := 557, numerator := 26750128284204077491693813760 }, some { target := 558, numerator := 851914913509683996550758400 }, some { target := 559, numerator := 26068596353396330294453207040 }, some { target := 560, numerator := 27261277232309887889624268800 }, some { target := 561, numerator := 1022297896211620795860910080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 57660094755838368059228160 }, some { target := 579, numerator := 836071373959656336858808320 }, some { target := 580, numerator := 1479942432066518113520189440 }, some { target := 581, numerator := 48050078963198640049356800 }, some { target := 582, numerator := 922561516093413888947650560 }, some { target := 583, numerator := 48050078963198640049356800 }, some { target := 584, numerator := 1470332416273878385510318080 }, some { target := 585, numerator := 1537602526822356481579417600 }, some { target := 586, numerator := 922561516093413888947650560 }, some { target := 587, numerator := 23554148707759973352194703360 }, some { target := 588, numerator := 1508772479444437297549803520 }, some { target := 589, numerator := 836071373959656336858808320 }, some { target := 590, numerator := 1470332416273878385510318080 }, some { target := 591, numerator := 48050078963198640049356800 }, some { target := 592, numerator := 1508772479444437297549803520 }, some { target := 593, numerator := 48050078963198640049356800 }, some { target := 594, numerator := 1470332416273878385510318080 }, some { target := 595, numerator := 1537602526822356481579417600 }, some { target := 596, numerator := 57660094755838368059228160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 59218475695185350979747840 }, some { target := 680, numerator := 858667897580187589206343680 }, some { target := 681, numerator := 1519940876176424008480194560 }, some { target := 682, numerator := 49348729745987792483123200 }, some { target := 683, numerator := 947495611122965615675965440 }, some { target := 684, numerator := 49348729745987792483123200 }, some { target := 685, numerator := 1510071130227226449983569920 }, some { target := 686, numerator := 1579159351871609359459942400 }, some { target := 687, numerator := 947495611122965615675965440 }, some { target := 688, numerator := 24190747321483215875226992640 }, some { target := 689, numerator := 1549550114024016683970068480 }, some { target := 690, numerator := 858667897580187589206343680 }, some { target := 691, numerator := 1510071130227226449983569920 }, some { target := 692, numerator := 49348729745987792483123200 }, some { target := 693, numerator := 1549550114024016683970068480 }, some { target := 694, numerator := 49348729745987792483123200 }, some { target := 695, numerator := 1510071130227226449983569920 }, some { target := 696, numerator := 1579159351871609359459942400 }, some { target := 697, numerator := 59218475695185350979747840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 59218475695185350979747840 }, some { target := 715, numerator := 858667897580187589206343680 }, some { target := 716, numerator := 1519940876176424008480194560 }, some { target := 717, numerator := 49348729745987792483123200 }, some { target := 718, numerator := 947495611122965615675965440 }, some { target := 719, numerator := 49348729745987792483123200 }, some { target := 720, numerator := 1510071130227226449983569920 }, some { target := 721, numerator := 1579159351871609359459942400 }, some { target := 722, numerator := 947495611122965615675965440 }, some { target := 723, numerator := 24190747321483215875226992640 }, some { target := 724, numerator := 1549550114024016683970068480 }, some { target := 725, numerator := 858667897580187589206343680 }, some { target := 726, numerator := 1510071130227226449983569920 }, some { target := 727, numerator := 49348729745987792483123200 }, some { target := 728, numerator := 1549550114024016683970068480 }, some { target := 729, numerator := 49348729745987792483123200 }, some { target := 730, numerator := 1510071130227226449983569920 }, some { target := 731, numerator := 1579159351871609359459942400 }, some { target := 732, numerator := 59218475695185350979747840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 57660094755838368059228160 }, some { target := 776, numerator := 836071373959656336858808320 }, some { target := 777, numerator := 1479942432066518113520189440 }, some { target := 778, numerator := 48050078963198640049356800 }, some { target := 779, numerator := 922561516093413888947650560 }, some { target := 780, numerator := 48050078963198640049356800 }, some { target := 781, numerator := 1470332416273878385510318080 }, some { target := 782, numerator := 1537602526822356481579417600 }, some { target := 783, numerator := 922561516093413888947650560 }, some { target := 784, numerator := 23554148707759973352194703360 }, some { target := 785, numerator := 1508772479444437297549803520 }, some { target := 786, numerator := 836071373959656336858808320 }, some { target := 787, numerator := 1470332416273878385510318080 }, some { target := 788, numerator := 48050078963198640049356800 }, some { target := 789, numerator := 1508772479444437297549803520 }, some { target := 790, numerator := 48050078963198640049356800 }, some { target := 791, numerator := 1470332416273878385510318080 }, some { target := 792, numerator := 1537602526822356481579417600 }, some { target := 793, numerator := 57660094755838368059228160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 1787462937430989409836072960 }, some { target := 811, numerator := 25918212592749346442623057920 }, some { target := 812, numerator := 45878215394062061519125872640 }, some { target := 813, numerator := 1489552447859157841530060800 }, some { target := 814, numerator := 28599406998895830557377167360 }, some { target := 815, numerator := 1489552447859157841530060800 }, some { target := 816, numerator := 45580304904490229950819860480 }, some { target := 817, numerator := 47665678331493050928961945600 }, some { target := 818, numerator := 28599406998895830557377167360 }, some { target := 819, numerator := 730178609940559173918035804160 }, some { target := 820, numerator := 46771946862777556224043909120 }, some { target := 821, numerator := 25918212592749346442623057920 }, some { target := 822, numerator := 45580304904490229950819860480 }, some { target := 823, numerator := 1489552447859157841530060800 }, some { target := 824, numerator := 46771946862777556224043909120 }, some { target := 825, numerator := 1489552447859157841530060800 }, some { target := 826, numerator := 45580304904490229950819860480 }, some { target := 827, numerator := 47665678331493050928961945600 }, some { target := 828, numerator := 1787462937430989409836072960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 57660094755838368059228160 }, some { target := 846, numerator := 836071373959656336858808320 }, some { target := 847, numerator := 1479942432066518113520189440 }, some { target := 848, numerator := 48050078963198640049356800 }, some { target := 849, numerator := 922561516093413888947650560 }, some { target := 850, numerator := 48050078963198640049356800 }, some { target := 851, numerator := 1470332416273878385510318080 }, some { target := 852, numerator := 1537602526822356481579417600 }, some { target := 853, numerator := 922561516093413888947650560 }, some { target := 854, numerator := 23554148707759973352194703360 }, some { target := 855, numerator := 1508772479444437297549803520 }, some { target := 856, numerator := 836071373959656336858808320 }, some { target := 857, numerator := 1470332416273878385510318080 }, some { target := 858, numerator := 48050078963198640049356800 }, some { target := 859, numerator := 1508772479444437297549803520 }, some { target := 860, numerator := 48050078963198640049356800 }, some { target := 861, numerator := 1470332416273878385510318080 }, some { target := 862, numerator := 1537602526822356481579417600 }, some { target := 863, numerator := 57660094755838368059228160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 74802285088655180184944640 }, some { target := 907, numerator := 1084633133785500112681697280 }, some { target := 908, numerator := 1919925317275482958080245760 }, some { target := 909, numerator := 62335237573879316820787200 }, some { target := 910, numerator := 1196836561418482882959114240 }, some { target := 911, numerator := 62335237573879316820787200 }, some { target := 912, numerator := 1907458269760707094716088320 }, some { target := 913, numerator := 1994727602364138138265190400 }, some { target := 914, numerator := 1196836561418482882959114240 }, some { target := 915, numerator := 30556733458715641105549885440 }, some { target := 916, numerator := 1957326459819810548172718080 }, some { target := 917, numerator := 1084633133785500112681697280 }, some { target := 918, numerator := 1907458269760707094716088320 }, some { target := 919, numerator := 62335237573879316820787200 }, some { target := 920, numerator := 1957326459819810548172718080 }, some { target := 921, numerator := 62335237573879316820787200 }, some { target := 922, numerator := 1907458269760707094716088320 }, some { target := 923, numerator := 1994727602364138138265190400 }, some { target := 924, numerator := 74802285088655180184944640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 76360666028002163105464320 }, some { target := 942, numerator := 1107229657406031365029232640 }, some { target := 943, numerator := 1959923761385388853040250880 }, some { target := 944, numerator := 63633888356668469254553600 }, some { target := 945, numerator := 1221770656448034609687429120 }, some { target := 946, numerator := 63633888356668469254553600 }, some { target := 947, numerator := 1947196983714055159189340160 }, some { target := 948, numerator := 2036284427413391016145715200 }, some { target := 949, numerator := 1221770656448034609687429120 }, some { target := 950, numerator := 31193332072438883628582174720 }, some { target := 951, numerator := 1998104094399389934592983040 }, some { target := 952, numerator := 1107229657406031365029232640 }, some { target := 953, numerator := 1947196983714055159189340160 }, some { target := 954, numerator := 63633888356668469254553600 }, some { target := 955, numerator := 1998104094399389934592983040 }, some { target := 956, numerator := 63633888356668469254553600 }, some { target := 957, numerator := 1947196983714055159189340160 }, some { target := 958, numerator := 2036284427413391016145715200 }, some { target := 959, numerator := 76360666028002163105464320 }]

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

end Slot19

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1
