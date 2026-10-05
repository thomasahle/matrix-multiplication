import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 13614582570113187151085568 }, some { target := 11, numerator := 329824242263064630660169728 }, some { target := 12, numerator := 249893467174013015773151232 }, some { target := 13, numerator := 278440172562960021089943552 }, some { target := 14, numerator := 13614582570113187151085568 }, some { target := 15, numerator := 278440172562960021089943552 }, some { target := 16, numerator := 278000992480053144085069824 }, some { target := 17, numerator := 13614582570113187151085568 }, some { target := 18, numerator := 329824242263064630660169728 }, some { target := 19, numerator := 13614582570113187151085568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 24, numerator := 15371302901740695170580480 }, some { target := 25, numerator := 372382209006685873325998080 }, some { target := 26, numerator := 282137785519046953292267520 }, some { target := 27, numerator := 314367936764632281875742720 }, some { target := 28, numerator := 15371302901740695170580480 }, some { target := 29, numerator := 314367936764632281875742720 }, some { target := 30, numerator := 313872088283930969128304640 }, some { target := 31, numerator := 15371302901740695170580480 }, some { target := 32, numerator := 372382209006685873325998080 }, some { target := 33, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 13175402487206310146211840 }, some { target := 56, numerator := 319184750577159319993712640 }, some { target := 57, numerator := 241832387587754531393372160 }, some { target := 58, numerator := 269458231512541955893493760 }, some { target := 59, numerator := 13175402487206310146211840 }, some { target := 60, numerator := 269458231512541955893493760 }, some { target := 61, numerator := 269033218529083687824261120 }, some { target := 62, numerator := 13175402487206310146211840 }, some { target := 63, numerator := 319184750577159319993712640 }, some { target := 64, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 69, numerator := 173476132748216416925122560 }, some { target := 70, numerator := 4202599215932597713250549760 }, some { target := 71, numerator := 3184126436572101330012733440 }, some { target := 72, numerator := 3547866714915135752597667840 }, some { target := 73, numerator := 173476132748216416925122560 }, some { target := 74, numerator := 3547866714915135752597667840 }, some { target := 75, numerator := 3542270710632935223019438080 }, some { target := 76, numerator := 173476132748216416925122560 }, some { target := 77, numerator := 4202599215932597713250549760 }, some { target := 78, numerator := 173476132748216416925122560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 95, numerator := 15371302901740695170580480 }, some { target := 96, numerator := 372382209006685873325998080 }, some { target := 97, numerator := 282137785519046953292267520 }, some { target := 98, numerator := 314367936764632281875742720 }, some { target := 99, numerator := 15371302901740695170580480 }, some { target := 100, numerator := 314367936764632281875742720 }, some { target := 101, numerator := 313872088283930969128304640 }, some { target := 102, numerator := 15371302901740695170580480 }, some { target := 103, numerator := 372382209006685873325998080 }, some { target := 104, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 13175402487206310146211840 }, some { target := 145, numerator := 319184750577159319993712640 }, some { target := 146, numerator := 241832387587754531393372160 }, some { target := 147, numerator := 269458231512541955893493760 }, some { target := 148, numerator := 13175402487206310146211840 }, some { target := 149, numerator := 269458231512541955893493760 }, some { target := 150, numerator := 269033218529083687824261120 }, some { target := 151, numerator := 13175402487206310146211840 }, some { target := 152, numerator := 319184750577159319993712640 }, some { target := 153, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 170, numerator := 15371302901740695170580480 }, some { target := 171, numerator := 372382209006685873325998080 }, some { target := 172, numerator := 282137785519046953292267520 }, some { target := 173, numerator := 314367936764632281875742720 }, some { target := 174, numerator := 15371302901740695170580480 }, some { target := 175, numerator := 314367936764632281875742720 }, some { target := 176, numerator := 313872088283930969128304640 }, some { target := 177, numerator := 15371302901740695170580480 }, some { target := 178, numerator := 372382209006685873325998080 }, some { target := 179, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 271, numerator := 15371302901740695170580480 }, some { target := 272, numerator := 372382209006685873325998080 }, some { target := 273, numerator := 282137785519046953292267520 }, some { target := 274, numerator := 314367936764632281875742720 }, some { target := 275, numerator := 15371302901740695170580480 }, some { target := 276, numerator := 314367936764632281875742720 }, some { target := 277, numerator := 313872088283930969128304640 }, some { target := 278, numerator := 15371302901740695170580480 }, some { target := 279, numerator := 372382209006685873325998080 }, some { target := 280, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 637250300297878534071779328 }, some { target := 286, numerator := 15437902436248605777029234688 }, some { target := 287, numerator := 11696626479661060835059433472 }, some { target := 288, numerator := 13032796464156612600048648192 }, some { target := 289, numerator := 637250300297878534071779328 }, some { target := 290, numerator := 13032796464156612600048648192 }, some { target := 291, numerator := 13012240002856681034433429504 }, some { target := 292, numerator := 637250300297878534071779328 }, some { target := 293, numerator := 15437902436248605777029234688 }, some { target := 294, numerator := 637250300297878534071779328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 15810482984647572175454208 }, some { target := 312, numerator := 383021700692591183992455168 }, some { target := 313, numerator := 290198865105305437672046592 }, some { target := 314, numerator := 323349877815050347072192512 }, some { target := 315, numerator := 15810482984647572175454208 }, some { target := 316, numerator := 323349877815050347072192512 }, some { target := 317, numerator := 322839862234900425389113344 }, some { target := 318, numerator := 15810482984647572175454208 }, some { target := 319, numerator := 383021700692591183992455168 }, some { target := 320, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 360, numerator := 173476132748216416925122560 }, some { target := 361, numerator := 4202599215932597713250549760 }, some { target := 362, numerator := 3184126436572101330012733440 }, some { target := 363, numerator := 3547866714915135752597667840 }, some { target := 364, numerator := 173476132748216416925122560 }, some { target := 365, numerator := 3547866714915135752597667840 }, some { target := 366, numerator := 3542270710632935223019438080 }, some { target := 367, numerator := 173476132748216416925122560 }, some { target := 368, numerator := 4202599215932597713250549760 }, some { target := 369, numerator := 173476132748216416925122560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 637250300297878534071779328 }, some { target := 387, numerator := 15437902436248605777029234688 }, some { target := 388, numerator := 11696626479661060835059433472 }, some { target := 389, numerator := 13032796464156612600048648192 }, some { target := 390, numerator := 637250300297878534071779328 }, some { target := 391, numerator := 13032796464156612600048648192 }, some { target := 392, numerator := 13012240002856681034433429504 }, some { target := 393, numerator := 637250300297878534071779328 }, some { target := 394, numerator := 15437902436248605777029234688 }, some { target := 395, numerator := 637250300297878534071779328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 13614582570113187151085568 }, some { target := 483, numerator := 329824242263064630660169728 }, some { target := 484, numerator := 249893467174013015773151232 }, some { target := 485, numerator := 278440172562960021089943552 }, some { target := 486, numerator := 13614582570113187151085568 }, some { target := 487, numerator := 278440172562960021089943552 }, some { target := 488, numerator := 278000992480053144085069824 }, some { target := 489, numerator := 13614582570113187151085568 }, some { target := 490, numerator := 329824242263064630660169728 }, some { target := 491, numerator := 13614582570113187151085568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 15371302901740695170580480 }, some { target := 628, numerator := 372382209006685873325998080 }, some { target := 629, numerator := 282137785519046953292267520 }, some { target := 630, numerator := 314367936764632281875742720 }, some { target := 631, numerator := 15371302901740695170580480 }, some { target := 632, numerator := 314367936764632281875742720 }, some { target := 633, numerator := 313872088283930969128304640 }, some { target := 634, numerator := 15371302901740695170580480 }, some { target := 635, numerator := 372382209006685873325998080 }, some { target := 636, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 15810482984647572175454208 }, some { target := 654, numerator := 383021700692591183992455168 }, some { target := 655, numerator := 290198865105305437672046592 }, some { target := 656, numerator := 323349877815050347072192512 }, some { target := 657, numerator := 15810482984647572175454208 }, some { target := 658, numerator := 323349877815050347072192512 }, some { target := 659, numerator := 322839862234900425389113344 }, some { target := 660, numerator := 15810482984647572175454208 }, some { target := 661, numerator := 383021700692591183992455168 }, some { target := 662, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 749, numerator := 15371302901740695170580480 }, some { target := 750, numerator := 372382209006685873325998080 }, some { target := 751, numerator := 282137785519046953292267520 }, some { target := 752, numerator := 314367936764632281875742720 }, some { target := 753, numerator := 15371302901740695170580480 }, some { target := 754, numerator := 314367936764632281875742720 }, some { target := 755, numerator := 313872088283930969128304640 }, some { target := 756, numerator := 15371302901740695170580480 }, some { target := 757, numerator := 372382209006685873325998080 }, some { target := 758, numerator := 15371302901740695170580480 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 125, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 41122115995940866228224000 }, some { target := 35, numerator := 7212432801691834182008832000 }, some { target := 40, numerator := 7212433666382962637144064000 }, some { target := 48, numerator := 41121251304812411092992000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 596270681941142560309248000 }, some { target := 80, numerator := 104580275624531595639128064000 }, some { target := 85, numerator := 104580288162552958238588928000 }, some { target := 93, numerator := 596258143919779960848384000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 105, numerator := 1055467643895815566524416000 }, some { target := 106, numerator := 185119108576757077338226688000 }, some { target := 111, numerator := 185119130770496041020030976000 }, some { target := 119, numerator := 1055445450156851884720128000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 34268429996617388523520000 }, some { target := 155, numerator := 6010360668076528485007360000 }, some { target := 160, numerator := 6010361388652468864286720000 }, some { target := 168, numerator := 34267709420677009244160000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 180, numerator := 657953855935053859651584000 }, some { target := 181, numerator := 115398924827069346912141312000 }, some { target := 186, numerator := 115398938662127402194305024000 }, some { target := 194, numerator := 657940020876998577487872000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 34268429996617388523520000 }, some { target := 216, numerator := 6010360668076528485007360000 }, some { target := 221, numerator := 6010361388652468864286720000 }, some { target := 229, numerator := 34267709420677009244160000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 295, numerator := 1048613957896492088819712000 }, some { target := 296, numerator := 183917036443141771641225216000 }, some { target := 301, numerator := 183917058492765547247173632000 }, some { target := 309, numerator := 1048591908272716482871296000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 321, numerator := 1096589759891756432752640000 }, some { target := 322, numerator := 192331541378448911520235520000 }, some { target := 327, numerator := 192331564436879003657175040000 }, some { target := 335, numerator := 1096566701461664295813120000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 370, numerator := 657953855935053859651584000 }, some { target := 371, numerator := 115398924827069346912141312000 }, some { target := 376, numerator := 115398938662127402194305024000 }, some { target := 384, numerator := 657940020876998577487872000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 396, numerator := 16798384384341843854229504000 }, some { target := 397, numerator := 2946278799491114263350607872000 }, some { target := 402, numerator := 2946279152717440237273350144000 }, some { target := 410, numerator := 16798031158015869931487232000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 431, numerator := 1076028701893785999638528000 }, some { target := 432, numerator := 188725324977602994429231104000 }, some { target := 437, numerator := 188725347603687522338603008000 }, some { target := 445, numerator := 1076006075809258090266624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 596270681941142560309248000 }, some { target := 493, numerator := 104580275624531595639128064000 }, some { target := 498, numerator := 104580288162552958238588928000 }, some { target := 506, numerator := 596258143919779960848384000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 527, numerator := 1048613957896492088819712000 }, some { target := 528, numerator := 183917036443141771641225216000 }, some { target := 533, numerator := 183917058492765547247173632000 }, some { target := 541, numerator := 1048591908272716482871296000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 637, numerator := 34268429996617388523520000 }, some { target := 638, numerator := 6010360668076528485007360000 }, some { target := 643, numerator := 6010361388652468864286720000 }, some { target := 651, numerator := 34267709420677009244160000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 663, numerator := 1076028701893785999638528000 }, some { target := 664, numerator := 188725324977602994429231104000 }, some { target := 669, numerator := 188725347603687522338603008000 }, some { target := 677, numerator := 1076006075809258090266624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 34268429996617388523520000 }, some { target := 699, numerator := 6010360668076528485007360000 }, some { target := 704, numerator := 6010361388652468864286720000 }, some { target := 712, numerator := 34267709420677009244160000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 759, numerator := 1048613957896492088819712000 }, some { target := 760, numerator := 183917036443141771641225216000 }, some { target := 765, numerator := 183917058492765547247173632000 }, some { target := 773, numerator := 1048591908272716482871296000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 794, numerator := 1096589759891756432752640000 }, some { target := 795, numerator := 192331541378448911520235520000 }, some { target := 800, numerator := 192331564436879003657175040000 }, some { target := 808, numerator := 1096566701461664295813120000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 41122115995940866228224000 }, some { target := 891, numerator := 7212432801691834182008832000 }, some { target := 896, numerator := 7212433666382962637144064000 }, some { target := 904, numerator := 41121251304812411092992000 }]

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

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0
