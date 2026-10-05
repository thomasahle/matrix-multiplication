import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 1,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 127, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 121, numerator := 41780069851875920087875584 }, some { target := 122, numerator := 605811012852200841274195968 }, some { target := 123, numerator := 1072355126198148615588806656 }, some { target := 124, numerator := 34816724876563266739896320 }, some { target := 125, numerator := 668481117630014721406009344 }, some { target := 126, numerator := 34816724876563266739896320 }, some { target := 127, numerator := 1065391781222835962240827392 }, some { target := 128, numerator := 1114135196050024535676682240 }, some { target := 129, numerator := 668481117630014721406009344 }, some { target := 130, numerator := 17067158534491313355897176064 }, some { target := 131, numerator := 1093245161124086575632744448 }, some { target := 132, numerator := 605811012852200841274195968 }, some { target := 133, numerator := 1065391781222835962240827392 }, some { target := 134, numerator := 34816724876563266739896320 }, some { target := 135, numerator := 1093245161124086575632744448 }, some { target := 136, numerator := 34816724876563266739896320 }, some { target := 137, numerator := 1065391781222835962240827392 }, some { target := 138, numerator := 1114135196050024535676682240 }, some { target := 139, numerator := 41780069851875920087875584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 7327831726518903528920973312 }, some { target := 197, numerator := 106253560034524101169354113024 }, some { target := 198, numerator := 188081014313985190575638315008 }, some { target := 199, numerator := 6106526438765752940767477760 }, some { target := 200, numerator := 117245307624302456462735572992 }, some { target := 201, numerator := 6106526438765752940767477760 }, some { target := 202, numerator := 186859709026232039987484819456 }, some { target := 203, numerator := 195408846040504094104559288320 }, some { target := 204, numerator := 117245307624302456462735572992 }, some { target := 205, numerator := 2993419260282972091564217597952 }, some { target := 206, numerator := 191744930177244642340098801664 }, some { target := 207, numerator := 106253560034524101169354113024 }, some { target := 208, numerator := 186859709026232039987484819456 }, some { target := 209, numerator := 6106526438765752940767477760 }, some { target := 210, numerator := 191744930177244642340098801664 }, some { target := 211, numerator := 6106526438765752940767477760 }, some { target := 212, numerator := 186859709026232039987484819456 }, some { target := 213, numerator := 195408846040504094104559288320 }, some { target := 214, numerator := 7327831726518903528920973312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 7327832605045090039338369024 }, some { target := 509, numerator := 106253572773153805570406350848 }, some { target := 510, numerator := 188081036862823977676351471616 }, some { target := 511, numerator := 6106527170870908366115307520 }, some { target := 512, numerator := 117245321680721440629413904384 }, some { target := 513, numerator := 6106527170870908366115307520 }, some { target := 514, numerator := 186859731428649796003128410112 }, some { target := 515, numerator := 195408869467869067715689840640 }, some { target := 516, numerator := 117245321680721440629413904384 }, some { target := 517, numerator := 2993419619160919281069723746304 }, some { target := 518, numerator := 191744953165346522696020656128 }, some { target := 519, numerator := 106253572773153805570406350848 }, some { target := 520, numerator := 186859731428649796003128410112 }, some { target := 521, numerator := 6106527170870908366115307520 }, some { target := 522, numerator := 191744953165346522696020656128 }, some { target := 523, numerator := 6106527170870908366115307520 }, some { target := 524, numerator := 186859731428649796003128410112 }, some { target := 525, numerator := 195408869467869067715689840640 }, some { target := 526, numerator := 7327832605045090039338369024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 41779191325689409670479872 }, some { target := 907, numerator := 605798274222496440221958144 }, some { target := 908, numerator := 1072332577359361514875650048 }, some { target := 909, numerator := 34815992771407841392066560 }, some { target := 910, numerator := 668467061211030554727677952 }, some { target := 911, numerator := 34815992771407841392066560 }, some { target := 912, numerator := 1065369378805079946597236736 }, some { target := 913, numerator := 1114111768685050924546129920 }, some { target := 914, numerator := 668467061211030554727677952 }, some { target := 915, numerator := 17066799656544123850391027712 }, some { target := 916, numerator := 1093222173022206219710889984 }, some { target := 917, numerator := 605798274222496440221958144 }, some { target := 918, numerator := 1065369378805079946597236736 }, some { target := 919, numerator := 34815992771407841392066560 }, some { target := 920, numerator := 1093222173022206219710889984 }, some { target := 921, numerator := 34815992771407841392066560 }, some { target := 922, numerator := 1065369378805079946597236736 }, some { target := 923, numerator := 1114111768685050924546129920 }, some { target := 924, numerator := 41779191325689409670479872 }]

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

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 3, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 250, numerator := 13614582570113187151085568 }, some { target := 251, numerator := 15371302901740695170580480 }, some { target := 252, numerator := 13175402487206310146211840 }, some { target := 253, numerator := 173476132748216416925122560 }, some { target := 254, numerator := 15371302901740695170580480 }, some { target := 255, numerator := 13175402487206310146211840 }, some { target := 256, numerator := 15371302901740695170580480 }, some { target := 257, numerator := 15371302901740695170580480 }, some { target := 258, numerator := 637250300297878534071779328 }, some { target := 259, numerator := 15810482984647572175454208 }, some { target := 260, numerator := 173476132748216416925122560 }, some { target := 261, numerator := 637250300297878534071779328 }, some { target := 262, numerator := 13614582570113187151085568 }, some { target := 263, numerator := 15371302901740695170580480 }, some { target := 264, numerator := 15810482984647572175454208 }, some { target := 265, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 329824242263064630660169728 }, some { target := 467, numerator := 372382209006685873325998080 }, some { target := 468, numerator := 319184750577159319993712640 }, some { target := 469, numerator := 4202599215932597713250549760 }, some { target := 470, numerator := 372382209006685873325998080 }, some { target := 471, numerator := 319184750577159319993712640 }, some { target := 472, numerator := 372382209006685873325998080 }, some { target := 473, numerator := 372382209006685873325998080 }, some { target := 474, numerator := 15437902436248605777029234688 }, some { target := 475, numerator := 383021700692591183992455168 }, some { target := 476, numerator := 4202599215932597713250549760 }, some { target := 477, numerator := 15437902436248605777029234688 }, some { target := 478, numerator := 329824242263064630660169728 }, some { target := 479, numerator := 372382209006685873325998080 }, some { target := 480, numerator := 383021700692591183992455168 }, some { target := 481, numerator := 372382209006685873325998080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 249893467174013015773151232 }, some { target := 563, numerator := 282137785519046953292267520 }, some { target := 564, numerator := 241832387587754531393372160 }, some { target := 565, numerator := 3184126436572101330012733440 }, some { target := 566, numerator := 282137785519046953292267520 }, some { target := 567, numerator := 241832387587754531393372160 }, some { target := 568, numerator := 282137785519046953292267520 }, some { target := 569, numerator := 282137785519046953292267520 }, some { target := 570, numerator := 11696626479661060835059433472 }, some { target := 571, numerator := 290198865105305437672046592 }, some { target := 572, numerator := 3184126436572101330012733440 }, some { target := 573, numerator := 11696626479661060835059433472 }, some { target := 574, numerator := 249893467174013015773151232 }, some { target := 575, numerator := 282137785519046953292267520 }, some { target := 576, numerator := 290198865105305437672046592 }, some { target := 577, numerator := 282137785519046953292267520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 278440172562960021089943552 }, some { target := 598, numerator := 314367936764632281875742720 }, some { target := 599, numerator := 269458231512541955893493760 }, some { target := 600, numerator := 3547866714915135752597667840 }, some { target := 601, numerator := 314367936764632281875742720 }, some { target := 602, numerator := 269458231512541955893493760 }, some { target := 603, numerator := 314367936764632281875742720 }, some { target := 604, numerator := 314367936764632281875742720 }, some { target := 605, numerator := 13032796464156612600048648192 }, some { target := 606, numerator := 323349877815050347072192512 }, some { target := 607, numerator := 3547866714915135752597667840 }, some { target := 608, numerator := 13032796464156612600048648192 }, some { target := 609, numerator := 278440172562960021089943552 }, some { target := 610, numerator := 314367936764632281875742720 }, some { target := 611, numerator := 323349877815050347072192512 }, some { target := 612, numerator := 314367936764632281875742720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 13614582570113187151085568 }, some { target := 734, numerator := 15371302901740695170580480 }, some { target := 735, numerator := 13175402487206310146211840 }, some { target := 736, numerator := 173476132748216416925122560 }, some { target := 737, numerator := 15371302901740695170580480 }, some { target := 738, numerator := 13175402487206310146211840 }, some { target := 739, numerator := 15371302901740695170580480 }, some { target := 740, numerator := 15371302901740695170580480 }, some { target := 741, numerator := 637250300297878534071779328 }, some { target := 742, numerator := 15810482984647572175454208 }, some { target := 743, numerator := 173476132748216416925122560 }, some { target := 744, numerator := 637250300297878534071779328 }, some { target := 745, numerator := 13614582570113187151085568 }, some { target := 746, numerator := 15371302901740695170580480 }, some { target := 747, numerator := 15810482984647572175454208 }, some { target := 748, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 278440172562960021089943552 }, some { target := 830, numerator := 314367936764632281875742720 }, some { target := 831, numerator := 269458231512541955893493760 }, some { target := 832, numerator := 3547866714915135752597667840 }, some { target := 833, numerator := 314367936764632281875742720 }, some { target := 834, numerator := 269458231512541955893493760 }, some { target := 835, numerator := 314367936764632281875742720 }, some { target := 836, numerator := 314367936764632281875742720 }, some { target := 837, numerator := 13032796464156612600048648192 }, some { target := 838, numerator := 323349877815050347072192512 }, some { target := 839, numerator := 3547866714915135752597667840 }, some { target := 840, numerator := 13032796464156612600048648192 }, some { target := 841, numerator := 278440172562960021089943552 }, some { target := 842, numerator := 314367936764632281875742720 }, some { target := 843, numerator := 323349877815050347072192512 }, some { target := 844, numerator := 314367936764632281875742720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 278000992480053144085069824 }, some { target := 865, numerator := 313872088283930969128304640 }, some { target := 866, numerator := 269033218529083687824261120 }, some { target := 867, numerator := 3542270710632935223019438080 }, some { target := 868, numerator := 313872088283930969128304640 }, some { target := 869, numerator := 269033218529083687824261120 }, some { target := 870, numerator := 313872088283930969128304640 }, some { target := 871, numerator := 313872088283930969128304640 }, some { target := 872, numerator := 13012240002856681034433429504 }, some { target := 873, numerator := 322839862234900425389113344 }, some { target := 874, numerator := 3542270710632935223019438080 }, some { target := 875, numerator := 13012240002856681034433429504 }, some { target := 876, numerator := 278000992480053144085069824 }, some { target := 877, numerator := 313872088283930969128304640 }, some { target := 878, numerator := 322839862234900425389113344 }, some { target := 879, numerator := 313872088283930969128304640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 13614582570113187151085568 }, some { target := 926, numerator := 15371302901740695170580480 }, some { target := 927, numerator := 13175402487206310146211840 }, some { target := 928, numerator := 173476132748216416925122560 }, some { target := 929, numerator := 15371302901740695170580480 }, some { target := 930, numerator := 13175402487206310146211840 }, some { target := 931, numerator := 15371302901740695170580480 }, some { target := 932, numerator := 15371302901740695170580480 }, some { target := 933, numerator := 637250300297878534071779328 }, some { target := 934, numerator := 15810482984647572175454208 }, some { target := 935, numerator := 173476132748216416925122560 }, some { target := 936, numerator := 637250300297878534071779328 }, some { target := 937, numerator := 13614582570113187151085568 }, some { target := 938, numerator := 15371302901740695170580480 }, some { target := 939, numerator := 15810482984647572175454208 }, some { target := 940, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 329824242263064630660169728 }, some { target := 961, numerator := 372382209006685873325998080 }, some { target := 962, numerator := 319184750577159319993712640 }, some { target := 963, numerator := 4202599215932597713250549760 }, some { target := 964, numerator := 372382209006685873325998080 }, some { target := 965, numerator := 319184750577159319993712640 }, some { target := 966, numerator := 372382209006685873325998080 }, some { target := 967, numerator := 372382209006685873325998080 }, some { target := 968, numerator := 15437902436248605777029234688 }, some { target := 969, numerator := 383021700692591183992455168 }, some { target := 970, numerator := 4202599215932597713250549760 }, some { target := 971, numerator := 15437902436248605777029234688 }, some { target := 972, numerator := 329824242263064630660169728 }, some { target := 973, numerator := 372382209006685873325998080 }, some { target := 974, numerator := 383021700692591183992455168 }, some { target := 975, numerator := 372382209006685873325998080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 13614582570113187151085568 }, some { target := 987, numerator := 15371302901740695170580480 }, some { target := 988, numerator := 13175402487206310146211840 }, some { target := 989, numerator := 173476132748216416925122560 }, some { target := 990, numerator := 15371302901740695170580480 }, some { target := 991, numerator := 13175402487206310146211840 }, some { target := 992, numerator := 15371302901740695170580480 }, some { target := 993, numerator := 15371302901740695170580480 }, some { target := 994, numerator := 637250300297878534071779328 }, some { target := 995, numerator := 15810482984647572175454208 }, some { target := 996, numerator := 173476132748216416925122560 }, some { target := 997, numerator := 637250300297878534071779328 }, some { target := 998, numerator := 13614582570113187151085568 }, some { target := 999, numerator := 15371302901740695170580480 }, some { target := 1000, numerator := 15810482984647572175454208 }, some { target := 1001, numerator := 15371302901740695170580480 }]

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

end Slot17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent0
