import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 58; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 15810482984647572175454208 }, some { target := 251, numerator := 18006383399181957199822848 }, some { target := 252, numerator := 14053762653020064155959296 }, some { target := 253, numerator := 188408255567050235090829312 }, some { target := 254, numerator := 16688843150461326185201664 }, some { target := 255, numerator := 14053762653020064155959296 }, some { target := 256, numerator := 16688843150461326185201664 }, some { target := 257, numerator := 16249663067554449180327936 }, some { target := 258, numerator := 613973755903814052813471744 }, some { target := 259, numerator := 16249663067554449180327936 }, some { target := 260, numerator := 188408255567050235090829312 }, some { target := 261, numerator := 613973755903814052813471744 }, some { target := 262, numerator := 15810482984647572175454208 }, some { target := 263, numerator := 16249663067554449180327936 }, some { target := 264, numerator := 16249663067554449180327936 }, some { target := 265, numerator := 18006383399181957199822848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 387611840913940479140167680 }, some { target := 467, numerator := 441446818818654434576302080 }, some { target := 468, numerator := 344543858590169314791260160 }, some { target := 469, numerator := 4619041104224457376420331520 }, some { target := 470, numerator := 409145832075826061314621440 }, some { target := 471, numerator := 344543858590169314791260160 }, some { target := 472, numerator := 409145832075826061314621440 }, some { target := 473, numerator := 398378836494883270227394560 }, some { target := 474, numerator := 15052259822158021939943178240 }, some { target := 475, numerator := 398378836494883270227394560 }, some { target := 476, numerator := 4619041104224457376420331520 }, some { target := 477, numerator := 15052259822158021939943178240 }, some { target := 478, numerator := 387611840913940479140167680 }, some { target := 479, numerator := 398378836494883270227394560 }, some { target := 480, numerator := 398378836494883270227394560 }, some { target := 481, numerator := 441446818818654434576302080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 286628756044255985890492416 }, some { target := 563, numerator := 326438305494847095041949696 }, some { target := 564, numerator := 254781116483783098569326592 }, some { target := 565, numerator := 3415659342860717165195034624 }, some { target := 566, numerator := 302552575824492429551075328 }, some { target := 567, numerator := 254781116483783098569326592 }, some { target := 568, numerator := 302552575824492429551075328 }, some { target := 569, numerator := 294590665934374207720783872 }, some { target := 570, numerator := 11130750026385274118747455488 }, some { target := 571, numerator := 294590665934374207720783872 }, some { target := 572, numerator := 3415659342860717165195034624 }, some { target := 573, numerator := 11130750026385274118747455488 }, some { target := 574, numerator := 286628756044255985890492416 }, some { target := 575, numerator := 294590665934374207720783872 }, some { target := 576, numerator := 294590665934374207720783872 }, some { target := 577, numerator := 326438305494847095041949696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 319779768754000895290638336 }, some { target := 598, numerator := 364193625525389908525449216 }, some { target := 599, numerator := 284248683336889684702789632 }, some { target := 600, numerator := 3810708910985177335546773504 }, some { target := 601, numerator := 337545311462556500584562688 }, some { target := 602, numerator := 284248683336889684702789632 }, some { target := 603, numerator := 337545311462556500584562688 }, some { target := 604, numerator := 328662540108278697937600512 }, some { target := 605, numerator := 12418114353280368100453122048 }, some { target := 606, numerator := 328662540108278697937600512 }, some { target := 607, numerator := 3810708910985177335546773504 }, some { target := 608, numerator := 12418114353280368100453122048 }, some { target := 609, numerator := 319779768754000895290638336 }, some { target := 610, numerator := 328662540108278697937600512 }, some { target := 611, numerator := 328662540108278697937600512 }, some { target := 612, numerator := 364193625525389908525449216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 15810482984647572175454208 }, some { target := 734, numerator := 18006383399181957199822848 }, some { target := 735, numerator := 14053762653020064155959296 }, some { target := 736, numerator := 188408255567050235090829312 }, some { target := 737, numerator := 16688843150461326185201664 }, some { target := 738, numerator := 14053762653020064155959296 }, some { target := 739, numerator := 16688843150461326185201664 }, some { target := 740, numerator := 16249663067554449180327936 }, some { target := 741, numerator := 613973755903814052813471744 }, some { target := 742, numerator := 16249663067554449180327936 }, some { target := 743, numerator := 188408255567050235090829312 }, some { target := 744, numerator := 613973755903814052813471744 }, some { target := 745, numerator := 15810482984647572175454208 }, some { target := 746, numerator := 16249663067554449180327936 }, some { target := 747, numerator := 16249663067554449180327936 }, some { target := 748, numerator := 18006383399181957199822848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 319269753173850973607559168 }, some { target := 830, numerator := 363612774447996942164164608 }, some { target := 831, numerator := 283795336154534198762274816 }, some { target := 832, numerator := 3804631225321724102156746752 }, some { target := 833, numerator := 337006961683509361030201344 }, some { target := 834, numerator := 283795336154534198762274816 }, some { target := 835, numerator := 337006961683509361030201344 }, some { target := 836, numerator := 328138357428680167318880256 }, some { target := 837, numerator := 12398308748251212808426881024 }, some { target := 838, numerator := 328138357428680167318880256 }, some { target := 839, numerator := 3804631225321724102156746752 }, some { target := 840, numerator := 12398308748251212808426881024 }, some { target := 841, numerator := 319269753173850973607559168 }, some { target := 842, numerator := 328138357428680167318880256 }, some { target := 843, numerator := 328138357428680167318880256 }, some { target := 844, numerator := 363612774447996942164164608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 324879924555500112121430016 }, some { target := 865, numerator := 370002136299319572138295296 }, some { target := 866, numerator := 288782155160444544107937792 }, some { target := 867, numerator := 3871485767619709669447041024 }, some { target := 868, numerator := 342928809253027896128176128 }, some { target := 869, numerator := 288782155160444544107937792 }, some { target := 870, numerator := 342928809253027896128176128 }, some { target := 871, numerator := 333904366904264004124803072 }, some { target := 872, numerator := 12616170403571921020715532288 }, some { target := 873, numerator := 333904366904264004124803072 }, some { target := 874, numerator := 3871485767619709669447041024 }, some { target := 875, numerator := 12616170403571921020715532288 }, some { target := 876, numerator := 324879924555500112121430016 }, some { target := 877, numerator := 333904366904264004124803072 }, some { target := 878, numerator := 333904366904264004124803072 }, some { target := 879, numerator := 370002136299319572138295296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 15810482984647572175454208 }, some { target := 926, numerator := 18006383399181957199822848 }, some { target := 927, numerator := 14053762653020064155959296 }, some { target := 928, numerator := 188408255567050235090829312 }, some { target := 929, numerator := 16688843150461326185201664 }, some { target := 930, numerator := 14053762653020064155959296 }, some { target := 931, numerator := 16688843150461326185201664 }, some { target := 932, numerator := 16249663067554449180327936 }, some { target := 933, numerator := 613973755903814052813471744 }, some { target := 934, numerator := 16249663067554449180327936 }, some { target := 935, numerator := 188408255567050235090829312 }, some { target := 936, numerator := 613973755903814052813471744 }, some { target := 937, numerator := 15810482984647572175454208 }, some { target := 938, numerator := 16249663067554449180327936 }, some { target := 939, numerator := 16249663067554449180327936 }, some { target := 940, numerator := 18006383399181957199822848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 387611840913940479140167680 }, some { target := 961, numerator := 441446818818654434576302080 }, some { target := 962, numerator := 344543858590169314791260160 }, some { target := 963, numerator := 4619041104224457376420331520 }, some { target := 964, numerator := 409145832075826061314621440 }, some { target := 965, numerator := 344543858590169314791260160 }, some { target := 966, numerator := 409145832075826061314621440 }, some { target := 967, numerator := 398378836494883270227394560 }, some { target := 968, numerator := 15052259822158021939943178240 }, some { target := 969, numerator := 398378836494883270227394560 }, some { target := 970, numerator := 4619041104224457376420331520 }, some { target := 971, numerator := 15052259822158021939943178240 }, some { target := 972, numerator := 387611840913940479140167680 }, some { target := 973, numerator := 398378836494883270227394560 }, some { target := 974, numerator := 398378836494883270227394560 }, some { target := 975, numerator := 441446818818654434576302080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 15810482984647572175454208 }, some { target := 987, numerator := 18006383399181957199822848 }, some { target := 988, numerator := 14053762653020064155959296 }, some { target := 989, numerator := 188408255567050235090829312 }, some { target := 990, numerator := 16688843150461326185201664 }, some { target := 991, numerator := 14053762653020064155959296 }, some { target := 992, numerator := 16688843150461326185201664 }, some { target := 993, numerator := 16249663067554449180327936 }, some { target := 994, numerator := 613973755903814052813471744 }, some { target := 995, numerator := 16249663067554449180327936 }, some { target := 996, numerator := 188408255567050235090829312 }, some { target := 997, numerator := 613973755903814052813471744 }, some { target := 998, numerator := 15810482984647572175454208 }, some { target := 999, numerator := 16249663067554449180327936 }, some { target := 1000, numerator := 16249663067554449180327936 }, some { target := 1001, numerator := 18006383399181957199822848 }]

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
def data : BetaFourLocalSlotData := ⟨1, 1, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 613, numerator := 3517797193909415876375871488 }, some { target := 616, numerator := 12848818678405895648654131200 }, some { target := 618, numerator := 3517796008706109140537180160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 880, numerator := 3507531248791003184129638400 }, some { target := 883, numerator := 12811322125842454318940160000 }, some { target := 885, numerator := 3507530067046460962111488000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 976, numerator := 3483577376848040235555094528 }, some { target := 979, numerator := 12723830169861091216274227200 }, some { target := 981, numerator := 3483576203173948545784872960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1002, numerator := 3507531248791003184129638400 }, some { target := 1005, numerator := 12811322125842454318940160000 }, some { target := 1007, numerator := 3507530067046460962111488000 }]

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
def data : BetaFourLocalSlotData := ⟨2, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737471578112, 0, 140737505132544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1012, numerator := 39614076534765685927126761472 }, some { target := 1014, numerator := 39614085979498651666417188864 }]

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
def data : BetaFourLocalSlotData := ⟨3, 135, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  [some { target := 121, numerator := 39299900499479652445716480 }, some { target := 122, numerator := 589498507492194786685747200 }, some { target := 123, numerator := 1034897379819630847737200640 }, some { target := 124, numerator := 39299900499479652445716480 }, some { target := 125, numerator := 654998341657994207428608000 }, some { target := 126, numerator := 39299900499479652445716480 }, some { target := 127, numerator := 1034897379819630847737200640 }, some { target := 128, numerator := 1028347396403050905662914560 }, some { target := 129, numerator := 654998341657994207428608000 }, some { target := 130, numerator := 15870609818373199645995171840 }, some { target := 131, numerator := 1015247429569891021514342400 }, some { target := 132, numerator := 589498507492194786685747200 }, some { target := 133, numerator := 1034897379819630847737200640 }, some { target := 134, numerator := 39299900499479652445716480 }, some { target := 135, numerator := 1015247429569891021514342400 }, some { target := 136, numerator := 39299900499479652445716480 }, some { target := 137, numerator := 1034897379819630847737200640 }, some { target := 138, numerator := 1034897379819630847737200640 }, some { target := 139, numerator := 39299900499479652445716480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 7794539410603317399650304000 }, some { target := 197, numerator := 116918091159049760994754560000 }, some { target := 198, numerator := 205256204479220691524124672000 }, some { target := 199, numerator := 7794539410603317399650304000 }, some { target := 200, numerator := 129908990176721956660838400000 }, some { target := 201, numerator := 7794539410603317399650304000 }, some { target := 202, numerator := 205256204479220691524124672000 }, some { target := 203, numerator := 203957114577453471957516288000 }, some { target := 204, numerator := 129908990176721956660838400000 }, some { target := 205, numerator := 3147694831981973009892114432000 }, some { target := 206, numerator := 201358934773919032824299520000 }, some { target := 207, numerator := 116918091159049760994754560000 }, some { target := 208, numerator := 205256204479220691524124672000 }, some { target := 209, numerator := 7794539410603317399650304000 }, some { target := 210, numerator := 201358934773919032824299520000 }, some { target := 211, numerator := 7794539410603317399650304000 }, some { target := 212, numerator := 205256204479220691524124672000 }, some { target := 213, numerator := 205256204479220691524124672000 }, some { target := 214, numerator := 7794539410603317399650304000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 7794539410603317399650304000 }, some { target := 509, numerator := 116918091159049760994754560000 }, some { target := 510, numerator := 205256204479220691524124672000 }, some { target := 511, numerator := 7794539410603317399650304000 }, some { target := 512, numerator := 129908990176721956660838400000 }, some { target := 513, numerator := 7794539410603317399650304000 }, some { target := 514, numerator := 205256204479220691524124672000 }, some { target := 515, numerator := 203957114577453471957516288000 }, some { target := 516, numerator := 129908990176721956660838400000 }, some { target := 517, numerator := 3147694831981973009892114432000 }, some { target := 518, numerator := 201358934773919032824299520000 }, some { target := 519, numerator := 116918091159049760994754560000 }, some { target := 520, numerator := 205256204479220691524124672000 }, some { target := 521, numerator := 7794539410603317399650304000 }, some { target := 522, numerator := 201358934773919032824299520000 }, some { target := 523, numerator := 7794539410603317399650304000 }, some { target := 524, numerator := 205256204479220691524124672000 }, some { target := 525, numerator := 205256204479220691524124672000 }, some { target := 526, numerator := 7794539410603317399650304000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 39299900499479652445716480 }, some { target := 907, numerator := 589498507492194786685747200 }, some { target := 908, numerator := 1034897379819630847737200640 }, some { target := 909, numerator := 39299900499479652445716480 }, some { target := 910, numerator := 654998341657994207428608000 }, some { target := 911, numerator := 39299900499479652445716480 }, some { target := 912, numerator := 1034897379819630847737200640 }, some { target := 913, numerator := 1028347396403050905662914560 }, some { target := 914, numerator := 654998341657994207428608000 }, some { target := 915, numerator := 15870609818373199645995171840 }, some { target := 916, numerator := 1015247429569891021514342400 }, some { target := 917, numerator := 589498507492194786685747200 }, some { target := 918, numerator := 1034897379819630847737200640 }, some { target := 919, numerator := 39299900499479652445716480 }, some { target := 920, numerator := 1015247429569891021514342400 }, some { target := 921, numerator := 39299900499479652445716480 }, some { target := 922, numerator := 1034897379819630847737200640 }, some { target := 923, numerator := 1034897379819630847737200640 }, some { target := 924, numerator := 39299900499479652445716480 }]

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
def data : BetaFourLocalSlotData := ⟨4, 35, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 734217735192128821091368960 }, some { target := 252, numerator := 28638444859018807277791477760 }, some { target := 255, numerator := 28638434354537339297485291520 }, some { target := 262, numerator := 734221236685951481193431040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 33185305911871497508445224960 }, some { target := 564, numerator := 1294405607402155842492705013760 }, some { target := 567, numerator := 1294405132618703670376681963520 }, some { target := 574, numerator := 33185464173022221547119575040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 738136477208429027812966400 }, some { target := 927, numerator := 28791296897006103196755558400 }, some { target := 930, numerator := 28791286336459041980337356800 }, some { target := 937, numerator := 738139997390782766619033600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0
