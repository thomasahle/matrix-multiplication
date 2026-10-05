import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 1,
parent 58; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 3, #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 15810482984647572175454208 }, some { target := 11, numerator := 387611840913940479140167680 }, some { target := 12, numerator := 286628756044255985890492416 }, some { target := 13, numerator := 319779768754000895290638336 }, some { target := 14, numerator := 15810482984647572175454208 }, some { target := 15, numerator := 319269753173850973607559168 }, some { target := 16, numerator := 324879924555500112121430016 }, some { target := 17, numerator := 15810482984647572175454208 }, some { target := 18, numerator := 387611840913940479140167680 }, some { target := 19, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 24, numerator := 18006383399181957199822848 }, some { target := 25, numerator := 441446818818654434576302080 }, some { target := 26, numerator := 326438305494847095041949696 }, some { target := 27, numerator := 364193625525389908525449216 }, some { target := 28, numerator := 18006383399181957199822848 }, some { target := 29, numerator := 363612774447996942164164608 }, some { target := 30, numerator := 370002136299319572138295296 }, some { target := 31, numerator := 18006383399181957199822848 }, some { target := 32, numerator := 441446818818654434576302080 }, some { target := 33, numerator := 18006383399181957199822848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 14053762653020064155959296 }, some { target := 56, numerator := 344543858590169314791260160 }, some { target := 57, numerator := 254781116483783098569326592 }, some { target := 58, numerator := 284248683336889684702789632 }, some { target := 59, numerator := 14053762653020064155959296 }, some { target := 60, numerator := 283795336154534198762274816 }, some { target := 61, numerator := 288782155160444544107937792 }, some { target := 62, numerator := 14053762653020064155959296 }, some { target := 63, numerator := 344543858590169314791260160 }, some { target := 64, numerator := 14053762653020064155959296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 69, numerator := 188408255567050235090829312 }, some { target := 70, numerator := 4619041104224457376420331520 }, some { target := 71, numerator := 3415659342860717165195034624 }, some { target := 72, numerator := 3810708910985177335546773504 }, some { target := 73, numerator := 188408255567050235090829312 }, some { target := 74, numerator := 3804631225321724102156746752 }, some { target := 75, numerator := 3871485767619709669447041024 }, some { target := 76, numerator := 188408255567050235090829312 }, some { target := 77, numerator := 4619041104224457376420331520 }, some { target := 78, numerator := 188408255567050235090829312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 95, numerator := 16688843150461326185201664 }, some { target := 96, numerator := 409145832075826061314621440 }, some { target := 97, numerator := 302552575824492429551075328 }, some { target := 98, numerator := 337545311462556500584562688 }, some { target := 99, numerator := 16688843150461326185201664 }, some { target := 100, numerator := 337006961683509361030201344 }, some { target := 101, numerator := 342928809253027896128176128 }, some { target := 102, numerator := 16688843150461326185201664 }, some { target := 103, numerator := 409145832075826061314621440 }, some { target := 104, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 14053762653020064155959296 }, some { target := 145, numerator := 344543858590169314791260160 }, some { target := 146, numerator := 254781116483783098569326592 }, some { target := 147, numerator := 284248683336889684702789632 }, some { target := 148, numerator := 14053762653020064155959296 }, some { target := 149, numerator := 283795336154534198762274816 }, some { target := 150, numerator := 288782155160444544107937792 }, some { target := 151, numerator := 14053762653020064155959296 }, some { target := 152, numerator := 344543858590169314791260160 }, some { target := 153, numerator := 14053762653020064155959296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 170, numerator := 16688843150461326185201664 }, some { target := 171, numerator := 409145832075826061314621440 }, some { target := 172, numerator := 302552575824492429551075328 }, some { target := 173, numerator := 337545311462556500584562688 }, some { target := 174, numerator := 16688843150461326185201664 }, some { target := 175, numerator := 337006961683509361030201344 }, some { target := 176, numerator := 342928809253027896128176128 }, some { target := 177, numerator := 16688843150461326185201664 }, some { target := 178, numerator := 409145832075826061314621440 }, some { target := 179, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 271, numerator := 16249663067554449180327936 }, some { target := 272, numerator := 398378836494883270227394560 }, some { target := 273, numerator := 294590665934374207720783872 }, some { target := 274, numerator := 328662540108278697937600512 }, some { target := 275, numerator := 16249663067554449180327936 }, some { target := 276, numerator := 328138357428680167318880256 }, some { target := 277, numerator := 333904366904264004124803072 }, some { target := 278, numerator := 16249663067554449180327936 }, some { target := 279, numerator := 398378836494883270227394560 }, some { target := 280, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 613973755903814052813471744 }, some { target := 286, numerator := 15052259822158021939943178240 }, some { target := 287, numerator := 11130750026385274118747455488 }, some { target := 288, numerator := 12418114353280368100453122048 }, some { target := 289, numerator := 613973755903814052813471744 }, some { target := 290, numerator := 12398308748251212808426881024 }, some { target := 291, numerator := 12616170403571921020715532288 }, some { target := 292, numerator := 613973755903814052813471744 }, some { target := 293, numerator := 15052259822158021939943178240 }, some { target := 294, numerator := 613973755903814052813471744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 16249663067554449180327936 }, some { target := 312, numerator := 398378836494883270227394560 }, some { target := 313, numerator := 294590665934374207720783872 }, some { target := 314, numerator := 328662540108278697937600512 }, some { target := 315, numerator := 16249663067554449180327936 }, some { target := 316, numerator := 328138357428680167318880256 }, some { target := 317, numerator := 333904366904264004124803072 }, some { target := 318, numerator := 16249663067554449180327936 }, some { target := 319, numerator := 398378836494883270227394560 }, some { target := 320, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 360, numerator := 188408255567050235090829312 }, some { target := 361, numerator := 4619041104224457376420331520 }, some { target := 362, numerator := 3415659342860717165195034624 }, some { target := 363, numerator := 3810708910985177335546773504 }, some { target := 364, numerator := 188408255567050235090829312 }, some { target := 365, numerator := 3804631225321724102156746752 }, some { target := 366, numerator := 3871485767619709669447041024 }, some { target := 367, numerator := 188408255567050235090829312 }, some { target := 368, numerator := 4619041104224457376420331520 }, some { target := 369, numerator := 188408255567050235090829312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 613973755903814052813471744 }, some { target := 387, numerator := 15052259822158021939943178240 }, some { target := 388, numerator := 11130750026385274118747455488 }, some { target := 389, numerator := 12418114353280368100453122048 }, some { target := 390, numerator := 613973755903814052813471744 }, some { target := 391, numerator := 12398308748251212808426881024 }, some { target := 392, numerator := 12616170403571921020715532288 }, some { target := 393, numerator := 613973755903814052813471744 }, some { target := 394, numerator := 15052259822158021939943178240 }, some { target := 395, numerator := 613973755903814052813471744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 15810482984647572175454208 }, some { target := 483, numerator := 387611840913940479140167680 }, some { target := 484, numerator := 286628756044255985890492416 }, some { target := 485, numerator := 319779768754000895290638336 }, some { target := 486, numerator := 15810482984647572175454208 }, some { target := 487, numerator := 319269753173850973607559168 }, some { target := 488, numerator := 324879924555500112121430016 }, some { target := 489, numerator := 15810482984647572175454208 }, some { target := 490, numerator := 387611840913940479140167680 }, some { target := 491, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 16249663067554449180327936 }, some { target := 628, numerator := 398378836494883270227394560 }, some { target := 629, numerator := 294590665934374207720783872 }, some { target := 630, numerator := 328662540108278697937600512 }, some { target := 631, numerator := 16249663067554449180327936 }, some { target := 632, numerator := 328138357428680167318880256 }, some { target := 633, numerator := 333904366904264004124803072 }, some { target := 634, numerator := 16249663067554449180327936 }, some { target := 635, numerator := 398378836494883270227394560 }, some { target := 636, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 16249663067554449180327936 }, some { target := 654, numerator := 398378836494883270227394560 }, some { target := 655, numerator := 294590665934374207720783872 }, some { target := 656, numerator := 328662540108278697937600512 }, some { target := 657, numerator := 16249663067554449180327936 }, some { target := 658, numerator := 328138357428680167318880256 }, some { target := 659, numerator := 333904366904264004124803072 }, some { target := 660, numerator := 16249663067554449180327936 }, some { target := 661, numerator := 398378836494883270227394560 }, some { target := 662, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 749, numerator := 18006383399181957199822848 }, some { target := 750, numerator := 441446818818654434576302080 }, some { target := 751, numerator := 326438305494847095041949696 }, some { target := 752, numerator := 364193625525389908525449216 }, some { target := 753, numerator := 18006383399181957199822848 }, some { target := 754, numerator := 363612774447996942164164608 }, some { target := 755, numerator := 370002136299319572138295296 }, some { target := 756, numerator := 18006383399181957199822848 }, some { target := 757, numerator := 441446818818654434576302080 }, some { target := 758, numerator := 18006383399181957199822848 }]

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

end Slot17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0
