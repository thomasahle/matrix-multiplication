import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 4011, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 35, numerator := 783006079346578265345919811584 }, some { target := 37, numerator := 27403260579235089836290502295552 }, some { target := 40, numerator := 27403274019495985873817639583744 }, some { target := 47, numerator := 782999359216130246582351167488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 2847961895231719784004955668480 }, some { target := 147, numerator := 99671565768550110266427640381440 }, some { target := 150, numerator := 99671614653676169351961174343680 }, some { target := 157, numerator := 2847937452668690241238188687360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 783006079346578265345919811584 }, some { target := 218, numerator := 27403260579235089836290502295552 }, some { target := 221, numerator := 27403274019495985873817639583744 }, some { target := 228, numerator := 782999359216130246582351167488 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 3144, #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 16, numerator := 92816794197964655114185605120 }, some { target := 17, numerator := 9731673470336177860379337031680 }, some { target := 19, numerator := 104897713214033816964657315840000 }, some { target := 27, numerator := 9731680893898058846115169566720 }, some { target := 34, numerator := 92816794197964655114185605120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 92816749939478828277722775552 }, some { target := 127, numerator := 9731668829913762067451612233728 }, some { target := 129, numerator := 104897663194918271464834596864000 }, some { target := 137, numerator := 9731676253472103223880331558912 }, some { target := 144, numerator := 92816749939478828277722775552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 124, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 57974698810927143823364587520 }, some { target := 1, numerator := 4854171377073461786976360333312 }, some { target := 6, numerator := 4854173133793793414484379828224 }, some { target := 14, numerator := 57972942090595516315345092608 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 3, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 86, numerator := 14053762653020064155959296 }, some { target := 87, numerator := 344543858590169314791260160 }, some { target := 88, numerator := 14053762653020064155959296 }, some { target := 89, numerator := 288782155160444544107937792 }, some { target := 90, numerator := 283795336154534198762274816 }, some { target := 91, numerator := 14053762653020064155959296 }, some { target := 92, numerator := 284248683336889684702789632 }, some { target := 93, numerator := 254781116483783098569326592 }, some { target := 94, numerator := 344543858590169314791260160 }, some { target := 95, numerator := 14053762653020064155959296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 112, numerator := 16688843150461326185201664 }, some { target := 113, numerator := 409145832075826061314621440 }, some { target := 114, numerator := 16688843150461326185201664 }, some { target := 115, numerator := 342928809253027896128176128 }, some { target := 116, numerator := 337006961683509361030201344 }, some { target := 117, numerator := 16688843150461326185201664 }, some { target := 118, numerator := 337545311462556500584562688 }, some { target := 119, numerator := 302552575824492429551075328 }, some { target := 120, numerator := 409145832075826061314621440 }, some { target := 121, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 161, numerator := 12736222404299433141338112 }, some { target := 162, numerator := 312242871847340941529579520 }, some { target := 163, numerator := 12736222404299433141338112 }, some { target := 164, numerator := 261708828114152868097818624 }, some { target := 165, numerator := 257189523390046617628311552 }, some { target := 166, numerator := 12736222404299433141338112 }, some { target := 167, numerator := 257600369274056276761903104 }, some { target := 168, numerator := 230895386813428433078452224 }, some { target := 169, numerator := 312242871847340941529579520 }, some { target := 170, numerator := 12736222404299433141338112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 131314844789156224457244672 }, some { target := 188, numerator := 3219331678701894535080837120 }, some { target := 189, numerator := 131314844789156224457244672 }, some { target := 190, numerator := 2698308262280403709008543744 }, some { target := 191, numerator := 2651712672193928919685005312 }, some { target := 192, numerator := 131314844789156224457244672 }, some { target := 193, numerator := 2655948634929062991441690624 }, some { target := 194, numerator := 2380611057145348327257145344 }, some { target := 195, numerator := 3219331678701894535080837120 }, some { target := 196, numerator := 131314844789156224457244672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 201, numerator := 15810482984647572175454208 }, some { target := 202, numerator := 387611840913940479140167680 }, some { target := 203, numerator := 15810482984647572175454208 }, some { target := 204, numerator := 324879924555500112121430016 }, some { target := 205, numerator := 319269753173850973607559168 }, some { target := 206, numerator := 15810482984647572175454208 }, some { target := 207, numerator := 319779768754000895290638336 }, some { target := 208, numerator := 286628756044255985890492416 }, some { target := 209, numerator := 387611840913940479140167680 }, some { target := 210, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 232, numerator := 12736222404299433141338112 }, some { target := 233, numerator := 312242871847340941529579520 }, some { target := 234, numerator := 12736222404299433141338112 }, some { target := 235, numerator := 261708828114152868097818624 }, some { target := 236, numerator := 257189523390046617628311552 }, some { target := 237, numerator := 12736222404299433141338112 }, some { target := 238, numerator := 257600369274056276761903104 }, some { target := 239, numerator := 230895386813428433078452224 }, some { target := 240, numerator := 312242871847340941529579520 }, some { target := 241, numerator := 12736222404299433141338112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 246, numerator := 15810482984647572175454208 }, some { target := 247, numerator := 387611840913940479140167680 }, some { target := 248, numerator := 15810482984647572175454208 }, some { target := 249, numerator := 324879924555500112121430016 }, some { target := 250, numerator := 319269753173850973607559168 }, some { target := 251, numerator := 15810482984647572175454208 }, some { target := 252, numerator := 319779768754000895290638336 }, some { target := 253, numerator := 286628756044255985890492416 }, some { target := 254, numerator := 387611840913940479140167680 }, some { target := 255, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 15810482984647572175454208 }, some { target := 302, numerator := 387611840913940479140167680 }, some { target := 303, numerator := 15810482984647572175454208 }, some { target := 304, numerator := 324879924555500112121430016 }, some { target := 305, numerator := 319269753173850973607559168 }, some { target := 306, numerator := 15810482984647572175454208 }, some { target := 307, numerator := 319779768754000895290638336 }, some { target := 308, numerator := 286628756044255985890492416 }, some { target := 309, numerator := 387611840913940479140167680 }, some { target := 310, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 327, numerator := 677215687842404341515288576 }, some { target := 328, numerator := 16602707185813783856503848960 }, some { target := 329, numerator := 677215687842404341515288576 }, some { target := 330, numerator := 13915690101793921469201252352 }, some { target := 331, numerator := 13675387760946616702857117696 }, some { target := 332, numerator := 677215687842404341515288576 }, some { target := 333, numerator := 13697233428296371681615675392 }, some { target := 334, numerator := 12277265050562298062309425152 }, some { target := 335, numerator := 16602707185813783856503848960 }, some { target := 336, numerator := 677215687842404341515288576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 15810482984647572175454208 }, some { target := 342, numerator := 387611840913940479140167680 }, some { target := 343, numerator := 15810482984647572175454208 }, some { target := 344, numerator := 324879924555500112121430016 }, some { target := 345, numerator := 319269753173850973607559168 }, some { target := 346, numerator := 15810482984647572175454208 }, some { target := 347, numerator := 319779768754000895290638336 }, some { target := 348, numerator := 286628756044255985890492416 }, some { target := 349, numerator := 387611840913940479140167680 }, some { target := 350, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 372, numerator := 131314844789156224457244672 }, some { target := 373, numerator := 3219331678701894535080837120 }, some { target := 374, numerator := 131314844789156224457244672 }, some { target := 375, numerator := 2698308262280403709008543744 }, some { target := 376, numerator := 2651712672193928919685005312 }, some { target := 377, numerator := 131314844789156224457244672 }, some { target := 378, numerator := 2655948634929062991441690624 }, some { target := 379, numerator := 2380611057145348327257145344 }, some { target := 380, numerator := 3219331678701894535080837120 }, some { target := 381, numerator := 131314844789156224457244672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 677215687842404341515288576 }, some { target := 387, numerator := 16602707185813783856503848960 }, some { target := 388, numerator := 677215687842404341515288576 }, some { target := 389, numerator := 13915690101793921469201252352 }, some { target := 390, numerator := 13675387760946616702857117696 }, some { target := 391, numerator := 677215687842404341515288576 }, some { target := 392, numerator := 13697233428296371681615675392 }, some { target := 393, numerator := 12277265050562298062309425152 }, some { target := 394, numerator := 16602707185813783856503848960 }, some { target := 395, numerator := 677215687842404341515288576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 406, numerator := 14053762653020064155959296 }, some { target := 407, numerator := 344543858590169314791260160 }, some { target := 408, numerator := 14053762653020064155959296 }, some { target := 409, numerator := 288782155160444544107937792 }, some { target := 410, numerator := 283795336154534198762274816 }, some { target := 411, numerator := 14053762653020064155959296 }, some { target := 412, numerator := 284248683336889684702789632 }, some { target := 413, numerator := 254781116483783098569326592 }, some { target := 414, numerator := 344543858590169314791260160 }, some { target := 415, numerator := 14053762653020064155959296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 15810482984647572175454208 }, some { target := 444, numerator := 387611840913940479140167680 }, some { target := 445, numerator := 15810482984647572175454208 }, some { target := 446, numerator := 324879924555500112121430016 }, some { target := 447, numerator := 319269753173850973607559168 }, some { target := 448, numerator := 15810482984647572175454208 }, some { target := 449, numerator := 319779768754000895290638336 }, some { target := 450, numerator := 286628756044255985890492416 }, some { target := 451, numerator := 387611840913940479140167680 }, some { target := 452, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 457, numerator := 15810482984647572175454208 }, some { target := 458, numerator := 387611840913940479140167680 }, some { target := 459, numerator := 15810482984647572175454208 }, some { target := 460, numerator := 324879924555500112121430016 }, some { target := 461, numerator := 319269753173850973607559168 }, some { target := 462, numerator := 15810482984647572175454208 }, some { target := 463, numerator := 319779768754000895290638336 }, some { target := 464, numerator := 286628756044255985890492416 }, some { target := 465, numerator := 387611840913940479140167680 }, some { target := 466, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 477, numerator := 16688843150461326185201664 }, some { target := 478, numerator := 409145832075826061314621440 }, some { target := 479, numerator := 16688843150461326185201664 }, some { target := 480, numerator := 342928809253027896128176128 }, some { target := 481, numerator := 337006961683509361030201344 }, some { target := 482, numerator := 16688843150461326185201664 }, some { target := 483, numerator := 337545311462556500584562688 }, some { target := 484, numerator := 302552575824492429551075328 }, some { target := 485, numerator := 409145832075826061314621440 }, some { target := 486, numerator := 16688843150461326185201664 }]

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

end Slot26

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1
