import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 52, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 86, numerator := 8656250280780061107277529088 }, some { target := 89, numerator := 30967163848261784005200838656 }, some { target := 91, numerator := 8656247403087985608587476992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 112, numerator := 8475911733263809834209247232 }, some { target := 115, numerator := 30322014601422996838425821184 }, some { target := 117, numerator := 8475908915523652575075237888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 161, numerator := 6672526258101297103526428672 }, some { target := 164, numerator := 23870522133035125170675646464 }, some { target := 166, numerator := 6672524039880322239952846848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 209733730761400230578411798528 }, some { target := 190, numerator := 750308574073509474959345319936 }, some { target := 192, numerator := 209733661037319317974734077952 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 201, numerator := 6672526258101297103526428672 }, some { target := 204, numerator := 23870522133035125170675646464 }, some { target := 206, numerator := 6672524039880322239952846848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 232, numerator := 6672526258101297103526428672 }, some { target := 235, numerator := 23870522133035125170675646464 }, some { target := 237, numerator := 6672524039880322239952846848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 246, numerator := 6852864805617548376594710528 }, some { target := 249, numerator := 24515671379873912337450663936 }, some { target := 251, numerator := 6852862527444655273465085952 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 6852864805617548376594710528 }, some { target := 304, numerator := 24515671379873912337450663936 }, some { target := 306, numerator := 6852862527444655273465085952 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 327, numerator := 115957686052949568582905233408 }, some { target := 330, numerator := 414830965717340148236336234496 }, some { target := 332, numerator := 115957647503866140548369743872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 6311849163068794557389864960 }, some { target := 344, numerator := 22580223639357550837125611520 }, some { target := 346, numerator := 6311847064751656172928368640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 372, numerator := 209733730761400230578411798528 }, some { target := 375, numerator := 750308574073509474959345319936 }, some { target := 377, numerator := 209733661037319317974734077952 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 386, numerator := 115957686052949568582905233408 }, some { target := 389, numerator := 414830965717340148236336234496 }, some { target := 391, numerator := 115957647503866140548369743872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 406, numerator := 8656250280780061107277529088 }, some { target := 409, numerator := 30967163848261784005200838656 }, some { target := 411, numerator := 8656247403087985608587476992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 6672526258101297103526428672 }, some { target := 446, numerator := 23870522133035125170675646464 }, some { target := 448, numerator := 6672524039880322239952846848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 457, numerator := 6311849163068794557389864960 }, some { target := 460, numerator := 22580223639357550837125611520 }, some { target := 462, numerator := 6311847064751656172928368640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 477, numerator := 8475911733263809834209247232 }, some { target := 480, numerator := 30322014601422996838425821184 }, some { target := 482, numerator := 8475908915523652575075237888 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 3, #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

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
  [some { target := 35, numerator := 14053762653020064155959296 }, some { target := 36, numerator := 16688843150461326185201664 }, some { target := 37, numerator := 12736222404299433141338112 }, some { target := 38, numerator := 131314844789156224457244672 }, some { target := 39, numerator := 15810482984647572175454208 }, some { target := 40, numerator := 12736222404299433141338112 }, some { target := 41, numerator := 15810482984647572175454208 }, some { target := 42, numerator := 15810482984647572175454208 }, some { target := 43, numerator := 677215687842404341515288576 }, some { target := 44, numerator := 15810482984647572175454208 }, some { target := 45, numerator := 131314844789156224457244672 }, some { target := 46, numerator := 677215687842404341515288576 }, some { target := 47, numerator := 14053762653020064155959296 }, some { target := 48, numerator := 15810482984647572175454208 }, some { target := 49, numerator := 15810482984647572175454208 }, some { target := 50, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 70, numerator := 344543858590169314791260160 }, some { target := 71, numerator := 409145832075826061314621440 }, some { target := 72, numerator := 312242871847340941529579520 }, some { target := 73, numerator := 3219331678701894535080837120 }, some { target := 74, numerator := 387611840913940479140167680 }, some { target := 75, numerator := 312242871847340941529579520 }, some { target := 76, numerator := 387611840913940479140167680 }, some { target := 77, numerator := 387611840913940479140167680 }, some { target := 78, numerator := 16602707185813783856503848960 }, some { target := 79, numerator := 387611840913940479140167680 }, some { target := 80, numerator := 3219331678701894535080837120 }, some { target := 81, numerator := 16602707185813783856503848960 }, some { target := 82, numerator := 344543858590169314791260160 }, some { target := 83, numerator := 387611840913940479140167680 }, some { target := 84, numerator := 387611840913940479140167680 }, some { target := 85, numerator := 409145832075826061314621440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 14053762653020064155959296 }, some { target := 97, numerator := 16688843150461326185201664 }, some { target := 98, numerator := 12736222404299433141338112 }, some { target := 99, numerator := 131314844789156224457244672 }, some { target := 100, numerator := 15810482984647572175454208 }, some { target := 101, numerator := 12736222404299433141338112 }, some { target := 102, numerator := 15810482984647572175454208 }, some { target := 103, numerator := 15810482984647572175454208 }, some { target := 104, numerator := 677215687842404341515288576 }, some { target := 105, numerator := 15810482984647572175454208 }, some { target := 106, numerator := 131314844789156224457244672 }, some { target := 107, numerator := 677215687842404341515288576 }, some { target := 108, numerator := 14053762653020064155959296 }, some { target := 109, numerator := 15810482984647572175454208 }, some { target := 110, numerator := 15810482984647572175454208 }, some { target := 111, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 288782155160444544107937792 }, some { target := 146, numerator := 342928809253027896128176128 }, some { target := 147, numerator := 261708828114152868097818624 }, some { target := 148, numerator := 2698308262280403709008543744 }, some { target := 149, numerator := 324879924555500112121430016 }, some { target := 150, numerator := 261708828114152868097818624 }, some { target := 151, numerator := 324879924555500112121430016 }, some { target := 152, numerator := 324879924555500112121430016 }, some { target := 153, numerator := 13915690101793921469201252352 }, some { target := 154, numerator := 324879924555500112121430016 }, some { target := 155, numerator := 2698308262280403709008543744 }, some { target := 156, numerator := 13915690101793921469201252352 }, some { target := 157, numerator := 288782155160444544107937792 }, some { target := 158, numerator := 324879924555500112121430016 }, some { target := 159, numerator := 324879924555500112121430016 }, some { target := 160, numerator := 342928809253027896128176128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 283795336154534198762274816 }, some { target := 172, numerator := 337006961683509361030201344 }, some { target := 173, numerator := 257189523390046617628311552 }, some { target := 174, numerator := 2651712672193928919685005312 }, some { target := 175, numerator := 319269753173850973607559168 }, some { target := 176, numerator := 257189523390046617628311552 }, some { target := 177, numerator := 319269753173850973607559168 }, some { target := 178, numerator := 319269753173850973607559168 }, some { target := 179, numerator := 13675387760946616702857117696 }, some { target := 180, numerator := 319269753173850973607559168 }, some { target := 181, numerator := 2651712672193928919685005312 }, some { target := 182, numerator := 13675387760946616702857117696 }, some { target := 183, numerator := 283795336154534198762274816 }, some { target := 184, numerator := 319269753173850973607559168 }, some { target := 185, numerator := 319269753173850973607559168 }, some { target := 186, numerator := 337006961683509361030201344 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 14053762653020064155959296 }, some { target := 217, numerator := 16688843150461326185201664 }, some { target := 218, numerator := 12736222404299433141338112 }, some { target := 219, numerator := 131314844789156224457244672 }, some { target := 220, numerator := 15810482984647572175454208 }, some { target := 221, numerator := 12736222404299433141338112 }, some { target := 222, numerator := 15810482984647572175454208 }, some { target := 223, numerator := 15810482984647572175454208 }, some { target := 224, numerator := 677215687842404341515288576 }, some { target := 225, numerator := 15810482984647572175454208 }, some { target := 226, numerator := 131314844789156224457244672 }, some { target := 227, numerator := 677215687842404341515288576 }, some { target := 228, numerator := 14053762653020064155959296 }, some { target := 229, numerator := 15810482984647572175454208 }, some { target := 230, numerator := 15810482984647572175454208 }, some { target := 231, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 284248683336889684702789632 }, some { target := 286, numerator := 337545311462556500584562688 }, some { target := 287, numerator := 257600369274056276761903104 }, some { target := 288, numerator := 2655948634929062991441690624 }, some { target := 289, numerator := 319779768754000895290638336 }, some { target := 290, numerator := 257600369274056276761903104 }, some { target := 291, numerator := 319779768754000895290638336 }, some { target := 292, numerator := 319779768754000895290638336 }, some { target := 293, numerator := 13697233428296371681615675392 }, some { target := 294, numerator := 319779768754000895290638336 }, some { target := 295, numerator := 2655948634929062991441690624 }, some { target := 296, numerator := 13697233428296371681615675392 }, some { target := 297, numerator := 284248683336889684702789632 }, some { target := 298, numerator := 319779768754000895290638336 }, some { target := 299, numerator := 319779768754000895290638336 }, some { target := 300, numerator := 337545311462556500584562688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 254781116483783098569326592 }, some { target := 312, numerator := 302552575824492429551075328 }, some { target := 313, numerator := 230895386813428433078452224 }, some { target := 314, numerator := 2380611057145348327257145344 }, some { target := 315, numerator := 286628756044255985890492416 }, some { target := 316, numerator := 230895386813428433078452224 }, some { target := 317, numerator := 286628756044255985890492416 }, some { target := 318, numerator := 286628756044255985890492416 }, some { target := 319, numerator := 12277265050562298062309425152 }, some { target := 320, numerator := 286628756044255985890492416 }, some { target := 321, numerator := 2380611057145348327257145344 }, some { target := 322, numerator := 12277265050562298062309425152 }, some { target := 323, numerator := 254781116483783098569326592 }, some { target := 324, numerator := 286628756044255985890492416 }, some { target := 325, numerator := 286628756044255985890492416 }, some { target := 326, numerator := 302552575824492429551075328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 344543858590169314791260160 }, some { target := 357, numerator := 409145832075826061314621440 }, some { target := 358, numerator := 312242871847340941529579520 }, some { target := 359, numerator := 3219331678701894535080837120 }, some { target := 360, numerator := 387611840913940479140167680 }, some { target := 361, numerator := 312242871847340941529579520 }, some { target := 362, numerator := 387611840913940479140167680 }, some { target := 363, numerator := 387611840913940479140167680 }, some { target := 364, numerator := 16602707185813783856503848960 }, some { target := 365, numerator := 387611840913940479140167680 }, some { target := 366, numerator := 3219331678701894535080837120 }, some { target := 367, numerator := 16602707185813783856503848960 }, some { target := 368, numerator := 344543858590169314791260160 }, some { target := 369, numerator := 387611840913940479140167680 }, some { target := 370, numerator := 387611840913940479140167680 }, some { target := 371, numerator := 409145832075826061314621440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 14053762653020064155959296 }, some { target := 428, numerator := 16688843150461326185201664 }, some { target := 429, numerator := 12736222404299433141338112 }, some { target := 430, numerator := 131314844789156224457244672 }, some { target := 431, numerator := 15810482984647572175454208 }, some { target := 432, numerator := 12736222404299433141338112 }, some { target := 433, numerator := 15810482984647572175454208 }, some { target := 434, numerator := 15810482984647572175454208 }, some { target := 435, numerator := 677215687842404341515288576 }, some { target := 436, numerator := 15810482984647572175454208 }, some { target := 437, numerator := 131314844789156224457244672 }, some { target := 438, numerator := 677215687842404341515288576 }, some { target := 439, numerator := 14053762653020064155959296 }, some { target := 440, numerator := 15810482984647572175454208 }, some { target := 441, numerator := 15810482984647572175454208 }, some { target := 442, numerator := 16688843150461326185201664 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 126, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

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
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 58909774598200162272128532480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 260, numerator := 4932464463800453106121140338688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 420, numerator := 4932466248854983630847031115776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 58907989543669637546237755392 }]

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

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1
