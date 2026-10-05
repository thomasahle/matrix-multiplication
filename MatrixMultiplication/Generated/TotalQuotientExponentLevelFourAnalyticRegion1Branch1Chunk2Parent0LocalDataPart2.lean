import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 9; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 774, numerator := 14040672253129549499426930688 }, some { target := 777, numerator := 51146808563272272855399661568 }, some { target := 779, numerator := 14040681697862515238717358080 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 1, #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 14040672253129549499426930688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 21, numerator := 51146808563272272855399661568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 14040681697862515238717358080 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 5, #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 1213061510460664579767664640 }, some { target := 3, numerator := 1209521447686946687025152000 }, some { target := 4, numerator := 1201261301214938270625955840 }, some { target := 5, numerator := 1209521447686946687025152000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 48497974118109420763343749120 }, some { target := 23, numerator := 48356443065235560586018816000 }, some { target := 24, numerator := 48026203941863220172260638720 }, some { target := 25, numerator := 48356443065235560586018816000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 48497962266076353404956835840 }, some { target := 73, numerator := 48356431247790138365837312000 }, some { target := 74, numerator := 48026192205122303274558423040 }, some { target := 75, numerator := 48356431247790138365837312000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 1213061510460664579767664640 }, some { target := 302, numerator := 1209521447686946687025152000 }, some { target := 303, numerator := 1201261301214938270625955840 }, some { target := 304, numerator := 1209521447686946687025152000 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 28, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 11, numerator := 8324120933377545731047424 }, some { target := 12, numerator := 204075222882804346954711040 }, some { target := 13, numerator := 150908256921231635511246848 }, some { target := 14, numerator := 168362058878313586237636608 }, some { target := 15, numerator := 8324120933377545731047424 }, some { target := 16, numerator := 168093538848204633149538304 }, some { target := 17, numerator := 171047259179403117118619648 }, some { target := 18, numerator := 8324120933377545731047424 }, some { target := 19, numerator := 204075222882804346954711040 }, some { target := 20, numerator := 8324120933377545731047424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 1364163103094846746662010880 }, some { target := 32, numerator := 33443998656518823466552524800 }, some { target := 33, numerator := 24730956901267866826582261760 }, some { target := 34, numerator := 27591298891628029359905832960 }, some { target := 35, numerator := 1364163103094846746662010880 }, some { target := 36, numerator := 27547293630237873013239316480 }, some { target := 37, numerator := 28031351505529592826570997760 }, some { target := 38, numerator := 1364163103094846746662010880 }, some { target := 39, numerator := 33443998656518823466552524800 }, some { target := 40, numerator := 1364163103094846746662010880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 14044587334751521393533255680 }, some { target := 77, numerator := 344318915303585685776944332800 }, some { target := 78, numerator := 254614776842914678166635151360 }, some { target := 79, numerator := 284063105125458190765979074560 }, some { target := 80, numerator := 14044587334751521393533255680 }, some { target := 81, numerator := 283610053921111367495219937280 }, some { target := 82, numerator := 288593617168926423473570447360 }, some { target := 83, numerator := 14044587334751521393533255680 }, some { target := 84, numerator := 344318915303585685776944332800 }, some { target := 85, numerator := 14044587334751521393533255680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 1364163103094846746662010880 }, some { target := 306, numerator := 33443998656518823466552524800 }, some { target := 307, numerator := 24730956901267866826582261760 }, some { target := 308, numerator := 27591298891628029359905832960 }, some { target := 309, numerator := 1364163103094846746662010880 }, some { target := 310, numerator := 27547293630237873013239316480 }, some { target := 311, numerator := 28031351505529592826570997760 }, some { target := 312, numerator := 1364163103094846746662010880 }, some { target := 313, numerator := 33443998656518823466552524800 }, some { target := 314, numerator := 1364163103094846746662010880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 8324120933377545731047424 }, some { target := 644, numerator := 204075222882804346954711040 }, some { target := 645, numerator := 150908256921231635511246848 }, some { target := 646, numerator := 168362058878313586237636608 }, some { target := 647, numerator := 8324120933377545731047424 }, some { target := 648, numerator := 168093538848204633149538304 }, some { target := 649, numerator := 171047259179403117118619648 }, some { target := 650, numerator := 8324120933377545731047424 }, some { target := 651, numerator := 204075222882804346954711040 }, some { target := 652, numerator := 8324120933377545731047424 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 48, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 109457500650402587552514048 }, some { target := 56, numerator := 81510904739661501368893440 }, some { target := 57, numerator := 86168670724785015732830208 }, some { target := 58, numerator := 111786383642964344734482432 }, some { target := 59, numerator := 1497471764217209868005670912 }, some { target := 60, numerator := 2708490920349323602629230592 }, some { target := 61, numerator := 81510904739661501368893440 }, some { target := 62, numerator := 1497471764217209868005670912 }, some { target := 63, numerator := 88497553717346772914798592 }, some { target := 64, numerator := 88497553717346772914798592 }, some { target := 65, numerator := 86168670724785015732830208 }, some { target := 66, numerator := 86168670724785015732830208 }, some { target := 67, numerator := 2708490920349323602629230592 }, some { target := 68, numerator := 86168670724785015732830208 }, some { target := 69, numerator := 109457500650402587552514048 }, some { target := 70, numerator := 111786383642964344734482432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 21709235691754424757544550400 }, some { target := 101, numerator := 16166452110880954606682112000 }, some { target := 102, numerator := 17090249374359866298492518400 }, some { target := 103, numerator := 22171134323493880603449753600 }, some { target := 104, numerator := 297000820208470108917045657600 }, some { target := 105, numerator := 537188108712987148787751321600 }, some { target := 106, numerator := 16166452110880954606682112000 }, some { target := 107, numerator := 297000820208470108917045657600 }, some { target := 108, numerator := 17552148006099322144397721600 }, some { target := 109, numerator := 17552148006099322144397721600 }, some { target := 110, numerator := 17090249374359866298492518400 }, some { target := 111, numerator := 17090249374359866298492518400 }, some { target := 112, numerator := 537188108712987148787751321600 }, some { target := 113, numerator := 17090249374359866298492518400 }, some { target := 114, numerator := 21709235691754424757544550400 }, some { target := 115, numerator := 22171134323493880603449753600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 21709235691754424757544550400 }, some { target := 316, numerator := 16166452110880954606682112000 }, some { target := 317, numerator := 17090249374359866298492518400 }, some { target := 318, numerator := 22171134323493880603449753600 }, some { target := 319, numerator := 297000820208470108917045657600 }, some { target := 320, numerator := 537188108712987148787751321600 }, some { target := 321, numerator := 16166452110880954606682112000 }, some { target := 322, numerator := 297000820208470108917045657600 }, some { target := 323, numerator := 17552148006099322144397721600 }, some { target := 324, numerator := 17552148006099322144397721600 }, some { target := 325, numerator := 17090249374359866298492518400 }, some { target := 326, numerator := 17090249374359866298492518400 }, some { target := 327, numerator := 537188108712987148787751321600 }, some { target := 328, numerator := 17090249374359866298492518400 }, some { target := 329, numerator := 21709235691754424757544550400 }, some { target := 330, numerator := 22171134323493880603449753600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 109457500650402587552514048 }, some { target := 654, numerator := 81510904739661501368893440 }, some { target := 655, numerator := 86168670724785015732830208 }, some { target := 656, numerator := 111786383642964344734482432 }, some { target := 657, numerator := 1497471764217209868005670912 }, some { target := 658, numerator := 2708490920349323602629230592 }, some { target := 659, numerator := 81510904739661501368893440 }, some { target := 660, numerator := 1497471764217209868005670912 }, some { target := 661, numerator := 88497553717346772914798592 }, some { target := 662, numerator := 88497553717346772914798592 }, some { target := 663, numerator := 86168670724785015732830208 }, some { target := 664, numerator := 86168670724785015732830208 }, some { target := 665, numerator := 2708490920349323602629230592 }, some { target := 666, numerator := 86168670724785015732830208 }, some { target := 667, numerator := 109457500650402587552514048 }, some { target := 668, numerator := 111786383642964344734482432 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 9, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 142, numerator := 22127840276321486128545792 }, some { target := 143, numerator := 320853684006661548863913984 }, some { target := 144, numerator := 567947900425584810632675328 }, some { target := 145, numerator := 18439866896934571773788160 }, some { target := 146, numerator := 354045444421143778056732672 }, some { target := 147, numerator := 18439866896934571773788160 }, some { target := 148, numerator := 564259927046197896277917696 }, some { target := 149, numerator := 590075740701906296761221120 }, some { target := 150, numerator := 354045444421143778056732672 }, some { target := 151, numerator := 9039222752877327083510956032 }, some { target := 152, numerator := 579011820563745553696948224 }, some { target := 153, numerator := 320853684006661548863913984 }, some { target := 154, numerator := 564259927046197896277917696 }, some { target := 155, numerator := 18439866896934571773788160 }, some { target := 156, numerator := 579011820563745553696948224 }, some { target := 157, numerator := 18439866896934571773788160 }, some { target := 158, numerator := 564259927046197896277917696 }, some { target := 159, numerator := 590075740701906296761221120 }, some { target := 160, numerator := 22127840276321486128545792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 1000138124621307718498516992 }, some { target := 358, numerator := 14502002807008961918228496384 }, some { target := 359, numerator := 25670211865280231441461936128 }, some { target := 360, numerator := 833448437184423098748764160 }, some { target := 361, numerator := 16002209993940923495976271872 }, some { target := 362, numerator := 833448437184423098748764160 }, some { target := 363, numerator := 25503522177843346821712183296 }, some { target := 364, numerator := 26670349989901539159960453120 }, some { target := 365, numerator := 16002209993940923495976271872 }, some { target := 366, numerator := 408556423907804203006644191232 }, some { target := 367, numerator := 26170280927590885300711194624 }, some { target := 368, numerator := 14502002807008961918228496384 }, some { target := 369, numerator := 25503522177843346821712183296 }, some { target := 370, numerator := 833448437184423098748764160 }, some { target := 371, numerator := 26170280927590885300711194624 }, some { target := 372, numerator := 833448437184423098748764160 }, some { target := 373, numerator := 25503522177843346821712183296 }, some { target := 374, numerator := 26670349989901539159960453120 }, some { target := 375, numerator := 1000138124621307718498516992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 22245943249410402319073280 }, some { target := 670, numerator := 322566177116450833626562560 }, some { target := 671, numerator := 570979210068200326189547520 }, some { target := 672, numerator := 18538286041175335265894400 }, some { target := 673, numerator := 355935091990566437105172480 }, some { target := 674, numerator := 18538286041175335265894400 }, some { target := 675, numerator := 567271552859965259136368640 }, some { target := 676, numerator := 593225153317610728508620800 }, some { target := 677, numerator := 355935091990566437105172480 }, some { target := 678, numerator := 9087467817384149347341434880 }, some { target := 679, numerator := 582102181692905527349084160 }, some { target := 680, numerator := 322566177116450833626562560 }, some { target := 681, numerator := 567271552859965259136368640 }, some { target := 682, numerator := 18538286041175335265894400 }, some { target := 683, numerator := 582102181692905527349084160 }, some { target := 684, numerator := 18538286041175335265894400 }, some { target := 685, numerator := 567271552859965259136368640 }, some { target := 686, numerator := 593225153317610728508620800 }, some { target := 687, numerator := 22245943249410402319073280 }]

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

end Slot10

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent0
