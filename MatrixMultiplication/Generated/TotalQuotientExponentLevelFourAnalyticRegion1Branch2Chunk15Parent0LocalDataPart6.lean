import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 3, #[2061584302080, 36696200577024, 2061584302080, 32641751449600, 55731495632896, 2061584302080, 55731495632896, 55731495632896, 36696200577024, 2061584302080, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 14875454421039382423142400 }, some { target := 15, numerator := 15300467404497650492375040 }, some { target := 16, numerator := 14875454421039382423142400 }, some { target := 17, numerator := 13175402487206310146211840 }, some { target := 18, numerator := 616693838997946968456560640 }, some { target := 19, numerator := 167880128466015887346892800 }, some { target := 20, numerator := 15300467404497650492375040 }, some { target := 21, numerator := 616693838997946968456560640 }, some { target := 22, numerator := 14875454421039382423142400 }, some { target := 23, numerator := 14875454421039382423142400 }, some { target := 24, numerator := 12750389503748042076979200 }, some { target := 25, numerator := 14875454421039382423142400 }, some { target := 26, numerator := 167880128466015887346892800 }, some { target := 27, numerator := 12750389503748042076979200 }, some { target := 28, numerator := 14875454421039382423142400 }, some { target := 29, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 40, numerator := 264783088694501007131934720 }, some { target := 41, numerator := 272348319800058178764275712 }, some { target := 42, numerator := 264783088694501007131934720 }, some { target := 43, numerator := 234522164272272320602570752 }, some { target := 44, numerator := 10977150334163456038526779392 }, some { target := 45, numerator := 2988266286695082794774691840 }, some { target := 46, numerator := 272348319800058178764275712 }, some { target := 47, numerator := 10977150334163456038526779392 }, some { target := 48, numerator := 264783088694501007131934720 }, some { target := 49, numerator := 264783088694501007131934720 }, some { target := 50, numerator := 226956933166715148970229760 }, some { target := 51, numerator := 264783088694501007131934720 }, some { target := 52, numerator := 2988266286695082794774691840 }, some { target := 53, numerator := 226956933166715148970229760 }, some { target := 54, numerator := 264783088694501007131934720 }, some { target := 55, numerator := 234522164272272320602570752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 75, numerator := 14875454421039382423142400 }, some { target := 76, numerator := 15300467404497650492375040 }, some { target := 77, numerator := 14875454421039382423142400 }, some { target := 78, numerator := 13175402487206310146211840 }, some { target := 79, numerator := 616693838997946968456560640 }, some { target := 80, numerator := 167880128466015887346892800 }, some { target := 81, numerator := 15300467404497650492375040 }, some { target := 82, numerator := 616693838997946968456560640 }, some { target := 83, numerator := 14875454421039382423142400 }, some { target := 84, numerator := 14875454421039382423142400 }, some { target := 85, numerator := 12750389503748042076979200 }, some { target := 86, numerator := 14875454421039382423142400 }, some { target := 87, numerator := 167880128466015887346892800 }, some { target := 88, numerator := 12750389503748042076979200 }, some { target := 89, numerator := 14875454421039382423142400 }, some { target := 90, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 235528028333123555033088000 }, some { target := 137, numerator := 242257400571212799462604800 }, some { target := 138, numerator := 235528028333123555033088000 }, some { target := 139, numerator := 208610539380766577315020800 }, some { target := 140, numerator := 9764319117467493667228876800 }, some { target := 141, numerator := 2658102034045251549659136000 }, some { target := 142, numerator := 242257400571212799462604800 }, some { target := 143, numerator := 9764319117467493667228876800 }, some { target := 144, numerator := 235528028333123555033088000 }, some { target := 145, numerator := 235528028333123555033088000 }, some { target := 146, numerator := 201881167142677332885504000 }, some { target := 147, numerator := 235528028333123555033088000 }, some { target := 148, numerator := 2658102034045251549659136000 }, some { target := 149, numerator := 201881167142677332885504000 }, some { target := 150, numerator := 235528028333123555033088000 }, some { target := 151, numerator := 208610539380766577315020800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 402133117848764638172282880 }, some { target := 172, numerator := 413622635501586484977205248 }, some { target := 173, numerator := 402133117848764638172282880 }, some { target := 174, numerator := 356175047237477250952593408 }, some { target := 175, numerator := 16671290114244499713942355968 }, some { target := 176, numerator := 4538359472864629487944335360 }, some { target := 177, numerator := 413622635501586484977205248 }, some { target := 178, numerator := 16671290114244499713942355968 }, some { target := 179, numerator := 402133117848764638172282880 }, some { target := 180, numerator := 402133117848764638172282880 }, some { target := 181, numerator := 344685529584655404147671040 }, some { target := 182, numerator := 402133117848764638172282880 }, some { target := 183, numerator := 4538359472864629487944335360 }, some { target := 184, numerator := 344685529584655404147671040 }, some { target := 185, numerator := 402133117848764638172282880 }, some { target := 186, numerator := 356175047237477250952593408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 14875454421039382423142400 }, some { target := 268, numerator := 15300467404497650492375040 }, some { target := 269, numerator := 14875454421039382423142400 }, some { target := 270, numerator := 13175402487206310146211840 }, some { target := 271, numerator := 616693838997946968456560640 }, some { target := 272, numerator := 167880128466015887346892800 }, some { target := 273, numerator := 15300467404497650492375040 }, some { target := 274, numerator := 616693838997946968456560640 }, some { target := 275, numerator := 14875454421039382423142400 }, some { target := 276, numerator := 14875454421039382423142400 }, some { target := 277, numerator := 12750389503748042076979200 }, some { target := 278, numerator := 14875454421039382423142400 }, some { target := 279, numerator := 167880128466015887346892800 }, some { target := 280, numerator := 12750389503748042076979200 }, some { target := 281, numerator := 14875454421039382423142400 }, some { target := 282, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 403, numerator := 402133117848764638172282880 }, some { target := 404, numerator := 413622635501586484977205248 }, some { target := 405, numerator := 402133117848764638172282880 }, some { target := 406, numerator := 356175047237477250952593408 }, some { target := 407, numerator := 16671290114244499713942355968 }, some { target := 408, numerator := 4538359472864629487944335360 }, some { target := 409, numerator := 413622635501586484977205248 }, some { target := 410, numerator := 16671290114244499713942355968 }, some { target := 411, numerator := 402133117848764638172282880 }, some { target := 412, numerator := 402133117848764638172282880 }, some { target := 413, numerator := 344685529584655404147671040 }, some { target := 414, numerator := 402133117848764638172282880 }, some { target := 415, numerator := 4538359472864629487944335360 }, some { target := 416, numerator := 344685529584655404147671040 }, some { target := 417, numerator := 402133117848764638172282880 }, some { target := 418, numerator := 356175047237477250952593408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 438, numerator := 402133117848764638172282880 }, some { target := 439, numerator := 413622635501586484977205248 }, some { target := 440, numerator := 402133117848764638172282880 }, some { target := 441, numerator := 356175047237477250952593408 }, some { target := 442, numerator := 16671290114244499713942355968 }, some { target := 443, numerator := 4538359472864629487944335360 }, some { target := 444, numerator := 413622635501586484977205248 }, some { target := 445, numerator := 16671290114244499713942355968 }, some { target := 446, numerator := 402133117848764638172282880 }, some { target := 447, numerator := 402133117848764638172282880 }, some { target := 448, numerator := 344685529584655404147671040 }, some { target := 449, numerator := 402133117848764638172282880 }, some { target := 450, numerator := 4538359472864629487944335360 }, some { target := 451, numerator := 344685529584655404147671040 }, some { target := 452, numerator := 402133117848764638172282880 }, some { target := 453, numerator := 356175047237477250952593408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 534, numerator := 264783088694501007131934720 }, some { target := 535, numerator := 272348319800058178764275712 }, some { target := 536, numerator := 264783088694501007131934720 }, some { target := 537, numerator := 234522164272272320602570752 }, some { target := 538, numerator := 10977150334163456038526779392 }, some { target := 539, numerator := 2988266286695082794774691840 }, some { target := 540, numerator := 272348319800058178764275712 }, some { target := 541, numerator := 10977150334163456038526779392 }, some { target := 542, numerator := 264783088694501007131934720 }, some { target := 543, numerator := 264783088694501007131934720 }, some { target := 544, numerator := 226956933166715148970229760 }, some { target := 545, numerator := 264783088694501007131934720 }, some { target := 546, numerator := 2988266286695082794774691840 }, some { target := 547, numerator := 226956933166715148970229760 }, some { target := 548, numerator := 264783088694501007131934720 }, some { target := 549, numerator := 234522164272272320602570752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 750, numerator := 14875454421039382423142400 }, some { target := 751, numerator := 15300467404497650492375040 }, some { target := 752, numerator := 14875454421039382423142400 }, some { target := 753, numerator := 13175402487206310146211840 }, some { target := 754, numerator := 616693838997946968456560640 }, some { target := 755, numerator := 167880128466015887346892800 }, some { target := 756, numerator := 15300467404497650492375040 }, some { target := 757, numerator := 616693838997946968456560640 }, some { target := 758, numerator := 14875454421039382423142400 }, some { target := 759, numerator := 14875454421039382423142400 }, some { target := 760, numerator := 12750389503748042076979200 }, some { target := 761, numerator := 14875454421039382423142400 }, some { target := 762, numerator := 167880128466015887346892800 }, some { target := 763, numerator := 12750389503748042076979200 }, some { target := 764, numerator := 14875454421039382423142400 }, some { target := 765, numerator := 13175402487206310146211840 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 4, numerator := 241785163922925834941235200 }, some { target := 5, numerator := 4845374685015433732222353408 }, some { target := 6, numerator := 8133652914367225087423152128 }, some { target := 7, numerator := 7804825091432045951903072256 }, some { target := 8, numerator := 241785163922925834941235200 }, some { target := 9, numerator := 7804825091432045951903072256 }, some { target := 10, numerator := 5212888134178281001333030912 }, some { target := 11, numerator := 251456570479842868338884608 }, some { target := 12, numerator := 4845374685015433732222353408 }, some { target := 13, numerator := 232113757366008801543585792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 241785163922925834941235200 }, some { target := 127, numerator := 4845374685015433732222353408 }, some { target := 128, numerator := 8133652914367225087423152128 }, some { target := 129, numerator := 7804825091432045951903072256 }, some { target := 130, numerator := 241785163922925834941235200 }, some { target := 131, numerator := 7804825091432045951903072256 }, some { target := 132, numerator := 5212888134178281001333030912 }, some { target := 133, numerator := 251456570479842868338884608 }, some { target := 134, numerator := 4845374685015433732222353408 }, some { target := 135, numerator := 232113757366008801543585792 }]

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
def data : BetaFourLocalSlotData := ⟨25, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot25

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0
