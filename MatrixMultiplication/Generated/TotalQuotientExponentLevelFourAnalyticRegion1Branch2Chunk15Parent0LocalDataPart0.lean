import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 1, #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 389, numerator := 241785163922925834941235200 }, some { target := 391, numerator := 241785163922925834941235200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 656, numerator := 4845374685015433732222353408 }, some { target := 658, numerator := 4845374685015433732222353408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 731, numerator := 8133652914367225087423152128 }, some { target := 733, numerator := 8133652914367225087423152128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 745, numerator := 7804825091432045951903072256 }, some { target := 747, numerator := 7804825091432045951903072256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 872, numerator := 241785163922925834941235200 }, some { target := 874, numerator := 241785163922925834941235200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 947, numerator := 7804825091432045951903072256 }, some { target := 949, numerator := 7804825091432045951903072256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 5212888134178281001333030912 }, some { target := 963, numerator := 5212888134178281001333030912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 992, numerator := 251456570479842868338884608 }, some { target := 994, numerator := 251456570479842868338884608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1006, numerator := 4845374685015433732222353408 }, some { target := 1008, numerator := 4845374685015433732222353408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1011, numerator := 232113757366008801543585792 }, some { target := 1013, numerator := 232113757366008801543585792 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 3, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[2061584302080, 36696200577024, 2061584302080, 32641751449600, 55731495632896, 2061584302080, 55731495632896, 55731495632896, 36696200577024, 2061584302080, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 14875454421039382423142400 }, some { target := 258, numerator := 264783088694501007131934720 }, some { target := 259, numerator := 14875454421039382423142400 }, some { target := 260, numerator := 235528028333123555033088000 }, some { target := 261, numerator := 402133117848764638172282880 }, some { target := 262, numerator := 14875454421039382423142400 }, some { target := 263, numerator := 402133117848764638172282880 }, some { target := 264, numerator := 402133117848764638172282880 }, some { target := 265, numerator := 264783088694501007131934720 }, some { target := 266, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 15300467404497650492375040 }, some { target := 354, numerator := 272348319800058178764275712 }, some { target := 355, numerator := 15300467404497650492375040 }, some { target := 356, numerator := 242257400571212799462604800 }, some { target := 357, numerator := 413622635501586484977205248 }, some { target := 358, numerator := 15300467404497650492375040 }, some { target := 359, numerator := 413622635501586484977205248 }, some { target := 360, numerator := 413622635501586484977205248 }, some { target := 361, numerator := 272348319800058178764275712 }, some { target := 362, numerator := 15300467404497650492375040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 14875454421039382423142400 }, some { target := 380, numerator := 264783088694501007131934720 }, some { target := 381, numerator := 14875454421039382423142400 }, some { target := 382, numerator := 235528028333123555033088000 }, some { target := 383, numerator := 402133117848764638172282880 }, some { target := 384, numerator := 14875454421039382423142400 }, some { target := 385, numerator := 402133117848764638172282880 }, some { target := 386, numerator := 402133117848764638172282880 }, some { target := 387, numerator := 264783088694501007131934720 }, some { target := 388, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 13175402487206310146211840 }, some { target := 525, numerator := 234522164272272320602570752 }, some { target := 526, numerator := 13175402487206310146211840 }, some { target := 527, numerator := 208610539380766577315020800 }, some { target := 528, numerator := 356175047237477250952593408 }, some { target := 529, numerator := 13175402487206310146211840 }, some { target := 530, numerator := 356175047237477250952593408 }, some { target := 531, numerator := 356175047237477250952593408 }, some { target := 532, numerator := 234522164272272320602570752 }, some { target := 533, numerator := 13175402487206310146211840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 616693838997946968456560640 }, some { target := 621, numerator := 10977150334163456038526779392 }, some { target := 622, numerator := 616693838997946968456560640 }, some { target := 623, numerator := 9764319117467493667228876800 }, some { target := 624, numerator := 16671290114244499713942355968 }, some { target := 625, numerator := 616693838997946968456560640 }, some { target := 626, numerator := 16671290114244499713942355968 }, some { target := 627, numerator := 16671290114244499713942355968 }, some { target := 628, numerator := 10977150334163456038526779392 }, some { target := 629, numerator := 616693838997946968456560640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 167880128466015887346892800 }, some { target := 647, numerator := 2988266286695082794774691840 }, some { target := 648, numerator := 167880128466015887346892800 }, some { target := 649, numerator := 2658102034045251549659136000 }, some { target := 650, numerator := 4538359472864629487944335360 }, some { target := 651, numerator := 167880128466015887346892800 }, some { target := 652, numerator := 4538359472864629487944335360 }, some { target := 653, numerator := 4538359472864629487944335360 }, some { target := 654, numerator := 2988266286695082794774691840 }, some { target := 655, numerator := 167880128466015887346892800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 15300467404497650492375040 }, some { target := 696, numerator := 272348319800058178764275712 }, some { target := 697, numerator := 15300467404497650492375040 }, some { target := 698, numerator := 242257400571212799462604800 }, some { target := 699, numerator := 413622635501586484977205248 }, some { target := 700, numerator := 15300467404497650492375040 }, some { target := 701, numerator := 413622635501586484977205248 }, some { target := 702, numerator := 413622635501586484977205248 }, some { target := 703, numerator := 272348319800058178764275712 }, some { target := 704, numerator := 15300467404497650492375040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 616693838997946968456560640 }, some { target := 722, numerator := 10977150334163456038526779392 }, some { target := 723, numerator := 616693838997946968456560640 }, some { target := 724, numerator := 9764319117467493667228876800 }, some { target := 725, numerator := 16671290114244499713942355968 }, some { target := 726, numerator := 616693838997946968456560640 }, some { target := 727, numerator := 16671290114244499713942355968 }, some { target := 728, numerator := 16671290114244499713942355968 }, some { target := 729, numerator := 10977150334163456038526779392 }, some { target := 730, numerator := 616693838997946968456560640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 14875454421039382423142400 }, some { target := 736, numerator := 264783088694501007131934720 }, some { target := 737, numerator := 14875454421039382423142400 }, some { target := 738, numerator := 235528028333123555033088000 }, some { target := 739, numerator := 402133117848764638172282880 }, some { target := 740, numerator := 14875454421039382423142400 }, some { target := 741, numerator := 402133117848764638172282880 }, some { target := 742, numerator := 402133117848764638172282880 }, some { target := 743, numerator := 264783088694501007131934720 }, some { target := 744, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 14875454421039382423142400 }, some { target := 837, numerator := 264783088694501007131934720 }, some { target := 838, numerator := 14875454421039382423142400 }, some { target := 839, numerator := 235528028333123555033088000 }, some { target := 840, numerator := 402133117848764638172282880 }, some { target := 841, numerator := 14875454421039382423142400 }, some { target := 842, numerator := 402133117848764638172282880 }, some { target := 843, numerator := 402133117848764638172282880 }, some { target := 844, numerator := 264783088694501007131934720 }, some { target := 845, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 12750389503748042076979200 }, some { target := 863, numerator := 226956933166715148970229760 }, some { target := 864, numerator := 12750389503748042076979200 }, some { target := 865, numerator := 201881167142677332885504000 }, some { target := 866, numerator := 344685529584655404147671040 }, some { target := 867, numerator := 12750389503748042076979200 }, some { target := 868, numerator := 344685529584655404147671040 }, some { target := 869, numerator := 344685529584655404147671040 }, some { target := 870, numerator := 226956933166715148970229760 }, some { target := 871, numerator := 12750389503748042076979200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 14875454421039382423142400 }, some { target := 912, numerator := 264783088694501007131934720 }, some { target := 913, numerator := 14875454421039382423142400 }, some { target := 914, numerator := 235528028333123555033088000 }, some { target := 915, numerator := 402133117848764638172282880 }, some { target := 916, numerator := 14875454421039382423142400 }, some { target := 917, numerator := 402133117848764638172282880 }, some { target := 918, numerator := 402133117848764638172282880 }, some { target := 919, numerator := 264783088694501007131934720 }, some { target := 920, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 167880128466015887346892800 }, some { target := 938, numerator := 2988266286695082794774691840 }, some { target := 939, numerator := 167880128466015887346892800 }, some { target := 940, numerator := 2658102034045251549659136000 }, some { target := 941, numerator := 4538359472864629487944335360 }, some { target := 942, numerator := 167880128466015887346892800 }, some { target := 943, numerator := 4538359472864629487944335360 }, some { target := 944, numerator := 4538359472864629487944335360 }, some { target := 945, numerator := 2988266286695082794774691840 }, some { target := 946, numerator := 167880128466015887346892800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 12750389503748042076979200 }, some { target := 952, numerator := 226956933166715148970229760 }, some { target := 953, numerator := 12750389503748042076979200 }, some { target := 954, numerator := 201881167142677332885504000 }, some { target := 955, numerator := 344685529584655404147671040 }, some { target := 956, numerator := 12750389503748042076979200 }, some { target := 957, numerator := 344685529584655404147671040 }, some { target := 958, numerator := 344685529584655404147671040 }, some { target := 959, numerator := 226956933166715148970229760 }, some { target := 960, numerator := 12750389503748042076979200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 14875454421039382423142400 }, some { target := 983, numerator := 264783088694501007131934720 }, some { target := 984, numerator := 14875454421039382423142400 }, some { target := 985, numerator := 235528028333123555033088000 }, some { target := 986, numerator := 402133117848764638172282880 }, some { target := 987, numerator := 14875454421039382423142400 }, some { target := 988, numerator := 402133117848764638172282880 }, some { target := 989, numerator := 402133117848764638172282880 }, some { target := 990, numerator := 264783088694501007131934720 }, some { target := 991, numerator := 14875454421039382423142400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 13175402487206310146211840 }, some { target := 997, numerator := 234522164272272320602570752 }, some { target := 998, numerator := 13175402487206310146211840 }, some { target := 999, numerator := 208610539380766577315020800 }, some { target := 1000, numerator := 356175047237477250952593408 }, some { target := 1001, numerator := 13175402487206310146211840 }, some { target := 1002, numerator := 356175047237477250952593408 }, some { target := 1003, numerator := 356175047237477250952593408 }, some { target := 1004, numerator := 234522164272272320602570752 }, some { target := 1005, numerator := 13175402487206310146211840 }]

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
def data : BetaFourLocalSlotData := ⟨3, 1, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

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
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 749, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 965, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1010, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1015, numerator := 19807040628566084398385987584 }]

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

end Slot3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0
