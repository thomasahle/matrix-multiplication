import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 77; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 54, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 257, numerator := 8427359047394049876075479040 }, some { target := 260, numerator := 30148320573427938755063316480 }, some { target := 262, numerator := 8427356245794793681437327360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 6554612592417594348058705920 }, some { target := 356, numerator := 23448693779332841253938135040 }, some { target := 358, numerator := 6554610413395950641117921280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 7490985819905822112067092480 }, some { target := 382, numerator := 26798507176380390004500725760 }, some { target := 384, numerator := 7490983329595372161277624320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 8801908338389340981678833664 }, some { target := 527, numerator := 31488245932246958255288352768 }, some { target := 529, numerator := 8801905412274562289501208576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 103937428251193281804930908160 }, some { target := 623, numerator := 371829287072277911312447569920 }, some { target := 625, numerator := 103937393698135788737727037440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 233718757581061649896493285376 }, some { target := 649, numerator := 836113423903068168140422643712 }, some { target := 651, numerator := 233718679883375611431861878784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 6554612592417594348058705920 }, some { target := 698, numerator := 23448693779332841253938135040 }, some { target := 700, numerator := 6554610413395950641117921280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 103937428251193281804930908160 }, some { target := 724, numerator := 371829287072277911312447569920 }, some { target := 726, numerator := 103937393698135788737727037440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 7490985819905822112067092480 }, some { target := 738, numerator := 26798507176380390004500725760 }, some { target := 740, numerator := 7490983329595372161277624320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 7303711174408176559265415168 }, some { target := 839, numerator := 26128544496970880254388207616 }, some { target := 841, numerator := 7303708746355487857245683712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 7303711174408176559265415168 }, some { target := 865, numerator := 26128544496970880254388207616 }, some { target := 867, numerator := 7303708746355487857245683712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 7303711174408176559265415168 }, some { target := 914, numerator := 26128544496970880254388207616 }, some { target := 916, numerator := 7303708746355487857245683712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 233718757581061649896493285376 }, some { target := 940, numerator := 836113423903068168140422643712 }, some { target := 942, numerator := 233718679883375611431861878784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 7303711174408176559265415168 }, some { target := 954, numerator := 26128544496970880254388207616 }, some { target := 956, numerator := 7303708746355487857245683712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 8427359047394049876075479040 }, some { target := 985, numerator := 30148320573427938755063316480 }, some { target := 987, numerator := 8427356245794793681437327360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 8801908338389340981678833664 }, some { target := 999, numerator := 31488245932246958255288352768 }, some { target := 1001, numerator := 8801905412274562289501208576 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 251, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 81156967061119236202037248 }, some { target := 111, numerator := 96373898385079092989919232 }, some { target := 112, numerator := 73548501399139307808096256 }, some { target := 113, numerator := 758310410977332863262785536 }, some { target := 114, numerator := 91301587943759140727291904 }, some { target := 115, numerator := 73548501399139307808096256 }, some { target := 116, numerator := 91301587943759140727291904 }, some { target := 117, numerator := 91301587943759140727291904 }, some { target := 118, numerator := 3910751350257683194485669888 }, some { target := 119, numerator := 91301587943759140727291904 }, some { target := 120, numerator := 758310410977332863262785536 }, some { target := 121, numerator := 3910751350257683194485669888 }, some { target := 122, numerator := 81156967061119236202037248 }, some { target := 123, numerator := 91301587943759140727291904 }, some { target := 124, numerator := 91301587943759140727291904 }, some { target := 125, numerator := 96373898385079092989919232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 12956481988775771005660430336 }, some { target := 207, numerator := 15385822361671228069221761024 }, some { target := 208, numerator := 11741811802328042473879764992 }, some { target := 209, numerator := 121062128582623610334139645952 }, some { target := 210, numerator := 14576042237372742381367984128 }, some { target := 211, numerator := 11741811802328042473879764992 }, some { target := 212, numerator := 14576042237372742381367984128 }, some { target := 213, numerator := 14576042237372742381367984128 }, some { target := 214, numerator := 624340475834132465335261986816 }, some { target := 215, numerator := 14576042237372742381367984128 }, some { target := 216, numerator := 121062128582623610334139645952 }, some { target := 217, numerator := 624340475834132465335261986816 }, some { target := 218, numerator := 12956481988775771005660430336 }, some { target := 219, numerator := 14576042237372742381367984128 }, some { target := 220, numerator := 14576042237372742381367984128 }, some { target := 221, numerator := 15385822361671228069221761024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 129286206278906969018310066176 }, some { target := 303, numerator := 153527369956202025709243203584 }, some { target := 304, numerator := 117165624440259440672843497472 }, some { target := 305, numerator := 1208017989918536991764834680832 }, some { target := 306, numerator := 145446982063770340145598824448 }, some { target := 307, numerator := 117165624440259440672843497472 }, some { target := 308, numerator := 145446982063770340145598824448 }, some { target := 309, numerator := 145446982063770340145598824448 }, some { target := 310, numerator := 6229979065064829569569816313856 }, some { target := 311, numerator := 145446982063770340145598824448 }, some { target := 312, numerator := 1208017989918536991764834680832 }, some { target := 313, numerator := 6229979065064829569569816313856 }, some { target := 314, numerator := 129286206278906969018310066176 }, some { target := 315, numerator := 145446982063770340145598824448 }, some { target := 316, numerator := 145446982063770340145598824448 }, some { target := 317, numerator := 153527369956202025709243203584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 12956481988775771005660430336 }, some { target := 680, numerator := 15385822361671228069221761024 }, some { target := 681, numerator := 11741811802328042473879764992 }, some { target := 682, numerator := 121062128582623610334139645952 }, some { target := 683, numerator := 14576042237372742381367984128 }, some { target := 684, numerator := 11741811802328042473879764992 }, some { target := 685, numerator := 14576042237372742381367984128 }, some { target := 686, numerator := 14576042237372742381367984128 }, some { target := 687, numerator := 624340475834132465335261986816 }, some { target := 688, numerator := 14576042237372742381367984128 }, some { target := 689, numerator := 121062128582623610334139645952 }, some { target := 690, numerator := 624340475834132465335261986816 }, some { target := 691, numerator := 12956481988775771005660430336 }, some { target := 692, numerator := 14576042237372742381367984128 }, some { target := 693, numerator := 14576042237372742381367984128 }, some { target := 694, numerator := 15385822361671228069221761024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 81147706795594234007126016 }, some { target := 967, numerator := 96362901819768152883462144 }, some { target := 968, numerator := 73540109283507274568957952 }, some { target := 969, numerator := 758223885371333624004083712 }, some { target := 970, numerator := 91291170145043513258016768 }, some { target := 971, numerator := 73540109283507274568957952 }, some { target := 972, numerator := 91291170145043513258016768 }, some { target := 973, numerator := 91291170145043513258016768 }, some { target := 974, numerator := 3910305121212697151218384896 }, some { target := 975, numerator := 91291170145043513258016768 }, some { target := 976, numerator := 758223885371333624004083712 }, some { target := 977, numerator := 3910305121212697151218384896 }, some { target := 978, numerator := 81147706795594234007126016 }, some { target := 979, numerator := 91291170145043513258016768 }, some { target := 980, numerator := 91291170145043513258016768 }, some { target := 981, numerator := 96362901819768152883462144 }]

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

end Slot6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent3
