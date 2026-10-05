import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 574, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 28999065670494547796295680 }, some { target := 72, numerator := 4629619435730386303068405760 }, some { target := 74, numerator := 46196639942786728222429020160 }, some { target := 82, numerator := 4629619435730386303068405760 }, some { target := 89, numerator := 28995756785776326145474560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 487184303264308402977767424 }, some { target := 147, numerator := 77777606520270489891549216768 }, some { target := 149, numerator := 776103551038817034136807538688 }, some { target := 157, numerator := 77777606520270489891549216768 }, some { target := 164, numerator := 487128714001042279243972608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 1055565990406001539785162752 }, some { target := 182, numerator := 168518147460586061431689969664 }, some { target := 184, numerator := 1681557693917436907296416333824 }, some { target := 192, numerator := 168518147460586061431689969664 }, some { target := 199, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 34798878804593457355554816 }, some { target := 243, numerator := 5555543322876463563682086912 }, some { target := 245, numerator := 55435967931344073866914824192 }, some { target := 253, numerator := 5555543322876463563682086912 }, some { target := 260, numerator := 34794908142931591374569472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 556782060873495317688877056 }, some { target := 278, numerator := 88888693166023417018913390592 }, some { target := 280, numerator := 886975486901505181870637187072 }, some { target := 288, numerator := 88888693166023417018913390592 }, some { target := 295, numerator := 556718530286905461993111552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 40598691938692366914813952 }, some { target := 313, numerator := 6481467210022540824295768064 }, some { target := 315, numerator := 64675295919901419511400628224 }, some { target := 323, numerator := 6481467210022540824295768064 }, some { target := 330, numerator := 40594059500086856603664384 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 1055565990406001539785162752 }, some { target := 414, numerator := 168518147460586061431689969664 }, some { target := 416, numerator := 1681557693917436907296416333824 }, some { target := 424, numerator := 168518147460586061431689969664 }, some { target := 431, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 1055565990406001539785162752 }, some { target := 449, numerator := 168518147460586061431689969664 }, some { target := 451, numerator := 1681557693917436907296416333824 }, some { target := 459, numerator := 168518147460586061431689969664 }, some { target := 466, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 556782060873495317688877056 }, some { target := 510, numerator := 88888693166023417018913390592 }, some { target := 512, numerator := 886975486901505181870637187072 }, some { target := 520, numerator := 88888693166023417018913390592 }, some { target := 527, numerator := 556718530286905461993111552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 13026380299186150870096019456 }, some { target := 545, numerator := 2079625050530089527338327867392 }, some { target := 547, numerator := 20751530662299798317515115855872 }, some { target := 555, numerator := 2079625050530089527338327867392 }, some { target := 562, numerator := 13024893948170725704547172352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 1043966364137803720666644480 }, some { target := 580, numerator := 166666299686293906910462607360 }, some { target := 582, numerator := 1663079037940322216007444725760 }, some { target := 590, numerator := 166666299686293906910462607360 }, some { target := 597, numerator := 1043847244287947741237084160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 487184303264308402977767424 }, some { target := 641, numerator := 77777606520270489891549216768 }, some { target := 643, numerator := 776103551038817034136807538688 }, some { target := 651, numerator := 77777606520270489891549216768 }, some { target := 658, numerator := 487128714001042279243972608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 1055565990406001539785162752 }, some { target := 676, numerator := 168518147460586061431689969664 }, some { target := 678, numerator := 1681557693917436907296416333824 }, some { target := 686, numerator := 168518147460586061431689969664 }, some { target := 693, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 40598691938692366914813952 }, some { target := 777, numerator := 6481467210022540824295768064 }, some { target := 779, numerator := 64675295919901419511400628224 }, some { target := 787, numerator := 6481467210022540824295768064 }, some { target := 794, numerator := 40594059500086856603664384 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 1043966364137803720666644480 }, some { target := 812, numerator := 166666299686293906910462607360 }, some { target := 814, numerator := 1663079037940322216007444725760 }, some { target := 822, numerator := 166666299686293906910462607360 }, some { target := 829, numerator := 1043847244287947741237084160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 40598691938692366914813952 }, some { target := 847, numerator := 6481467210022540824295768064 }, some { target := 849, numerator := 64675295919901419511400628224 }, some { target := 857, numerator := 6481467210022540824295768064 }, some { target := 864, numerator := 40594059500086856603664384 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 1055565990406001539785162752 }, some { target := 908, numerator := 168518147460586061431689969664 }, some { target := 910, numerator := 1681557693917436907296416333824 }, some { target := 918, numerator := 168518147460586061431689969664 }, some { target := 925, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 1055565990406001539785162752 }, some { target := 943, numerator := 168518147460586061431689969664 }, some { target := 945, numerator := 1681557693917436907296416333824 }, some { target := 953, numerator := 168518147460586061431689969664 }, some { target := 960, numerator := 1055445547002258271695273984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 34798878804593457355554816 }, some { target := 1018, numerator := 5555543322876463563682086912 }, some { target := 1020, numerator := 55435967931344073866914824192 }, some { target := 1028, numerator := 5555543322876463563682086912 }, some { target := 1035, numerator := 34794908142931591374569472 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 228, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 29, numerator := 2616190662574901974196551680 }, some { target := 30, numerator := 2034814959780479313263984640 }, some { target := 31, numerator := 2325502811177690643730268160 }, some { target := 32, numerator := 2732465803133786506383065088 }, some { target := 33, numerator := 32266351505090457681757470720 }, some { target := 34, numerator := 72555687708743948084384366592 }, some { target := 35, numerator := 2034814959780479313263984640 }, some { target := 36, numerator := 32266351505090457681757470720 }, some { target := 37, numerator := 2325502811177690643730268160 }, some { target := 38, numerator := 2267365240898248377637011456 }, some { target := 39, numerator := 2267365240898248377637011456 }, some { target := 40, numerator := 2267365240898248377637011456 }, some { target := 41, numerator := 72555687708743948084384366592 }, some { target := 42, numerator := 2267365240898248377637011456 }, some { target := 43, numerator := 2616190662574901974196551680 }, some { target := 44, numerator := 2732465803133786506383065088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 96612440611393860685686374400 }, some { target := 105, numerator := 75143009364417447199978291200 }, some { target := 106, numerator := 85877724987905653942832332800 }, some { target := 107, numerator := 100906326860789143382827991040 }, some { target := 108, numerator := 1191553434207190948456798617600 }, some { target := 109, numerator := 2679385019622656403016368783360 }, some { target := 110, numerator := 75143009364417447199978291200 }, some { target := 111, numerator := 1191553434207190948456798617600 }, some { target := 112, numerator := 85877724987905653942832332800 }, some { target := 113, numerator := 83730781863208012594261524480 }, some { target := 114, numerator := 83730781863208012594261524480 }, some { target := 115, numerator := 83730781863208012594261524480 }, some { target := 116, numerator := 2679385019622656403016368783360 }, some { target := 117, numerator := 83730781863208012594261524480 }, some { target := 118, numerator := 96612440611393860685686374400 }, some { target := 119, numerator := 100906326860789143382827991040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 96612416953444586153186426880 }, some { target := 227, numerator := 75142990963790233674700554240 }, some { target := 228, numerator := 85877703958617409913943490560 }, some { target := 229, numerator := 100906302151375456648883601408 }, some { target := 230, numerator := 1191553142425816562555965931520 }, some { target := 231, numerator := 2679384363508863189315036905472 }, some { target := 232, numerator := 75142990963790233674700554240 }, some { target := 233, numerator := 1191553142425816562555965931520 }, some { target := 234, numerator := 85877703958617409913943490560 }, some { target := 235, numerator := 83730761359651974666094903296 }, some { target := 236, numerator := 83730761359651974666094903296 }, some { target := 237, numerator := 83730761359651974666094903296 }, some { target := 238, numerator := 2679384363508863189315036905472 }, some { target := 239, numerator := 83730761359651974666094903296 }, some { target := 240, numerator := 96612416953444586153186426880 }, some { target := 241, numerator := 100906302151375456648883601408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 2616214320524176506696499200 }, some { target := 625, numerator := 2034833360407692838541721600 }, some { target := 626, numerator := 2325523840465934672619110400 }, some { target := 627, numerator := 2732490512547473240327454720 }, some { target := 628, numerator := 32266643286464843582590156800 }, some { target := 629, numerator := 72556343822537161785716244480 }, some { target := 630, numerator := 2034833360407692838541721600 }, some { target := 631, numerator := 32266643286464843582590156800 }, some { target := 632, numerator := 2325523840465934672619110400 }, some { target := 633, numerator := 2267385744454286305803632640 }, some { target := 634, numerator := 2267385744454286305803632640 }, some { target := 635, numerator := 2267385744454286305803632640 }, some { target := 636, numerator := 72556343822537161785716244480 }, some { target := 637, numerator := 2267385744454286305803632640 }, some { target := 638, numerator := 2616214320524176506696499200 }, some { target := 639, numerator := 2732490512547473240327454720 }]

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

end Slot9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
