import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 51; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 141, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

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
  [some { target := 121, numerator := 80472220462338623825510400 }, some { target := 122, numerator := 1351933303767288880268574720 }, some { target := 123, numerator := 2929188824829125907248578560 }, some { target := 124, numerator := 96566664554806348590612480 }, some { target := 125, numerator := 1545066632876901577449799680 }, some { target := 126, numerator := 112661108647274073355714560 }, some { target := 127, numerator := 2929188824829125907248578560 }, some { target := 128, numerator := 2929188824829125907248578560 }, some { target := 129, numerator := 1545066632876901577449799680 }, some { target := 130, numerator := 36148121431682509822419271680 }, some { target := 131, numerator := 2896999936644190457718374400 }, some { target := 132, numerator := 1351933303767288880268574720 }, some { target := 133, numerator := 2929188824829125907248578560 }, some { target := 134, numerator := 112661108647274073355714560 }, some { target := 135, numerator := 2896999936644190457718374400 }, some { target := 136, numerator := 112661108647274073355714560 }, some { target := 137, numerator := 2929188824829125907248578560 }, some { target := 138, numerator := 2929188824829125907248578560 }, some { target := 139, numerator := 96566664554806348590612480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 6737869402164169921517322240 }, some { target := 197, numerator := 113196205956358054681491013632 }, some { target := 198, numerator := 245258446238775785143230529536 }, some { target := 199, numerator := 8085443282597003905820786688 }, some { target := 200, numerator := 129367092521552062493132587008 }, some { target := 201, numerator := 9433017163029837890124251136 }, some { target := 202, numerator := 245258446238775785143230529536 }, some { target := 203, numerator := 245258446238775785143230529536 }, some { target := 204, numerator := 129367092521552062493132587008 }, some { target := 205, numerator := 3026650935452145128745581150208 }, some { target := 206, numerator := 242563298477910117174623600640 }, some { target := 207, numerator := 113196205956358054681491013632 }, some { target := 208, numerator := 245258446238775785143230529536 }, some { target := 209, numerator := 9433017163029837890124251136 }, some { target := 210, numerator := 242563298477910117174623600640 }, some { target := 211, numerator := 9433017163029837890124251136 }, some { target := 212, numerator := 245258446238775785143230529536 }, some { target := 213, numerator := 245258446238775785143230529536 }, some { target := 214, numerator := 8085443282597003905820786688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 6737871840593152164998676480 }, some { target := 509, numerator := 113196246921964956371977764864 }, some { target := 510, numerator := 245258534997590738805951823872 }, some { target := 511, numerator := 8085446208711782597998411776 }, some { target := 512, numerator := 129367139339388521567974588416 }, some { target := 513, numerator := 9433020576830413030998147072 }, some { target := 514, numerator := 245258534997590738805951823872 }, some { target := 515, numerator := 245258534997590738805951823872 }, some { target := 516, numerator := 129367139339388521567974588416 }, some { target := 517, numerator := 3026652030794443952517405474816 }, some { target := 518, numerator := 242563386261353477939952353280 }, some { target := 519, numerator := 113196246921964956371977764864 }, some { target := 520, numerator := 245258534997590738805951823872 }, some { target := 521, numerator := 9433020576830413030998147072 }, some { target := 522, numerator := 242563386261353477939952353280 }, some { target := 523, numerator := 9433020576830413030998147072 }, some { target := 524, numerator := 245258534997590738805951823872 }, some { target := 525, numerator := 245258534997590738805951823872 }, some { target := 526, numerator := 8085446208711782597998411776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 80469782033356380344156160 }, some { target := 907, numerator := 1351892338160387189781823488 }, some { target := 908, numerator := 2929100066014172244527284224 }, some { target := 909, numerator := 96563738440027656412987392 }, some { target := 910, numerator := 1545019815040442502607798272 }, some { target := 911, numerator := 112657694846698932481818624 }, some { target := 912, numerator := 2929100066014172244527284224 }, some { target := 913, numerator := 2929100066014172244527284224 }, some { target := 914, numerator := 1545019815040442502607798272 }, some { target := 915, numerator := 36147026089383686050594947072 }, some { target := 916, numerator := 2896912153200829692389621760 }, some { target := 917, numerator := 1351892338160387189781823488 }, some { target := 918, numerator := 2929100066014172244527284224 }, some { target := 919, numerator := 112657694846698932481818624 }, some { target := 920, numerator := 2896912153200829692389621760 }, some { target := 921, numerator := 112657694846698932481818624 }, some { target := 922, numerator := 2929100066014172244527284224 }, some { target := 923, numerator := 2929100066014172244527284224 }, some { target := 924, numerator := 96563738440027656412987392 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 75, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 582953660340917868114739200 }, some { target := 252, numerator := 21903066584491184781420134400 }, some { target := 255, numerator := 21901410009227290433342668800 }, some { target := 262, numerator := 584610235604812216192204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 13953277934611647036810854400 }, some { target := 468, numerator := 524260496957821261542378700800 }, some { target := 471, numerator := 524220846027311274243234201600 }, some { target := 478, numerator := 13992928865121634335955353600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 10436751015780948929150976000 }, some { target := 564, numerator := 392135546915890566248005632000 }, some { target := 567, numerator := 392105888874875683564683264000 }, some { target := 574, numerator := 10466409056795831612473344000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 12110392169662938937609420800 }, some { target := 599, numerator := 455018544529429774168856985600 }, some { target := 602, numerator := 454984130514270162550731571200 }, some { target := 609, numerator := 12144806184822550555734835200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 582953660340917868114739200 }, some { target := 735, numerator := 21903066584491184781420134400 }, some { target := 738, numerator := 21901410009227290433342668800 }, some { target := 745, numerator := 584610235604812216192204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 12091587212877748038637977600 }, some { target := 831, numerator := 454311993994446187563004723200 }, some { target := 834, numerator := 454277633417198314472236646400 }, some { target := 841, numerator := 12125947790125621129406054400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 12148002083233320735552307200 }, some { target := 866, numerator := 456431645599396947380561510400 }, some { target := 869, numerator := 456397124708413858707721420800 }, some { target := 876, numerator := 12182522974216409408392396800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 582953660340917868114739200 }, some { target := 927, numerator := 21903066584491184781420134400 }, some { target := 930, numerator := 21901410009227290433342668800 }, some { target := 937, numerator := 584610235604812216192204800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 13953277934611647036810854400 }, some { target := 962, numerator := 524260496957821261542378700800 }, some { target := 965, numerator := 524220846027311274243234201600 }, some { target := 972, numerator := 13992928865121634335955353600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 582953660340917868114739200 }, some { target := 988, numerator := 21903066584491184781420134400 }, some { target := 991, numerator := 21901410009227290433342668800 }, some { target := 998, numerator := 584610235604812216192204800 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 544, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  [some { target := 121, numerator := 132298922308507685414240256 }, some { target := 122, numerator := 21121151591750788570511572992 }, some { target := 124, numerator := 210757330879226727474734825472 }, some { target := 132, numerator := 21121151591750788570511572992 }, some { target := 139, numerator := 132283826584830311191805952 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 11124916078488015532155994112 }, some { target := 197, numerator := 1776061624986803965744522461184 }, some { target := 199, numerator := 17722424174325653883447509254144 }, some { target := 207, numerator := 1776061624986803965744522461184 }, some { target := 214, numerator := 11123646690528352362880303104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 11124913394558810401454161920 }, some { target := 509, numerator := 1776061196505039988084640317440 }, some { target := 511, numerator := 17722419898722000642080023511040 }, some { target := 519, numerator := 1776061196505039988084640317440 }, some { target := 526, numerator := 11123644006905392006839664640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 132301606237712816116072448 }, some { target := 907, numerator := 21121580073514766230393716736 }, some { target := 909, numerator := 210761606482879968842220568576 }, some { target := 917, numerator := 21121580073514766230393716736 }, some { target := 924, numerator := 132286510207790667232444416 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 367, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 34, numerator := 173915914656148698704117760 }, some { target := 35, numerator := 135267933621448987880980480 }, some { target := 36, numerator := 154591924138798843292549120 }, some { target := 37, numerator := 181645510863088640868745216 }, some { target := 38, numerator := 2144962947425833950684119040 }, some { target := 39, numerator := 4823268033130523910727532544 }, some { target := 40, numerator := 135267933621448987880980480 }, some { target := 41, numerator := 2144962947425833950684119040 }, some { target := 42, numerator := 154591924138798843292549120 }, some { target := 43, numerator := 150727126035328872210235392 }, some { target := 44, numerator := 150727126035328872210235392 }, some { target := 45, numerator := 150727126035328872210235392 }, some { target := 46, numerator := 4823268033130523910727532544 }, some { target := 47, numerator := 150727126035328872210235392 }, some { target := 48, numerator := 173915914656148698704117760 }, some { target := 49, numerator := 181645510863088640868745216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 25686470458877760575278940160 }, some { target := 80, numerator := 19978365912460480447439175680 }, some { target := 81, numerator := 22832418185669120511359057920 }, some { target := 82, numerator := 26828091368161216600846893056 }, some { target := 83, numerator := 316799802326159047095106928640 }, some { target := 84, numerator := 712371447392876559954402607104 }, some { target := 85, numerator := 19978365912460480447439175680 }, some { target := 86, numerator := 316799802326159047095106928640 }, some { target := 87, numerator := 22832418185669120511359057920 }, some { target := 88, numerator := 22261607731027392498575081472 }, some { target := 89, numerator := 22261607731027392498575081472 }, some { target := 90, numerator := 22261607731027392498575081472 }, some { target := 91, numerator := 712371447392876559954402607104 }, some { target := 92, numerator := 22261607731027392498575081472 }, some { target := 93, numerator := 25686470458877760575278940160 }, some { target := 94, numerator := 26828091368161216600846893056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 267725785827901794576393830400 }, some { target := 155, numerator := 208231166755034729114972979200 }, some { target := 156, numerator := 237978476291468261845683404800 }, some { target := 157, numerator := 279624709642475207668678000640 }, some { target := 158, numerator := 3301951358544122133108857241600 }, some { target := 159, numerator := 7424928460293809769585322229760 }, some { target := 160, numerator := 208231166755034729114972979200 }, some { target := 161, numerator := 3301951358544122133108857241600 }, some { target := 162, numerator := 237978476291468261845683404800 }, some { target := 163, numerator := 232029014384181555299541319680 }, some { target := 164, numerator := 232029014384181555299541319680 }, some { target := 165, numerator := 232029014384181555299541319680 }, some { target := 166, numerator := 7424928460293809769585322229760 }, some { target := 167, numerator := 232029014384181555299541319680 }, some { target := 168, numerator := 267725785827901794576393830400 }, some { target := 169, numerator := 279624709642475207668678000640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 25686470458877760575278940160 }, some { target := 493, numerator := 19978365912460480447439175680 }, some { target := 494, numerator := 22832418185669120511359057920 }, some { target := 495, numerator := 26828091368161216600846893056 }, some { target := 496, numerator := 316799802326159047095106928640 }, some { target := 497, numerator := 712371447392876559954402607104 }, some { target := 498, numerator := 19978365912460480447439175680 }, some { target := 499, numerator := 316799802326159047095106928640 }, some { target := 500, numerator := 22832418185669120511359057920 }, some { target := 501, numerator := 22261607731027392498575081472 }, some { target := 502, numerator := 22261607731027392498575081472 }, some { target := 503, numerator := 22261607731027392498575081472 }, some { target := 504, numerator := 712371447392876559954402607104 }, some { target := 505, numerator := 22261607731027392498575081472 }, some { target := 506, numerator := 25686470458877760575278940160 }, some { target := 507, numerator := 26828091368161216600846893056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 173915914656148698704117760 }, some { target := 891, numerator := 135267933621448987880980480 }, some { target := 892, numerator := 154591924138798843292549120 }, some { target := 893, numerator := 181645510863088640868745216 }, some { target := 894, numerator := 2144962947425833950684119040 }, some { target := 895, numerator := 4823268033130523910727532544 }, some { target := 896, numerator := 135267933621448987880980480 }, some { target := 897, numerator := 2144962947425833950684119040 }, some { target := 898, numerator := 154591924138798843292549120 }, some { target := 899, numerator := 150727126035328872210235392 }, some { target := 900, numerator := 150727126035328872210235392 }, some { target := 901, numerator := 150727126035328872210235392 }, some { target := 902, numerator := 4823268033130523910727532544 }, some { target := 903, numerator := 150727126035328872210235392 }, some { target := 904, numerator := 173915914656148698704117760 }, some { target := 905, numerator := 181645510863088640868745216 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent1
