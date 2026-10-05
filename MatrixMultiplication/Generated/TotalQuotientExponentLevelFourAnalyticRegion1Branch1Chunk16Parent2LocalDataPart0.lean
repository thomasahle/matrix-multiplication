import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨1, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 3, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 44255680552642972257091584 }, some { target := 251, numerator := 50402302851621162848354304 }, some { target := 252, numerator := 39338382713460419784081408 }, some { target := 253, numerator := 527380193252328752730341376 }, some { target := 254, numerator := 46714329472234248493596672 }, some { target := 255, numerator := 39338382713460419784081408 }, some { target := 256, numerator := 46714329472234248493596672 }, some { target := 257, numerator := 45485005012438610375344128 }, some { target := 258, numerator := 1718595594794302089317056512 }, some { target := 259, numerator := 45485005012438610375344128 }, some { target := 260, numerator := 527380193252328752730341376 }, some { target := 261, numerator := 1718595594794302089317056512 }, some { target := 262, numerator := 44255680552642972257091584 }, some { target := 263, numerator := 45485005012438610375344128 }, some { target := 264, numerator := 45485005012438610375344128 }, some { target := 265, numerator := 50402302851621162848354304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 2000276249242615436997033984 }, some { target := 563, numerator := 2278092394970756469913288704 }, some { target := 564, numerator := 1778023332660102610664030208 }, some { target := 565, numerator := 23836625303474500624214654976 }, some { target := 566, numerator := 2111402707533871850163535872 }, some { target := 567, numerator := 1778023332660102610664030208 }, some { target := 568, numerator := 2111402707533871850163535872 }, some { target := 569, numerator := 2055839478388243643580284928 }, some { target := 570, numerator := 77677394345588232803384819712 }, some { target := 571, numerator := 2055839478388243643580284928 }, some { target := 572, numerator := 23836625303474500624214654976 }, some { target := 573, numerator := 77677394345588232803384819712 }, some { target := 574, numerator := 2000276249242615436997033984 }, some { target := 575, numerator := 2055839478388243643580284928 }, some { target := 576, numerator := 2055839478388243643580284928 }, some { target := 577, numerator := 2278092394970756469913288704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 44491886498820804638146560 }, some { target := 926, numerator := 50671315179212583060111360 }, some { target := 927, numerator := 39548343554507381900574720 }, some { target := 928, numerator := 530194980777614588604579840 }, some { target := 929, numerator := 46963657970977516006932480 }, some { target := 930, numerator := 39548343554507381900574720 }, some { target := 931, numerator := 46963657970977516006932480 }, some { target := 932, numerator := 45727772234899160322539520 }, some { target := 933, numerator := 1727768259037541246781358080 }, some { target := 934, numerator := 45727772234899160322539520 }, some { target := 935, numerator := 530194980777614588604579840 }, some { target := 936, numerator := 1727768259037541246781358080 }, some { target := 937, numerator := 44491886498820804638146560 }, some { target := 938, numerator := 45727772234899160322539520 }, some { target := 939, numerator := 45727772234899160322539520 }, some { target := 940, numerator := 50671315179212583060111360 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 1, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 613, numerator := 3504109267084865620047560704 }, some { target := 616, numerator := 12798823274987973875702169600 }, some { target := 618, numerator := 3504108086493244902636257280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 880, numerator := 3504109267084865620047560704 }, some { target := 883, numerator := 12798823274987973875702169600 }, some { target := 885, numerator := 3504108086493244902636257280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 976, numerator := 3504109267084865620047560704 }, some { target := 979, numerator := 12798823274987973875702169600 }, some { target := 981, numerator := 3504108086493244902636257280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1002, numerator := 3504109267084865620047560704 }, some { target := 1005, numerator := 12798823274987973875702169600 }, some { target := 1007, numerator := 3504108086493244902636257280 }]

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

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 129, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416]⟩

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
  [some { target := 121, numerator := 42438023707810973947527168 }, some { target := 122, numerator := 636570355617164609212907520 }, some { target := 123, numerator := 1117534624305688980618215424 }, some { target := 124, numerator := 42438023707810973947527168 }, some { target := 125, numerator := 707300395130182899125452800 }, some { target := 126, numerator := 42438023707810973947527168 }, some { target := 127, numerator := 1117534624305688980618215424 }, some { target := 128, numerator := 1110461620354387151626960896 }, some { target := 129, numerator := 707300395130182899125452800 }, some { target := 130, numerator := 17137888574004331645809721344 }, some { target := 131, numerator := 1096315612451783493644451840 }, some { target := 132, numerator := 636570355617164609212907520 }, some { target := 133, numerator := 1117534624305688980618215424 }, some { target := 134, numerator := 42438023707810973947527168 }, some { target := 135, numerator := 1096315612451783493644451840 }, some { target := 136, numerator := 42438023707810973947527168 }, some { target := 137, numerator := 1117534624305688980618215424 }, some { target := 138, numerator := 1117534624305688980618215424 }, some { target := 139, numerator := 42438023707810973947527168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 7443230651345972875833114624 }, some { target := 197, numerator := 111648459770189593137496719360 }, some { target := 198, numerator := 196005073818777285730272018432 }, some { target := 199, numerator := 7443230651345972875833114624 }, some { target := 200, numerator := 124053844189099547930551910400 }, some { target := 201, numerator := 7443230651345972875833114624 }, some { target := 202, numerator := 196005073818777285730272018432 }, some { target := 203, numerator := 194764535376886290250966499328 }, some { target := 204, numerator := 124053844189099547930551910400 }, some { target := 205, numerator := 3005824644701882046357272788992 }, some { target := 206, numerator := 192283458493104299292355461120 }, some { target := 207, numerator := 111648459770189593137496719360 }, some { target := 208, numerator := 196005073818777285730272018432 }, some { target := 209, numerator := 7443230651345972875833114624 }, some { target := 210, numerator := 192283458493104299292355461120 }, some { target := 211, numerator := 7443230651345972875833114624 }, some { target := 212, numerator := 196005073818777285730272018432 }, some { target := 213, numerator := 196005073818777285730272018432 }, some { target := 214, numerator := 7443230651345972875833114624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 7443231543707217441532674048 }, some { target := 509, numerator := 111648473155608261622990110720 }, some { target := 510, numerator := 196005097317623392627027083264 }, some { target := 511, numerator := 7443231543707217441532674048 }, some { target := 512, numerator := 124053859061786957358877900800 }, some { target := 513, numerator := 7443231543707217441532674048 }, some { target := 514, numerator := 196005097317623392627027083264 }, some { target := 515, numerator := 194764558727005523053438304256 }, some { target := 516, numerator := 124053859061786957358877900800 }, some { target := 517, numerator := 3005825005067097976805611536384 }, some { target := 518, numerator := 192283481545769783906260746240 }, some { target := 519, numerator := 111648473155608261622990110720 }, some { target := 520, numerator := 196005097317623392627027083264 }, some { target := 521, numerator := 7443231543707217441532674048 }, some { target := 522, numerator := 192283481545769783906260746240 }, some { target := 523, numerator := 7443231543707217441532674048 }, some { target := 524, numerator := 196005097317623392627027083264 }, some { target := 525, numerator := 196005097317623392627027083264 }, some { target := 526, numerator := 7443231543707217441532674048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 42437131346566408247967744 }, some { target := 907, numerator := 636556970198496123719516160 }, some { target := 908, numerator := 1117511125459582083863150592 }, some { target := 909, numerator := 42437131346566408247967744 }, some { target := 910, numerator := 707285522442773470799462400 }, some { target := 911, numerator := 42437131346566408247967744 }, some { target := 912, numerator := 1117511125459582083863150592 }, some { target := 913, numerator := 1110438270235154349155155968 }, some { target := 914, numerator := 707285522442773470799462400 }, some { target := 915, numerator := 17137528208788401197470973952 }, some { target := 916, numerator := 1096292559786298879739166720 }, some { target := 917, numerator := 636556970198496123719516160 }, some { target := 918, numerator := 1117511125459582083863150592 }, some { target := 919, numerator := 42437131346566408247967744 }, some { target := 920, numerator := 1096292559786298879739166720 }, some { target := 921, numerator := 42437131346566408247967744 }, some { target := 922, numerator := 1117511125459582083863150592 }, some { target := 923, numerator := 1117511125459582083863150592 }, some { target := 924, numerator := 42437131346566408247967744 }]

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

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 29, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 217335633731309833749004288 }, some { target := 252, numerator := 8477259897413535832293244928 }, some { target := 255, numerator := 8477256787984237907626950656 }, some { target := 262, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 466, numerator := 5265130997813344682112974848 }, some { target := 468, numerator := 205368457514760174517813772288 }, some { target := 471, numerator := 205368382186327828020252901376 }, some { target := 478, numerator := 5265156107290793514633265152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 3989160503003719206554304512 }, some { target := 564, numerator := 155598738117041996405640527872 }, some { target := 567, numerator := 155598681043968753852894674944 }, some { target := 574, numerator := 3989179527361466724136255488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 597, numerator := 4444864251150014019253829632 }, some { target := 599, numerator := 173373637901941345731416686592 }, some { target := 602, numerator := 173373574309096994626951184384 }, some { target := 609, numerator := 4444885448764797720742330368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 733, numerator := 217335633731309833749004288 }, some { target := 735, numerator := 8477259897413535832293244928 }, some { target := 738, numerator := 8477256787984237907626950656 }, some { target := 745, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 829, numerator := 4444864251150014019253829632 }, some { target := 831, numerator := 173373637901941345731416686592 }, some { target := 834, numerator := 173373574309096994626951184384 }, some { target := 841, numerator := 4444885448764797720742330368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 864, numerator := 4437853424255455637519990784 }, some { target := 866, numerator := 173100177905250586511020130304 }, some { target := 869, numerator := 173100114412710406307350315008 }, some { target := 876, numerator := 4437874588435515705409929216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 217335633731309833749004288 }, some { target := 927, numerator := 8477259897413535832293244928 }, some { target := 930, numerator := 8477256787984237907626950656 }, some { target := 937, numerator := 217336670207742475304435712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 960, numerator := 5265130997813344682112974848 }, some { target := 962, numerator := 205368457514760174517813772288 }, some { target := 965, numerator := 205368382186327828020252901376 }, some { target := 972, numerator := 5265156107290793514633265152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 986, numerator := 217335633731309833749004288 }, some { target := 988, numerator := 8477259897413535832293244928 }, some { target := 991, numerator := 8477256787984237907626950656 }, some { target := 998, numerator := 217336670207742475304435712 }]

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

end Slot5

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
