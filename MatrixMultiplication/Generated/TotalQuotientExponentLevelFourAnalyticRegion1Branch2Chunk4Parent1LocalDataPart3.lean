import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 49, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 267332834553857288775401472 }, some { target := 201, numerator := 261763400500651928592580608 }, some { target := 202, numerator := 206069059968598326764371968 }, some { target := 203, numerator := 6477251803877833892620664832 }, some { target := 204, numerator := 206069059968598326764371968 }, some { target := 205, numerator := 206069059968598326764371968 }, some { target := 206, numerator := 211638494021803686947192832 }, some { target := 207, numerator := 211638494021803686947192832 }, some { target := 208, numerator := 3581146096211046597553815552 }, some { target := 209, numerator := 194930191862187606398730240 }, some { target := 210, numerator := 6477251803877833892620664832 }, some { target := 211, numerator := 3581146096211046597553815552 }, some { target := 212, numerator := 267332834553857288775401472 }, some { target := 213, numerator := 206069059968598326764371968 }, some { target := 214, numerator := 194930191862187606398730240 }, some { target := 215, numerator := 261763400500651928592580608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 22479815387315005262496006144 }, some { target := 297, numerator := 22011485900079275986194006016 }, some { target := 298, numerator := 17328191027721983223174004736 }, some { target := 299, numerator := 544667193655153148339226148864 }, some { target := 300, numerator := 17328191027721983223174004736 }, some { target := 301, numerator := 17328191027721983223174004736 }, some { target := 302, numerator := 17796520514957712499476004864 }, some { target := 303, numerator := 17796520514957712499476004864 }, some { target := 304, numerator := 301135860292573924662186082304 }, some { target := 305, numerator := 16391532053250524670570004480 }, some { target := 306, numerator := 544667193655153148339226148864 }, some { target := 307, numerator := 301135860292573924662186082304 }, some { target := 308, numerator := 22479815387315005262496006144 }, some { target := 309, numerator := 17328191027721983223174004736 }, some { target := 310, numerator := 16391532053250524670570004480 }, some { target := 311, numerator := 22011485900079275986194006016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 22479809963972247591887831040 }, some { target := 660, numerator := 22011480589722825767056834560 }, some { target := 661, numerator := 17328186847228607518746869760 }, some { target := 662, numerator := 544667062252077582278448906240 }, some { target := 663, numerator := 17328186847228607518746869760 }, some { target := 664, numerator := 17328186847228607518746869760 }, some { target := 665, numerator := 17796516221478029343577866240 }, some { target := 666, numerator := 17796516221478029343577866240 }, some { target := 667, numerator := 301135787642378233366330736640 }, some { target := 668, numerator := 16391528098729763869084876800 }, some { target := 669, numerator := 544667062252077582278448906240 }, some { target := 670, numerator := 301135787642378233366330736640 }, some { target := 671, numerator := 22479809963972247591887831040 }, some { target := 672, numerator := 17328186847228607518746869760 }, some { target := 673, numerator := 16391528098729763869084876800 }, some { target := 674, numerator := 22011480589722825767056834560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 267338257896614959383576576 }, some { target := 1037, numerator := 261768710857102147729752064 }, some { target := 1038, numerator := 206073240461974031191506944 }, some { target := 1039, numerator := 6477383206953399953397907456 }, some { target := 1040, numerator := 206073240461974031191506944 }, some { target := 1041, numerator := 206073240461974031191506944 }, some { target := 1042, numerator := 211642787501486842845331456 }, some { target := 1043, numerator := 211642787501486842845331456 }, some { target := 1044, numerator := 3581218746406737893409161216 }, some { target := 1045, numerator := 194934146382948407883857920 }, some { target := 1046, numerator := 6477383206953399953397907456 }, some { target := 1047, numerator := 3581218746406737893409161216 }, some { target := 1048, numerator := 267338257896614959383576576 }, some { target := 1049, numerator := 206073240461974031191506944 }, some { target := 1050, numerator := 194934146382948407883857920 }, some { target := 1051, numerator := 261768710857102147729752064 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 898, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 71, numerator := 56739869704349330222088192 }, some { target := 72, numerator := 1513063192115982139255685120 }, some { target := 73, numerator := 1446866677460907920663248896 }, some { target := 74, numerator := 47283224753624441851740160 }, some { target := 75, numerator := 1484693257263807474144641024 }, some { target := 76, numerator := 47283224753624441851740160 }, some { target := 77, numerator := 1446866677460907920663248896 }, some { target := 78, numerator := 822728110713065288220278784 }, some { target := 79, numerator := 1484693257263807474144641024 }, some { target := 80, numerator := 23178236774226701395723026432 }, some { target := 81, numerator := 907837915269589283553411072 }, some { target := 82, numerator := 1513063192115982139255685120 }, some { target := 83, numerator := 1446866677460907920663248896 }, some { target := 84, numerator := 47283224753624441851740160 }, some { target := 85, numerator := 907837915269589283553411072 }, some { target := 86, numerator := 47283224753624441851740160 }, some { target := 87, numerator := 1456323322411632809033596928 }, some { target := 88, numerator := 822728110713065288220278784 }, some { target := 89, numerator := 56739869704349330222088192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 8380181824549401996948406272 }, some { target := 147, numerator := 223471515321317386585290833920 }, some { target := 148, numerator := 213694636526009750922184359936 }, some { target := 149, numerator := 6983484853791168330790338560 }, some { target := 150, numerator := 219281424409042685586816630784 }, some { target := 151, numerator := 6983484853791168330790338560 }, some { target := 152, numerator := 213694636526009750922184359936 }, some { target := 153, numerator := 121512636455966328955751890944 }, some { target := 154, numerator := 219281424409042685586816630784 }, some { target := 155, numerator := 3423304275328430715753423962112 }, some { target := 156, numerator := 134082909192790431951174500352 }, some { target := 157, numerator := 223471515321317386585290833920 }, some { target := 158, numerator := 213694636526009750922184359936 }, some { target := 159, numerator := 6983484853791168330790338560 }, some { target := 160, numerator := 134082909192790431951174500352 }, some { target := 161, numerator := 6983484853791168330790338560 }, some { target := 162, numerator := 215091333496767984588342427648 }, some { target := 163, numerator := 121512636455966328955751890944 }, some { target := 164, numerator := 8380181824549401996948406272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 87345233668830449238729031680 }, some { target := 243, numerator := 2329206231168811979699440844800 }, some { target := 244, numerator := 2227303458555176455587590307840 }, some { target := 245, numerator := 72787694724025374365607526400 }, some { target := 246, numerator := 2285533614334396755080076328960 }, some { target := 247, numerator := 72787694724025374365607526400 }, some { target := 248, numerator := 2227303458555176455587590307840 }, some { target := 249, numerator := 1266505888198041513961570959360 }, some { target := 250, numerator := 2285533614334396755080076328960 }, some { target := 251, numerator := 35680527953717238514020809441280 }, some { target := 252, numerator := 1397523738701287187819664506880 }, some { target := 253, numerator := 2329206231168811979699440844800 }, some { target := 254, numerator := 2227303458555176455587590307840 }, some { target := 255, numerator := 72787694724025374365607526400 }, some { target := 256, numerator := 1397523738701287187819664506880 }, some { target := 257, numerator := 72787694724025374365607526400 }, some { target := 258, numerator := 2241860997499981530460711813120 }, some { target := 259, numerator := 1266505888198041513961570959360 }, some { target := 260, numerator := 87345233668830449238729031680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 8380181824549401996948406272 }, some { target := 641, numerator := 223471515321317386585290833920 }, some { target := 642, numerator := 213694636526009750922184359936 }, some { target := 643, numerator := 6983484853791168330790338560 }, some { target := 644, numerator := 219281424409042685586816630784 }, some { target := 645, numerator := 6983484853791168330790338560 }, some { target := 646, numerator := 213694636526009750922184359936 }, some { target := 647, numerator := 121512636455966328955751890944 }, some { target := 648, numerator := 219281424409042685586816630784 }, some { target := 649, numerator := 3423304275328430715753423962112 }, some { target := 650, numerator := 134082909192790431951174500352 }, some { target := 651, numerator := 223471515321317386585290833920 }, some { target := 652, numerator := 213694636526009750922184359936 }, some { target := 653, numerator := 6983484853791168330790338560 }, some { target := 654, numerator := 134082909192790431951174500352 }, some { target := 655, numerator := 6983484853791168330790338560 }, some { target := 656, numerator := 215091333496767984588342427648 }, some { target := 657, numerator := 121512636455966328955751890944 }, some { target := 658, numerator := 8380181824549401996948406272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 56739869704349330222088192 }, some { target := 1018, numerator := 1513063192115982139255685120 }, some { target := 1019, numerator := 1446866677460907920663248896 }, some { target := 1020, numerator := 47283224753624441851740160 }, some { target := 1021, numerator := 1484693257263807474144641024 }, some { target := 1022, numerator := 47283224753624441851740160 }, some { target := 1023, numerator := 1446866677460907920663248896 }, some { target := 1024, numerator := 822728110713065288220278784 }, some { target := 1025, numerator := 1484693257263807474144641024 }, some { target := 1026, numerator := 23178236774226701395723026432 }, some { target := 1027, numerator := 907837915269589283553411072 }, some { target := 1028, numerator := 1513063192115982139255685120 }, some { target := 1029, numerator := 1446866677460907920663248896 }, some { target := 1030, numerator := 47283224753624441851740160 }, some { target := 1031, numerator := 907837915269589283553411072 }, some { target := 1032, numerator := 47283224753624441851740160 }, some { target := 1033, numerator := 1456323322411632809033596928 }, some { target := 1034, numerator := 822728110713065288220278784 }, some { target := 1035, numerator := 56739869704349330222088192 }]

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

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 790, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 7180773750113555855074918400 }, some { target := 30, numerator := 7385938714402514593791344640 }, some { target := 31, numerator := 7180773750113555855074918400 }, some { target := 32, numerator := 6360113892957720900209213440 }, some { target := 33, numerator := 297694363183279129877534474240 }, some { target := 34, numerator := 81040160894138701792988364800 }, some { target := 35, numerator := 7385938714402514593791344640 }, some { target := 36, numerator := 297694363183279129877534474240 }, some { target := 37, numerator := 7180773750113555855074918400 }, some { target := 38, numerator := 7180773750113555855074918400 }, some { target := 39, numerator := 6154948928668762161492787200 }, some { target := 40, numerator := 7180773750113555855074918400 }, some { target := 41, numerator := 81040160894138701792988364800 }, some { target := 42, numerator := 6154948928668762161492787200 }, some { target := 43, numerator := 7180773750113555855074918400 }, some { target := 44, numerator := 6360113892957720900209213440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 260233617548642417589931212800 }, some { target := 105, numerator := 267668863764317915235357818880 }, some { target := 106, numerator := 260233617548642417589931212800 }, some { target := 107, numerator := 230492632685940427008224788480 }, some { target := 108, numerator := 10788542258945147083514005422080 }, some { target := 109, numerator := 2936922255191821569943509401600 }, some { target := 110, numerator := 267668863764317915235357818880 }, some { target := 111, numerator := 10788542258945147083514005422080 }, some { target := 112, numerator := 260233617548642417589931212800 }, some { target := 113, numerator := 260233617548642417589931212800 }, some { target := 114, numerator := 223057386470264929362798182400 }, some { target := 115, numerator := 260233617548642417589931212800 }, some { target := 116, numerator := 2936922255191821569943509401600 }, some { target := 117, numerator := 223057386470264929362798182400 }, some { target := 118, numerator := 260233617548642417589931212800 }, some { target := 119, numerator := 230492632685940427008224788480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 260233713183481224727887872000 }, some { target := 227, numerator := 267668962131580688291541811200 }, some { target := 228, numerator := 260233713183481224727887872000 }, some { target := 229, numerator := 230492717391083370473272115200 }, some { target := 230, numerator := 10788546223692321630861865779200 }, some { target := 231, numerator := 2936923334499288107643305984000 }, some { target := 232, numerator := 267668962131580688291541811200 }, some { target := 233, numerator := 10788546223692321630861865779200 }, some { target := 234, numerator := 260233713183481224727887872000 }, some { target := 235, numerator := 260233713183481224727887872000 }, some { target := 236, numerator := 223057468442983906909618176000 }, some { target := 237, numerator := 260233713183481224727887872000 }, some { target := 238, numerator := 2936923334499288107643305984000 }, some { target := 239, numerator := 223057468442983906909618176000 }, some { target := 240, numerator := 260233713183481224727887872000 }, some { target := 241, numerator := 230492717391083370473272115200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 7180678115274748717118259200 }, some { target := 625, numerator := 7385840347139741537607352320 }, some { target := 626, numerator := 7180678115274748717118259200 }, some { target := 627, numerator := 6360029187814777435161886720 }, some { target := 628, numerator := 297690398436104582529674117120 }, some { target := 629, numerator := 81039081586672164093191782400 }, some { target := 630, numerator := 7385840347139741537607352320 }, some { target := 631, numerator := 297690398436104582529674117120 }, some { target := 632, numerator := 7180678115274748717118259200 }, some { target := 633, numerator := 7180678115274748717118259200 }, some { target := 634, numerator := 6154866955949784614672793600 }, some { target := 635, numerator := 7180678115274748717118259200 }, some { target := 636, numerator := 81039081586672164093191782400 }, some { target := 637, numerator := 6154866955949784614672793600 }, some { target := 638, numerator := 7180678115274748717118259200 }, some { target := 639, numerator := 6360029187814777435161886720 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 44, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 5, numerator := 3947710684058073403962163200 }, some { target := 6, numerator := 79112122108523791015401750528 }, some { target := 7, numerator := 132800987411713589309287170048 }, some { target := 8, numerator := 127432100881394609479898628096 }, some { target := 9, numerator := 3947710684058073403962163200 }, some { target := 10, numerator := 127432100881394609479898628096 }, some { target := 11, numerator := 85112642348292062589424238592 }, some { target := 12, numerator := 4105619111420396340120649728 }, some { target := 13, numerator := 79112122108523791015401750528 }, some { target := 14, numerator := 3789802256695750467803676672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 13381673057101326666904371200 }, some { target := 95, numerator := 268168728064310586404763598848 }, some { target := 96, numerator := 450159481640888629074663047168 }, some { target := 97, numerator := 431960406283230824807673102336 }, some { target := 98, numerator := 13381673057101326666904371200 }, some { target := 99, numerator := 431960406283230824807673102336 }, some { target := 100, numerator := 288508871111104602938458243072 }, some { target := 101, numerator := 13916939979385379733580546048 }, some { target := 102, numerator := 268168728064310586404763598848 }, some { target := 103, numerator := 12846406134817273600228196352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 3947710684058073403962163200 }, some { target := 217, numerator := 79112122108523791015401750528 }, some { target := 218, numerator := 132800987411713589309287170048 }, some { target := 219, numerator := 127432100881394609479898628096 }, some { target := 220, numerator := 3947710684058073403962163200 }, some { target := 221, numerator := 127432100881394609479898628096 }, some { target := 222, numerator := 85112642348292062589424238592 }, some { target := 223, numerator := 4105619111420396340120649728 }, some { target := 224, numerator := 79112122108523791015401750528 }, some { target := 225, numerator := 3789802256695750467803676672 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 10348405015901225735484866560 }, some { target := 2, numerator := 9458635612664858662901121024 }, some { target := 3, numerator := 10348405015901225735484866560 }, some { target := 4, numerator := 9458635612664858662901121024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 10348405015901225735484866560 }, some { target := 91, numerator := 9458635612664858662901121024 }, some { target := 92, numerator := 10348405015901225735484866560 }, some { target := 93, numerator := 9458635612664858662901121024 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot20

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent1
