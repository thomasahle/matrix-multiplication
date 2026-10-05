import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨1, 1, #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 746, numerator := 10348405015901225735484866560 }, some { target := 748, numerator := 10348405015901225735484866560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1013, numerator := 9458635612664858662901121024 }, some { target := 1015, numerator := 9458635612664858662901121024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1088, numerator := 10348405015901225735484866560 }, some { target := 1090, numerator := 10348405015901225735484866560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1102, numerator := 9458635612664858662901121024 }, some { target := 1104, numerator := 9458635612664858662901121024 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 7, #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 347, numerator := 606908573371999476672102400 }, some { target := 350, numerator := 2171175349938226042031308800 }, some { target := 352, numerator := 606908371610736170473881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 614, numerator := 12162447810374869512508932096 }, some { target := 617, numerator := 43510354012762049882307428352 }, some { target := 619, numerator := 12162443767079152856296587264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 710, numerator := 20416404408234062395249524736 }, some { target := 713, numerator := 73038338771921924053933228032 }, some { target := 715, numerator := 20416397620985164774741377024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 736, numerator := 19591008748448143106975465472 }, some { target := 739, numerator := 70085540296005936636770648064 }, some { target := 741, numerator := 19591002235594563582896898048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 881, numerator := 606908573371999476672102400 }, some { target := 884, numerator := 2171175349938226042031308800 }, some { target := 886, numerator := 606908371610736170473881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 977, numerator := 19591008748448143106975465472 }, some { target := 980, numerator := 70085540296005936636770648064 }, some { target := 982, numerator := 19591002235594563582896898048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1003, numerator := 13084948841900308717050527744 }, some { target := 1006, numerator := 46810540544668153466195017728 }, some { target := 1008, numerator := 13084944491927471835416887296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1052, numerator := 631184916306879455738986496 }, some { target := 1055, numerator := 2258022363935755083712561152 }, some { target := 1057, numerator := 631184706475165617292836864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1078, numerator := 12162447810374869512508932096 }, some { target := 1081, numerator := 43510354012762049882307428352 }, some { target := 1083, numerator := 12162443767079152856296587264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1092, numerator := 582632230437119497605218304 }, some { target := 1095, numerator := 2084328335940697000350056448 }, some { target := 1097, numerator := 582632036746306723654926336 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 27, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 142804362441978071262167040 }, some { target := 201, numerator := 169580180399848959623823360 }, some { target := 202, numerator := 129416453463042627081338880 }, some { target := 203, numerator := 1334328261567232603355873280 }, some { target := 204, numerator := 160654907747225330169937920 }, some { target := 205, numerator := 129416453463042627081338880 }, some { target := 206, numerator := 160654907747225330169937920 }, some { target := 207, numerator := 160654907747225330169937920 }, some { target := 208, numerator := 6881385215172818308945674240 }, some { target := 209, numerator := 160654907747225330169937920 }, some { target := 210, numerator := 1334328261567232603355873280 }, some { target := 211, numerator := 6881385215172818308945674240 }, some { target := 212, numerator := 142804362441978071262167040 }, some { target := 213, numerator := 160654907747225330169937920 }, some { target := 214, numerator := 160654907747225330169937920 }, some { target := 215, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 146884487083177444726800384 }, some { target := 297, numerator := 174425328411273215613075456 }, some { target := 298, numerator := 133114066419129559283662848 }, some { target := 299, numerator := 1372451926183439249166041088 }, some { target := 300, numerator := 165245047968574625317650432 }, some { target := 301, numerator := 133114066419129559283662848 }, some { target := 302, numerator := 165245047968574625317650432 }, some { target := 303, numerator := 165245047968574625317650432 }, some { target := 304, numerator := 7077996221320613117772693504 }, some { target := 305, numerator := 165245047968574625317650432 }, some { target := 306, numerator := 1372451926183439249166041088 }, some { target := 307, numerator := 7077996221320613117772693504 }, some { target := 308, numerator := 146884487083177444726800384 }, some { target := 309, numerator := 165245047968574625317650432 }, some { target := 310, numerator := 165245047968574625317650432 }, some { target := 311, numerator := 174425328411273215613075456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 142804362441978071262167040 }, some { target := 332, numerator := 169580180399848959623823360 }, some { target := 333, numerator := 129416453463042627081338880 }, some { target := 334, numerator := 1334328261567232603355873280 }, some { target := 335, numerator := 160654907747225330169937920 }, some { target := 336, numerator := 129416453463042627081338880 }, some { target := 337, numerator := 160654907747225330169937920 }, some { target := 338, numerator := 160654907747225330169937920 }, some { target := 339, numerator := 6881385215172818308945674240 }, some { target := 340, numerator := 160654907747225330169937920 }, some { target := 341, numerator := 1334328261567232603355873280 }, some { target := 342, numerator := 6881385215172818308945674240 }, some { target := 343, numerator := 142804362441978071262167040 }, some { target := 344, numerator := 160654907747225330169937920 }, some { target := 345, numerator := 160654907747225330169937920 }, some { target := 346, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 126483863877180577403633664 }, some { target := 468, numerator := 150199588354151935666814976 }, some { target := 469, numerator := 114626001638694898272043008 }, some { target := 470, numerator := 1181833603102406020115202048 }, some { target := 471, numerator := 142294346861828149579087872 }, some { target := 472, numerator := 114626001638694898272043008 }, some { target := 473, numerator := 142294346861828149579087872 }, some { target := 474, numerator := 142294346861828149579087872 }, some { target := 475, numerator := 6094941190581639073637597184 }, some { target := 476, numerator := 142294346861828149579087872 }, some { target := 477, numerator := 1181833603102406020115202048 }, some { target := 478, numerator := 6094941190581639073637597184 }, some { target := 479, numerator := 126483863877180577403633664 }, some { target := 480, numerator := 142294346861828149579087872 }, some { target := 481, numerator := 142294346861828149579087872 }, some { target := 482, numerator := 150199588354151935666814976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 5920260854380290897182982144 }, some { target := 564, numerator := 7030309764576595440404791296 }, some { target := 565, numerator := 5365236399282138625572077568 }, some { target := 566, numerator := 55317437358115843070553489408 }, some { target := 567, numerator := 6660293461177827259330854912 }, some { target := 568, numerator := 5365236399282138625572077568 }, some { target := 569, numerator := 6660293461177827259330854912 }, some { target := 570, numerator := 6660293461177827259330854912 }, some { target := 571, numerator := 285282569920450267608004952064 }, some { target := 572, numerator := 6660293461177827259330854912 }, some { target := 573, numerator := 55317437358115843070553489408 }, some { target := 574, numerator := 285282569920450267608004952064 }, some { target := 575, numerator := 5920260854380290897182982144 }, some { target := 576, numerator := 6660293461177827259330854912 }, some { target := 577, numerator := 6660293461177827259330854912 }, some { target := 578, numerator := 7030309764576595440404791296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 1611649233273752518530170880 }, some { target := 599, numerator := 1913833464512581115754577920 }, some { target := 600, numerator := 1460557117654338219917967360 }, some { target := 601, numerator := 15058847523401625095016284160 }, some { target := 602, numerator := 1813105387432971583346442240 }, some { target := 603, numerator := 1460557117654338219917967360 }, some { target := 604, numerator := 1813105387432971583346442240 }, some { target := 605, numerator := 1813105387432971583346442240 }, some { target := 606, numerator := 77661347428378949486672609280 }, some { target := 607, numerator := 1813105387432971583346442240 }, some { target := 608, numerator := 15058847523401625095016284160 }, some { target := 609, numerator := 77661347428378949486672609280 }, some { target := 610, numerator := 1611649233273752518530170880 }, some { target := 611, numerator := 1813105387432971583346442240 }, some { target := 612, numerator := 1813105387432971583346442240 }, some { target := 613, numerator := 1913833464512581115754577920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 146884487083177444726800384 }, some { target := 660, numerator := 174425328411273215613075456 }, some { target := 661, numerator := 133114066419129559283662848 }, some { target := 662, numerator := 1372451926183439249166041088 }, some { target := 663, numerator := 165245047968574625317650432 }, some { target := 664, numerator := 133114066419129559283662848 }, some { target := 665, numerator := 165245047968574625317650432 }, some { target := 666, numerator := 165245047968574625317650432 }, some { target := 667, numerator := 7077996221320613117772693504 }, some { target := 668, numerator := 165245047968574625317650432 }, some { target := 669, numerator := 1372451926183439249166041088 }, some { target := 670, numerator := 7077996221320613117772693504 }, some { target := 671, numerator := 146884487083177444726800384 }, some { target := 672, numerator := 165245047968574625317650432 }, some { target := 673, numerator := 165245047968574625317650432 }, some { target := 674, numerator := 174425328411273215613075456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 5920260854380290897182982144 }, some { target := 695, numerator := 7030309764576595440404791296 }, some { target := 696, numerator := 5365236399282138625572077568 }, some { target := 697, numerator := 55317437358115843070553489408 }, some { target := 698, numerator := 6660293461177827259330854912 }, some { target := 699, numerator := 5365236399282138625572077568 }, some { target := 700, numerator := 6660293461177827259330854912 }, some { target := 701, numerator := 6660293461177827259330854912 }, some { target := 702, numerator := 285282569920450267608004952064 }, some { target := 703, numerator := 6660293461177827259330854912 }, some { target := 704, numerator := 55317437358115843070553489408 }, some { target := 705, numerator := 285282569920450267608004952064 }, some { target := 706, numerator := 5920260854380290897182982144 }, some { target := 707, numerator := 6660293461177827259330854912 }, some { target := 708, numerator := 6660293461177827259330854912 }, some { target := 709, numerator := 7030309764576595440404791296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 142804362441978071262167040 }, some { target := 721, numerator := 169580180399848959623823360 }, some { target := 722, numerator := 129416453463042627081338880 }, some { target := 723, numerator := 1334328261567232603355873280 }, some { target := 724, numerator := 160654907747225330169937920 }, some { target := 725, numerator := 129416453463042627081338880 }, some { target := 726, numerator := 160654907747225330169937920 }, some { target := 727, numerator := 160654907747225330169937920 }, some { target := 728, numerator := 6881385215172818308945674240 }, some { target := 729, numerator := 160654907747225330169937920 }, some { target := 730, numerator := 1334328261567232603355873280 }, some { target := 731, numerator := 6881385215172818308945674240 }, some { target := 732, numerator := 142804362441978071262167040 }, some { target := 733, numerator := 160654907747225330169937920 }, some { target := 734, numerator := 160654907747225330169937920 }, some { target := 735, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 142804362441978071262167040 }, some { target := 831, numerator := 169580180399848959623823360 }, some { target := 832, numerator := 129416453463042627081338880 }, some { target := 833, numerator := 1334328261567232603355873280 }, some { target := 834, numerator := 160654907747225330169937920 }, some { target := 835, numerator := 129416453463042627081338880 }, some { target := 836, numerator := 160654907747225330169937920 }, some { target := 837, numerator := 160654907747225330169937920 }, some { target := 838, numerator := 6881385215172818308945674240 }, some { target := 839, numerator := 160654907747225330169937920 }, some { target := 840, numerator := 1334328261567232603355873280 }, some { target := 841, numerator := 6881385215172818308945674240 }, some { target := 842, numerator := 142804362441978071262167040 }, some { target := 843, numerator := 160654907747225330169937920 }, some { target := 844, numerator := 160654907747225330169937920 }, some { target := 845, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 122403739235981203939000320 }, some { target := 866, numerator := 145354440342727679677562880 }, some { target := 867, numerator := 110928388682607966069719040 }, some { target := 868, numerator := 1143709938486199374305034240 }, some { target := 869, numerator := 137704206640478854431375360 }, some { target := 870, numerator := 110928388682607966069719040 }, some { target := 871, numerator := 137704206640478854431375360 }, some { target := 872, numerator := 137704206640478854431375360 }, some { target := 873, numerator := 5898330184433844264810577920 }, some { target := 874, numerator := 137704206640478854431375360 }, some { target := 875, numerator := 1143709938486199374305034240 }, some { target := 876, numerator := 5898330184433844264810577920 }, some { target := 877, numerator := 122403739235981203939000320 }, some { target := 878, numerator := 137704206640478854431375360 }, some { target := 879, numerator := 137704206640478854431375360 }, some { target := 880, numerator := 145354440342727679677562880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 142804362441978071262167040 }, some { target := 927, numerator := 169580180399848959623823360 }, some { target := 928, numerator := 129416453463042627081338880 }, some { target := 929, numerator := 1334328261567232603355873280 }, some { target := 930, numerator := 160654907747225330169937920 }, some { target := 931, numerator := 129416453463042627081338880 }, some { target := 932, numerator := 160654907747225330169937920 }, some { target := 933, numerator := 160654907747225330169937920 }, some { target := 934, numerator := 6881385215172818308945674240 }, some { target := 935, numerator := 160654907747225330169937920 }, some { target := 936, numerator := 1334328261567232603355873280 }, some { target := 937, numerator := 6881385215172818308945674240 }, some { target := 938, numerator := 142804362441978071262167040 }, some { target := 939, numerator := 160654907747225330169937920 }, some { target := 940, numerator := 160654907747225330169937920 }, some { target := 941, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 1611649233273752518530170880 }, some { target := 962, numerator := 1913833464512581115754577920 }, some { target := 963, numerator := 1460557117654338219917967360 }, some { target := 964, numerator := 15058847523401625095016284160 }, some { target := 965, numerator := 1813105387432971583346442240 }, some { target := 966, numerator := 1460557117654338219917967360 }, some { target := 967, numerator := 1813105387432971583346442240 }, some { target := 968, numerator := 1813105387432971583346442240 }, some { target := 969, numerator := 77661347428378949486672609280 }, some { target := 970, numerator := 1813105387432971583346442240 }, some { target := 971, numerator := 15058847523401625095016284160 }, some { target := 972, numerator := 77661347428378949486672609280 }, some { target := 973, numerator := 1611649233273752518530170880 }, some { target := 974, numerator := 1813105387432971583346442240 }, some { target := 975, numerator := 1813105387432971583346442240 }, some { target := 976, numerator := 1913833464512581115754577920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 122403739235981203939000320 }, some { target := 988, numerator := 145354440342727679677562880 }, some { target := 989, numerator := 110928388682607966069719040 }, some { target := 990, numerator := 1143709938486199374305034240 }, some { target := 991, numerator := 137704206640478854431375360 }, some { target := 992, numerator := 110928388682607966069719040 }, some { target := 993, numerator := 137704206640478854431375360 }, some { target := 994, numerator := 137704206640478854431375360 }, some { target := 995, numerator := 5898330184433844264810577920 }, some { target := 996, numerator := 137704206640478854431375360 }, some { target := 997, numerator := 1143709938486199374305034240 }, some { target := 998, numerator := 5898330184433844264810577920 }, some { target := 999, numerator := 122403739235981203939000320 }, some { target := 1000, numerator := 137704206640478854431375360 }, some { target := 1001, numerator := 137704206640478854431375360 }, some { target := 1002, numerator := 145354440342727679677562880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 142804362441978071262167040 }, some { target := 1037, numerator := 169580180399848959623823360 }, some { target := 1038, numerator := 129416453463042627081338880 }, some { target := 1039, numerator := 1334328261567232603355873280 }, some { target := 1040, numerator := 160654907747225330169937920 }, some { target := 1041, numerator := 129416453463042627081338880 }, some { target := 1042, numerator := 160654907747225330169937920 }, some { target := 1043, numerator := 160654907747225330169937920 }, some { target := 1044, numerator := 6881385215172818308945674240 }, some { target := 1045, numerator := 160654907747225330169937920 }, some { target := 1046, numerator := 1334328261567232603355873280 }, some { target := 1047, numerator := 6881385215172818308945674240 }, some { target := 1048, numerator := 142804362441978071262167040 }, some { target := 1049, numerator := 160654907747225330169937920 }, some { target := 1050, numerator := 160654907747225330169937920 }, some { target := 1051, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 126483863877180577403633664 }, some { target := 1063, numerator := 150199588354151935666814976 }, some { target := 1064, numerator := 114626001638694898272043008 }, some { target := 1065, numerator := 1181833603102406020115202048 }, some { target := 1066, numerator := 142294346861828149579087872 }, some { target := 1067, numerator := 114626001638694898272043008 }, some { target := 1068, numerator := 142294346861828149579087872 }, some { target := 1069, numerator := 142294346861828149579087872 }, some { target := 1070, numerator := 6094941190581639073637597184 }, some { target := 1071, numerator := 142294346861828149579087872 }, some { target := 1072, numerator := 1181833603102406020115202048 }, some { target := 1073, numerator := 6094941190581639073637597184 }, some { target := 1074, numerator := 126483863877180577403633664 }, some { target := 1075, numerator := 142294346861828149579087872 }, some { target := 1076, numerator := 142294346861828149579087872 }, some { target := 1077, numerator := 150199588354151935666814976 }]

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

end Slot3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2
