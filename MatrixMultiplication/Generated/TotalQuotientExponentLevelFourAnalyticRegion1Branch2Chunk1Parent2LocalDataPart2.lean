import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 6, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 257, numerator := 21230968802829764583751680 }, some { target := 258, numerator := 520501170650020034956492800 }, some { target := 259, numerator := 21230968802829764583751680 }, some { target := 260, numerator := 436262165400082581930639360 }, some { target := 261, numerator := 428728595824884923529953280 }, some { target := 262, numerator := 21230968802829764583751680 }, some { target := 263, numerator := 429413465786266528839106560 }, some { target := 264, numerator := 384896918296462183744143360 }, some { target := 265, numerator := 520501170650020034956492800 }, some { target := 266, numerator := 21230968802829764583751680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 1777650650783738447379038208 }, some { target := 354, numerator := 43581112728891652258324807680 }, some { target := 355, numerator := 1777650650783738447379038208 }, some { target := 356, numerator := 36527853695136819063885398016 }, some { target := 357, numerator := 35897074431955492518041223168 }, some { target := 358, numerator := 1777650650783738447379038208 }, some { target := 359, numerator := 35954418001335613113117966336 }, some { target := 360, numerator := 32227085991627774433129660416 }, some { target := 361, numerator := 43581112728891652258324807680 }, some { target := 362, numerator := 1777650650783738447379038208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 1777651294113938017999650816 }, some { target := 696, numerator := 43581128500857835279991439360 }, some { target := 697, numerator := 1777651294113938017999650816 }, some { target := 698, numerator := 36527866914534790885992824832 }, some { target := 699, numerator := 35897087423075006427992948736 }, some { target := 700, numerator := 1777651294113938017999650816 }, some { target := 701, numerator := 35954431013207714105992937472 }, some { target := 702, numerator := 32227097654581715035993669632 }, some { target := 703, numerator := 43581128500857835279991439360 }, some { target := 704, numerator := 1777651294113938017999650816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 21230325472630193963139072 }, some { target := 983, numerator := 520485398683837013289861120 }, some { target := 984, numerator := 21230325472630193963139072 }, some { target := 985, numerator := 436248946002110759823212544 }, some { target := 986, numerator := 428715604705371013578227712 }, some { target := 987, numerator := 21230325472630193963139072 }, some { target := 988, numerator := 429400453914165535964135424 }, some { target := 989, numerator := 384885255342521580880134144 }, some { target := 990, numerator := 520485398683837013289861120 }, some { target := 991, numerator := 21230325472630193963139072 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 222, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 153606001008291288887328768 }, some { target := 111, numerator := 150405875987285220368842752 }, some { target := 112, numerator := 118404625777224535183982592 }, some { target := 113, numerator := 3721745399430057686999236608 }, some { target := 114, numerator := 118404625777224535183982592 }, some { target := 115, numerator := 118404625777224535183982592 }, some { target := 116, numerator := 121604750798230603702468608 }, some { target := 117, numerator := 121604750798230603702468608 }, some { target := 118, numerator := 2057680388506902057386508288 }, some { target := 119, numerator := 112004375735212398147010560 }, some { target := 120, numerator := 3721745399430057686999236608 }, some { target := 121, numerator := 2057680388506902057386508288 }, some { target := 122, numerator := 153606001008291288887328768 }, some { target := 123, numerator := 118404625777224535183982592 }, some { target := 124, numerator := 112004375735212398147010560 }, some { target := 125, numerator := 150405875987285220368842752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 16105312166982819447677386752 }, some { target := 207, numerator := 15769784830170677375850774528 }, some { target := 208, numerator := 12414511462049256657584652288 }, some { target := 209, numerator := 390218292712521229534350016512 }, some { target := 210, numerator := 12414511462049256657584652288 }, some { target := 211, numerator := 12414511462049256657584652288 }, some { target := 212, numerator := 12750038798861398729411264512 }, some { target := 213, numerator := 12750038798861398729411264512 }, some { target := 214, numerator := 215744077570207352184511660032 }, some { target := 215, numerator := 11743456788424972513931427840 }, some { target := 216, numerator := 390218292712521229534350016512 }, some { target := 217, numerator := 215744077570207352184511660032 }, some { target := 218, numerator := 16105312166982819447677386752 }, some { target := 219, numerator := 12414511462049256657584652288 }, some { target := 220, numerator := 11743456788424972513931427840 }, some { target := 221, numerator := 15769784830170677375850774528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 173599167919502041207013376000 }, some { target := 303, numerator := 169982518587845748681867264000 }, some { target := 304, numerator := 133816025271282823430406144000 }, some { target := 305, numerator := 4206163172716268206744928256000 }, some { target := 306, numerator := 133816025271282823430406144000 }, some { target := 307, numerator := 133816025271282823430406144000 }, some { target := 308, numerator := 137432674602939115955552256000 }, some { target := 309, numerator := 137432674602939115955552256000 }, some { target := 310, numerator := 2325505520254996093668950016000 }, some { target := 311, numerator := 126582726607970238380113920000 }, some { target := 312, numerator := 4206163172716268206744928256000 }, some { target := 313, numerator := 2325505520254996093668950016000 }, some { target := 314, numerator := 173599167919502041207013376000 }, some { target := 315, numerator := 133816025271282823430406144000 }, some { target := 316, numerator := 126582726607970238380113920000 }, some { target := 317, numerator := 169982518587845748681867264000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 16105324452514372538238763008 }, some { target := 680, numerator := 15769796859753656443692122112 }, some { target := 681, numerator := 12414520932146495498225713152 }, some { target := 682, numerator := 390218590380712817957743362048 }, some { target := 683, numerator := 12414520932146495498225713152 }, some { target := 684, numerator := 12414520932146495498225713152 }, some { target := 685, numerator := 12750048524907211592772354048 }, some { target := 686, numerator := 12750048524907211592772354048 }, some { target := 687, numerator := 215744242145140448793490096128 }, some { target := 688, numerator := 11743465746625063309132431360 }, some { target := 689, numerator := 390218590380712817957743362048 }, some { target := 690, numerator := 215744242145140448793490096128 }, some { target := 691, numerator := 16105324452514372538238763008 }, some { target := 692, numerator := 12414520932146495498225713152 }, some { target := 693, numerator := 11743465746625063309132431360 }, some { target := 694, numerator := 15769796859753656443692122112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 153606001008291288887328768 }, some { target := 967, numerator := 150405875987285220368842752 }, some { target := 968, numerator := 118404625777224535183982592 }, some { target := 969, numerator := 3721745399430057686999236608 }, some { target := 970, numerator := 118404625777224535183982592 }, some { target := 971, numerator := 118404625777224535183982592 }, some { target := 972, numerator := 121604750798230603702468608 }, some { target := 973, numerator := 121604750798230603702468608 }, some { target := 974, numerator := 2057680388506902057386508288 }, some { target := 975, numerator := 112004375735212398147010560 }, some { target := 976, numerator := 3721745399430057686999236608 }, some { target := 977, numerator := 2057680388506902057386508288 }, some { target := 978, numerator := 153606001008291288887328768 }, some { target := 979, numerator := 118404625777224535183982592 }, some { target := 980, numerator := 112004375735212398147010560 }, some { target := 981, numerator := 150405875987285220368842752 }]

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

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 574, #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 925295199049615146957668352 }, some { target := 57, numerator := 24674538641323070585537822720 }, some { target := 58, numerator := 23595027575765186247420542976 }, some { target := 59, numerator := 771079332541345955798056960 }, some { target := 60, numerator := 24211891041798263012058988544 }, some { target := 61, numerator := 771079332541345955798056960 }, some { target := 62, numerator := 23595027575765186247420542976 }, some { target := 63, numerator := 13416780386219419630886191104 }, some { target := 64, numerator := 24211891041798263012058988544 }, some { target := 65, numerator := 377983088811767787532207521792 }, some { target := 66, numerator := 14804723184793842351322693632 }, some { target := 67, numerator := 24674538641323070585537822720 }, some { target := 68, numerator := 23595027575765186247420542976 }, some { target := 69, numerator := 771079332541345955798056960 }, some { target := 70, numerator := 14804723184793842351322693632 }, some { target := 71, numerator := 771079332541345955798056960 }, some { target := 72, numerator := 23749243442273455438580154368 }, some { target := 73, numerator := 13416780386219419630886191104 }, some { target := 74, numerator := 925295199049615146957668352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 32383025012310986008565907456 }, some { target := 153, numerator := 863547333661626293561757532160 }, some { target := 154, numerator := 825767137813930143218430640128 }, some { target := 155, numerator := 26985854176925821673804922880 }, some { target := 156, numerator := 847355821155470800557474578432 }, some { target := 157, numerator := 26985854176925821673804922880 }, some { target := 158, numerator := 825767137813930143218430640128 }, some { target := 159, numerator := 469553862678509297124205658112 }, some { target := 160, numerator := 847355821155470800557474578432 }, some { target := 161, numerator := 13228465717529037784499173195776 }, some { target := 162, numerator := 518128400196975776137054519296 }, some { target := 163, numerator := 863547333661626293561757532160 }, some { target := 164, numerator := 825767137813930143218430640128 }, some { target := 165, numerator := 26985854176925821673804922880 }, some { target := 166, numerator := 518128400196975776137054519296 }, some { target := 167, numerator := 26985854176925821673804922880 }, some { target := 168, numerator := 831164308649315307553191624704 }, some { target := 169, numerator := 469553862678509297124205658112 }, some { target := 170, numerator := 32383025012310986008565907456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 32383040894957633472489848832 }, some { target := 284, numerator := 863547757198870225933062635520 }, some { target := 285, numerator := 825767542821419653548491145216 }, some { target := 286, numerator := 26985867412464694560408207360 }, some { target := 287, numerator := 847356236751391409196817711104 }, some { target := 288, numerator := 26985867412464694560408207360 }, some { target := 289, numerator := 825767542821419653548491145216 }, some { target := 290, numerator := 469554092976885685351102808064 }, some { target := 291, numerator := 847356236751391409196817711104 }, some { target := 292, numerator := 13228472205590193273512103247872 }, some { target := 293, numerator := 518128654319322135559837581312 }, some { target := 294, numerator := 863547757198870225933062635520 }, some { target := 295, numerator := 825767542821419653548491145216 }, some { target := 296, numerator := 26985867412464694560408207360 }, some { target := 297, numerator := 518128654319322135559837581312 }, some { target := 298, numerator := 26985867412464694560408207360 }, some { target := 299, numerator := 831164716303912592460572786688 }, some { target := 300, numerator := 469554092976885685351102808064 }, some { target := 301, numerator := 32383040894957633472489848832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 925287257726291414995697664 }, some { target := 661, numerator := 24674326872701104399885271040 }, some { target := 662, numerator := 23594825072020431082390290432 }, some { target := 663, numerator := 771072714771909512496414720 }, some { target := 664, numerator := 24211683243837958692387422208 }, some { target := 665, numerator := 771072714771909512496414720 }, some { target := 666, numerator := 23594825072020431082390290432 }, some { target := 667, numerator := 13416665237031225517437616128 }, some { target := 668, numerator := 24211683243837958692387422208 }, some { target := 669, numerator := 377979844781190043025742495744 }, some { target := 670, numerator := 14804596123620662639931162624 }, some { target := 671, numerator := 24674326872701104399885271040 }, some { target := 672, numerator := 23594825072020431082390290432 }, some { target := 673, numerator := 771072714771909512496414720 }, some { target := 674, numerator := 14804596123620662639931162624 }, some { target := 675, numerator := 771072714771909512496414720 }, some { target := 676, numerator := 23749039614974812984889573376 }, some { target := 677, numerator := 13416665237031225517437616128 }, some { target := 678, numerator := 925287257726291414995697664 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 52, #[51941589647360, 0, 0, 177591814193152, 0, 51941572870144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 6496305927752757414146867200 }, some { target := 15, numerator := 6681914668545693340265349120 }, some { target := 16, numerator := 6496305927752757414146867200 }, some { target := 17, numerator := 5753870964581013709672939520 }, some { target := 18, numerator := 269318282890550028797917265920 }, some { target := 19, numerator := 73315452613209690816800358400 }, some { target := 20, numerator := 6681914668545693340265349120 }, some { target := 21, numerator := 269318282890550028797917265920 }, some { target := 22, numerator := 6496305927752757414146867200 }, some { target := 23, numerator := 6496305927752757414146867200 }, some { target := 24, numerator := 5568262223788077783554457600 }, some { target := 25, numerator := 6496305927752757414146867200 }, some { target := 26, numerator := 73315452613209690816800358400 }, some { target := 27, numerator := 5568262223788077783554457600 }, some { target := 28, numerator := 6496305927752757414146867200 }, some { target := 29, numerator := 5753870964581013709672939520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 22211310109989625123611607040 }, some { target := 137, numerator := 22845918970275042984286224384 }, some { target := 138, numerator := 22211310109989625123611607040 }, some { target := 139, numerator := 19672874668847953680913137664 }, some { target := 140, numerator := 920817456274141315838869766144 }, some { target := 141, numerator := 250670499812740054966473850880 }, some { target := 142, numerator := 22845918970275042984286224384 }, some { target := 143, numerator := 920817456274141315838869766144 }, some { target := 144, numerator := 22211310109989625123611607040 }, some { target := 145, numerator := 22211310109989625123611607040 }, some { target := 146, numerator := 19038265808562535820238520320 }, some { target := 147, numerator := 22211310109989625123611607040 }, some { target := 148, numerator := 250670499812740054966473850880 }, some { target := 149, numerator := 19038265808562535820238520320 }, some { target := 150, numerator := 22211310109989625123611607040 }, some { target := 151, numerator := 19672874668847953680913137664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 6496303829435619029685370880 }, some { target := 268, numerator := 6681912510276636716247810048 }, some { target := 269, numerator := 6496303829435619029685370880 }, some { target := 270, numerator := 5753869106071548283435614208 }, some { target := 271, numerator := 269318195900316663202099232768 }, some { target := 272, numerator := 73315428932201986192163471360 }, some { target := 273, numerator := 6681912510276636716247810048 }, some { target := 274, numerator := 269318195900316663202099232768 }, some { target := 275, numerator := 6496303829435619029685370880 }, some { target := 276, numerator := 6496303829435619029685370880 }, some { target := 277, numerator := 5568260425230530596873175040 }, some { target := 278, numerator := 6496303829435619029685370880 }, some { target := 279, numerator := 73315428932201986192163471360 }, some { target := 280, numerator := 5568260425230530596873175040 }, some { target := 281, numerator := 6496303829435619029685370880 }, some { target := 282, numerator := 5753869106071548283435614208 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 0, #[140769314734080, 0, 140705661976576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2
